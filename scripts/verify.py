#!/usr/bin/env python3
# SCRIPT: DIRAC-TIME-LEAN-VERIFY-01
"""Audit the Dirac Time Lean library after `lake build`.

Why each check proves what it claims:

1. Axiom audit. `lake build` accepts a proof that uses `sorry` with only a
   warning, and a declared `axiom` would be accepted silently. `#print axioms`
   asks the kernel which axioms each theorem actually rests on. Requiring the
   answer to lie inside {propext, Classical.choice, Quot.sound} (the standard
   three every Mathlib theorem may use) rules out `sorry` (sorryAx), project
   axioms, and native_decide (Lean.ofReduceBool) for every named theorem.

2. Theorem inventory. The script discovers theorem names from the source files
   and fails if any expected module is missing or the count drops, so a theorem
   cannot silently disappear from the audit.

3. False controls. Each file in FalseControls/ states something deliberately
   false. It must FAIL to compile, and it must fail for a mathematical reason
   (unsolved goals, a failed tactic, a proposition proved false), not because of
   a typo or a missing name. This shows the checker can say no: a pipeline that
   accepts everything would pass the first two checks and fail this one.

4. Hashes. The SHA-256 of every source file is written to the report, so anyone
   can confirm the checked files are the files in the repository.
"""
from __future__ import annotations

import hashlib
import json
import pathlib
import re
import shutil
import subprocess
import sys

ROOT = pathlib.Path(__file__).resolve().parents[1]
OUT = ROOT / "verification"
ALLOWED = {"propext", "Classical.choice", "choice", "Quot.sound"}
CONFIG = json.loads((pathlib.Path(__file__).resolve().parent / "config.json").read_text())
MODULES = [(m["module"], m["path"]) for m in CONFIG["modules"]]
EXPECTED_THEOREMS = CONFIG["expected_theorems"]
EXPECTED_FALSE_CONTROLS = CONFIG["expected_false_controls"]
ROOT_IMPORTS = CONFIG["root_imports"]
# A declaration is `theorem` or `lemma` at the top level of its file; `private` ones cannot be
# named from another file and are audited through the public theorems that use them.
DECL_RE = re.compile(r"(?:theorem|lemma)\s+([^\s:({\[]+)")
MATH_FAILURE = re.compile(
    r"unsolved goals|proved that the proposition.*false|tactic '.*' failed|"
    r"linarith failed|failed to prove|decide failed|norm_num failed|type mismatch|"
    r"made no progress|failed to simplify",
    re.S | re.I)
INFRA_FAILURE = re.compile(
    r"unknown (?:module|identifier|constant|namespace)|unexpected token|"
    r"object file .* does not exist|invalid field", re.I)


LAST_OUTPUT = ""


# `lake env lean` is the CI path, where the pinned Mathlib has been built. In a bare
# checkout (no `.lake/build`) that command cannot resolve the library modules, so the
# plain toolchain is used instead; the checks themselves are identical.
USE_LAKE = (shutil.which("lake") is not None
            and (pathlib.Path(__file__).resolve().parents[1] / ".lake/build/lib/lean").is_dir())


OLEAN_DIR = OUT / "olean"
ENV = None


def prepare_oleans() -> None:
    """Without `lake`, build the library objects so the audit file can import them."""
    global ENV
    if USE_LAKE:
        return
    import os
    OLEAN_DIR.mkdir(parents=True, exist_ok=True)
    for module, rel in MODULES:
        out = OLEAN_DIR / rel.replace(".lean", ".olean")
        out.parent.mkdir(parents=True, exist_ok=True)
        env = dict(os.environ, LEAN_PATH=os.environ["LEAN_PATH"] + ":" + str(OLEAN_DIR))
        proc = subprocess.run(["lean", "-o", str(out), rel], cwd=ROOT,
                              capture_output=True, text=True, env=env)
        if proc.returncode != 0:
            print(proc.stdout + proc.stderr)
            raise SystemExit(f"could not build objects for {module}")
    ENV = dict(os.environ, LEAN_PATH=os.environ["LEAN_PATH"] + ":" + str(OLEAN_DIR))


def lean_cmd(args: list[str]) -> list[str]:
    """`lake env lean` in CI (where the pinned Mathlib is built); plain `lean` otherwise."""
    return ["lake", "env", "lean", *args] if USE_LAKE else ["lean", *args]


def run(argv: list[str]) -> subprocess.CompletedProcess:
    global LAST_OUTPUT
    proc = subprocess.run(argv, cwd=ROOT, capture_output=True, text=True, env=ENV)
    LAST_OUTPUT = " ".join(argv) + "\n" + proc.stdout + proc.stderr
    return proc


def strip_comments(text: str) -> str:
    text = re.sub(r"/-.*?-/", "", text, flags=re.S)
    return re.sub(r"--[^\n]*", "", text)


def theorems_in(path: pathlib.Path) -> list[str]:
    """Every non-private theorem/lemma in the file, fully qualified.

    The extension modules open many namespaces (one per card), so the namespace path is
    tracked line by line, with `section` acting as an anonymous frame.
    """
    out: list[str] = []
    stack: list[tuple[str, str]] = []
    depth = 0
    for line in path.read_text().splitlines():
        stripped = line.strip()
        at_top = depth == 0
        if at_top and stripped.startswith("namespace "):
            stack.append(("ns", stripped.split()[1]))
        elif at_top and re.match(r"(?:noncomputable\s+|private\s+|protected\s+)?section\b", stripped):
            stack.append(("sec", ""))
        elif at_top and (stripped == "end" or stripped.startswith("end ")):
            if stack:
                stack.pop()
        depth = max(0, depth + line.count("/-") - line.count("-/"))
        if at_top and depth == 0:
            mt = DECL_RE.match(line)
            if mt:
                path_ns = [n for kind, n in stack if kind == "ns"]
                out.append(".".join(path_ns + [mt.group(1)]))
    return list(dict.fromkeys(out))


def main() -> int:
    OUT.mkdir(exist_ok=True)
    report: dict = {"lean": run(["lean", "--version"]).stdout.strip(), "modules": {}}

    # Inventory and hashes.
    names: list[str] = []
    for module, rel in MODULES:
        path = ROOT / rel
        found = theorems_in(path)
        if not found:
            raise SystemExit(f"no theorems found in {module}")
        report["modules"][module] = {
            "file": rel,
            "sha256": hashlib.sha256(path.read_bytes()).hexdigest(),
            "theorems": len(found),
        }
        names += found
    total = sum(v["theorems"] for v in report["modules"].values())
    if total != EXPECTED_THEOREMS:
        raise SystemExit(f"inventory changed: {total} theorems, expected {EXPECTED_THEOREMS}")
    report["theorems"] = total

    prepare_oleans()

    # Axiom audit.
    audit = OUT / "AxiomAudit.lean"
    lines = [f"import {m}" for m in ROOT_IMPORTS] + [""]
    lines += [f"#print axioms {name}" for name in names]
    audit.write_text("\n".join(lines) + "\n")
    proc = run(lean_cmd([str(audit.relative_to(ROOT))]))
    log = proc.stdout + proc.stderr
    (OUT / "axioms.log").write_text(log)
    if proc.returncode != 0:
        print(log)
        raise SystemExit("axiom audit file did not compile")
    log = re.sub(r"\n (?=\S)", " ", log)   # Lean wraps long axiom lists
    axioms: dict[str, list[str]] = {}
    for name in names:
        dep = re.search(re.escape(f"'{name}' depends on axioms: [") + r"([^\]]*)\]", log, re.S)
        none = f"'{name}' does not depend on any axioms" in log
        if dep:
            used = sorted(a.strip() for a in dep.group(1).replace("\n", " ").split(",") if a.strip())
        elif none:
            used = []
        else:
            raise SystemExit(f"no axiom report for {name}")
        bad = set(used) - ALLOWED
        if bad:
            raise SystemExit(f"{name} uses disallowed axioms {sorted(bad)}")
        axioms[name] = used
    report["axioms"] = axioms
    report["axiom_union"] = sorted({a for used in axioms.values() for a in used})

    # False controls.
    controls = {}
    for path in sorted((ROOT / "FalseControls").glob("*.lean")):
        proc = run(lean_cmd([str(path.relative_to(ROOT))]))
        text = proc.stdout + proc.stderr
        (OUT / f"{path.stem}.log").write_text(text)
        if proc.returncode == 0:
            print(text)
            raise SystemExit(f"false control ACCEPTED: {path.name}")
        if INFRA_FAILURE.search(text) or not MATH_FAILURE.search(text):
            print(text)
            raise SystemExit(f"false control failed for the wrong reason: {path.name}")
        controls[path.stem] = "rejected"
    if len(controls) < EXPECTED_FALSE_CONTROLS:
        raise SystemExit(f"expected {EXPECTED_FALSE_CONTROLS} false controls, found {len(controls)}")
    report["false_controls"] = controls

    (OUT / "report.json").write_text(json.dumps(report, indent=2, sort_keys=True) + "\n")
    print(f"OK: {total} theorems, "
          f"axioms used: {report['axiom_union']}, {len(controls)} false controls rejected")
    return 0


def annotate(message: str) -> None:
    """Surface a failure as a GitHub error annotation (readable without the log)."""
    flat = message.replace("%", "%25").replace("\r", "").replace("\n", "%0A")
    print(f"::error title=verify.py::{flat[:6000]}")


if __name__ == "__main__":
    try:
        sys.exit(main())
    except SystemExit as exc:
        if exc.code not in (0, None):
            annotate(str(exc.code) + "%0A" + LAST_OUTPUT[-5000:])
        raise
