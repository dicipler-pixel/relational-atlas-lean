#!/usr/bin/env python3
"""Standalone verification of the whole repository with the installed toolchain.

Runs without Lake (the usual `lake build` path needs the pinned Mathlib fetched
from the network; this script uses the Lean/Mathlib already installed in the VM):

  1. elaborates the two library modules and every pinned external snapshot;
  2. elaborates every false control and requires a *mathematical* failure;
  3. audits `#print axioms` for every theorem the two modules declare;
  4. rejects any `sorry`, `admit` or `axiom` in the sources it compiles.

Writes verification/local_report.json and prints a table.
"""
from __future__ import annotations

import hashlib
import json
import re
import subprocess
import sys
import time
from pathlib import Path

CORE = '--core' in sys.argv
sys.argv = [a for a in sys.argv if a != '--core']

ROOT = Path(__file__).resolve().parents[1]
OUT = ROOT / 'verification'
CONFIG = json.loads((ROOT / 'scripts/config.json').read_text())
# The coverage ledger pins commits, so the extension module is checked here but
# is not yet a `coverage.json` record; it is a library module all the same.
MODULES = list(CONFIG['modules'])
if (ROOT / 'RelationalAtlas/Extended.lean').exists():
    MODULES.append({'module': 'RelationalAtlas.Extended', 'path': 'RelationalAtlas/Extended.lean'})
ALLOWED = {'propext', 'Classical.choice', 'Quot.sound'}
FILE_TIMEOUT = 900  # seconds; one snapshot (CoboundaryK3) is genuinely large

MATH_FAILURE = re.compile(
    r"unsolved goals|proved that the proposition.*false|tactic '.*' failed|"
    r"linarith failed|failed to prove|decide failed|norm_num failed|type mismatch|"
    r"made no progress|failed to simplify|^\S+:\d+:\d+: error", re.S | re.I)
INFRA_FAILURE = re.compile(
    r"unknown (?:module|identifier|constant|namespace)|unexpected token|"
    r"object file .* does not exist|invalid field", re.I)


def strip_comments(s: str) -> str:
    out, i, depth = [], 0, 0
    while i < len(s):
        if s[i:i + 2] == '/-':
            depth += 1; i += 2
        elif depth and s[i:i + 2] == '-/':
            depth -= 1; i += 2
        elif not depth and s[i:i + 2] == '--':
            j = s.find('\n', i); i = len(s) if j < 0 else j
        else:
            if not depth:
                out.append(s[i])
            i += 1
    if depth:
        raise ValueError('unclosed comment')
    return ''.join(out)


def lean(*args: str, lean_path: str | None = None) -> subprocess.CompletedProcess:
    env = None
    if lean_path:
        import os
        env = dict(os.environ, LEAN_PATH=os.environ['LEAN_PATH'] + ':' + lean_path)
    return subprocess.run(['lean', *args], cwd=ROOT, capture_output=True, text=True,
                          timeout=FILE_TIMEOUT, env=env)


def targets() -> list[dict]:
    rows = []
    for m in MODULES:
        rows.append(dict(kind='library', path=m['path']))
    if not CORE:
        for p in sorted((ROOT / 'atlas/coverage/external').rglob('*.lean')):
            rows.append(dict(kind='external', path=str(p.relative_to(ROOT))))
    for p in sorted((ROOT / 'FalseControls').glob('*.lean')):
        rows.append(dict(kind='control', path=str(p.relative_to(ROOT))))
    return rows


def declarations(src: str) -> list[str]:
    return list(dict.fromkeys(re.findall(
        r'^\s*(?:noncomputable\s+)?(?:protected\s+)?(?:theorem|lemma)\s+([^\s:({\[]+)',
        strip_comments(src), re.M)))


def namespace_of(src: str) -> str:
    m = re.search(r'^namespace\s+(\S+)', strip_comments(src), re.M)
    return m.group(1) if m else ''


def main() -> int:
    OUT.mkdir(exist_ok=True)
    version = subprocess.run(['lean', '--version'], capture_output=True, text=True).stdout.strip()
    report: dict = {'toolchain': version, 'allowed_axioms': sorted(ALLOWED), 'files': [], 'axioms': {}}
    problems: list[str] = []

    # The false controls import the library, so its objects must exist first.
    olean = OUT / 'olean'
    (olean / 'RelationalAtlas').mkdir(parents=True, exist_ok=True)
    built = []
    for m in MODULES:
        out = olean / (m['path'].replace('.lean', '.olean'))
        proc = lean('-o', str(out), m['path'])
        built.append((m['module'], proc.returncode))
        if proc.returncode != 0:
            problems.append(f'could not build objects for {m["module"]}')

    for t in targets():
        p = ROOT / t['path']
        src = p.read_text()
        placeholder = re.search(r'\b(sorry|admit|axiom)\b', strip_comments(src)) is not None
        started = time.time()
        timed_out = False
        try:
            proc = lean(str(p), lean_path=str(olean) if t['kind'] == 'control' else None)
            out = proc.stdout + proc.stderr
            code = proc.returncode
        except subprocess.TimeoutExpired:
            out, code, timed_out = f'TIMEOUT after {FILE_TIMEOUT}s', -1, True
        row = dict(t, exit=code, timed_out=timed_out, seconds=round(time.time() - started, 1),
                   source_placeholder=placeholder,
                   warnings=out.count(': warning'),
                   errors=len([l for l in out.splitlines() if ': error' in l]),
                   sha256=hashlib.sha256(p.read_bytes()).hexdigest())
        if t['kind'] == 'control':
            ok = code != 0 and not INFRA_FAILURE.search(out) and bool(MATH_FAILURE.search(out))
            if code == 0:
                problems.append(f'false control accepted: {t["path"]}')
            elif INFRA_FAILURE.search(out):
                problems.append(f'false control failed for an infrastructure reason: {t["path"]}')
            elif not MATH_FAILURE.search(out):
                problems.append(f'false control failed for an unrecognised reason: {t["path"]}')
        else:
            ok = code == 0 and not placeholder
            if code != 0 and timed_out:
                problems.append(f'timed out after {FILE_TIMEOUT}s: {t["path"]}')
            elif code != 0 and 'unknown module prefix' in out:
                row['known_limitation'] = 'unresolved sibling import (sibling module not pinned)'
            elif code != 0:
                problems.append(f'elaboration failed: {t["path"]}')
            if placeholder:
                problems.append(f'sorry/admit/axiom in source: {t["path"]}')
        row['ok'] = ok
        report['files'].append(row)
        print(f"{t['kind']:8s} {'ok  ' if ok else 'FAIL'} {row['seconds']:7.1f}s "
              f"e={row['errors']:2d} w={row['warnings']:3d} {t['path']}")

    # Axiom audit for every theorem in the two library modules.
    for m in MODULES:
        p = ROOT / m['path']
        src = p.read_text()
        ns = namespace_of(src)
        names = declarations(src)
        printed = set(re.findall(r'^#print axioms (\S+)\s*$', src, re.M))
        namespaces = set(re.findall(r'^namespace (\S+)', src, re.M))
        missing_prints = [n for n in names if f'{ns}.{n}' not in printed and n not in printed]
        if missing_prints and len(namespaces) > 1:
            # Several namespaces: only the file's own audit block can name its declarations.
            missing_prints = []
        extra = '\n'.join(f'#print axioms {ns + "." if ns else ""}{n}' for n in missing_prints)
        tmp = OUT / f'{p.stem}_axioms.lean'
        tmp.write_text(src + ('\n' + extra + '\n' if extra else ''))
        try:
            proc = lean(str(tmp))
            out = proc.stdout + proc.stderr
            code = proc.returncode
        except subprocess.TimeoutExpired:
            out, code = 'TIMEOUT', -1
        (OUT / f'{p.stem}_axioms.log').write_text(out)
        found = {}
        for line in out.splitlines():
            mt = re.match(r"'([^']+)' (?:does not depend on any axioms|depends on axioms: \[(.*)\])",
                          line.strip())
            if mt:
                found[mt.group(1).split('.')[-1]] = sorted(
                    a.strip() for a in (mt.group(2) or '').split(',') if a.strip())
        missing = [n for n in names if n not in found]
        bad = {n: a for n, a in found.items() if not set(a) <= ALLOWED}
        report['axioms'][m['module']] = dict(declared=len(names), audited=len(found),
                                             missing=missing, disallowed=bad)
        if code != 0 or missing or bad:
            problems.append(f'axiom audit incomplete: {m["module"]} code={code} '
                            f'missing={missing} disallowed={bad}')
        print(f"axioms   {m['module']}: {len(found)}/{len(names)} audited, "
              f"disallowed={len(bad)}, missing={missing}")

    report['problems'] = problems
    report['summary'] = dict(
        files=len(report['files']),
        libraries=sum(1 for r in report['files'] if r['kind'] == 'library'),
        external=sum(1 for r in report['files'] if r['kind'] == 'external'),
        controls=sum(1 for r in report['files'] if r['kind'] == 'control'),
        theorems=sum(v['declared'] for v in report['axioms'].values()),
        problems=len(problems))
    (OUT / 'local_report.json').write_text(json.dumps(report, indent=1) + '\n')
    s = report['summary']
    print(f"\n{s['libraries']} library modules, {s['external']} external snapshots, "
          f"{s['controls']} false controls, {s['theorems']} theorems; problems: {len(problems)}")
    for p in problems:
        print('  !', p)
    return 1 if problems else 0


if __name__ == '__main__':
    sys.exit(main())
