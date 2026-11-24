#!/usr/bin/env python3
"""Generate atlas/coverage/CERTIFICATION.md: for every mapped card, what the Lean
kernel proves and what would still be needed before the card itself could be called
certified.

The ledger's `full_card_certified` flag is required by the validator to stay false:
a kernel proves a named finite statement, not the card's reading of it. This report
makes that gap explicit per card instead of leaving it as a boolean.
"""
from __future__ import annotations
import json
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
COV = ROOT / 'atlas/coverage/coverage.json'
OUT = ROOT / 'atlas/coverage/CERTIFICATION.md'

# What each source grade means for how far a finite proof can carry the card.
GRADE = {
    'theorem': 'A displayed statement the card presents as proved. A finite kernel can come close to complete.',
    'derived': 'A consequence the card draws from a cited result. The citation stays an input.',
    'measured': 'A number or exponent read off data or a simulation. No Lean statement can certify the measurement; only the algebra behind it is formalisable.',
    'conjecture': 'An open claim. Only the established sub-claims can be formalised.',
    'reading': 'An interpretation, not a mathematical assertion. Not certifiable in any form.',
}


def main() -> None:
    cov = json.loads(COV.read_text())
    LOCAL = 'dicipler-pixel/relational-atlas-lean'
    mapped = [c for c in cov['cards'] if c['proof_references']]
    local = [c for c in mapped if any(r['repository'] == LOCAL for r in c['proof_references'])]
    external = [c for c in mapped if c not in local]
    lines = ["# What each mapped kernel covers, and what it does not", "",
             f"Generated from `coverage.json` by `scripts/build_certification.py`. "
             f"{len(mapped)} of {len(cov['cards'])} cards carry a mapped kernel: "
             f"{len(local)} with a kernel in this repository, {len(external)} only in a companion "
             f"repository.", "",
             "Every card keeps `full_card_certified: false`, and the validator requires that: a kernel "
             "proves the finite statement it names under its written hypotheses, not the card's physical "
             "reading, measured exponent or genericity claim. The table states, per card, what is proved "
             "and what is not.", "",
             "How far a finite proof can carry a card depends on its source grade:", ""]
    lines += [f"- **{k}** — {v}" for k, v in GRADE.items()]
    lines += ["## Cards with a kernel in this repository", "",
              "| Card | Grade | Kernels | What is proved, and what is not |",
              "| :--- | :--- | :---: | :--- |"]
    for c in local:
        local = [r for r in c['proof_references'] if r['repository'].endswith('relational-atlas-lean')]
        kinds = sorted({r['path'].split('/')[-1].replace('.lean', '') for r in c['proof_references']})
        n = sum(len(r['declarations']) for r in c['proof_references'])
        scope = local[0]['scope'] if local else c['proof_references'][0]['scope']
        extra = []
        for k in c.get('corrections', []):
            extra.append(f"**{k['kind']}**: {k['finding']}")
        remains = scope + (' ' + ' '.join(extra) if extra else '')
        lines.append(f"| {c['id']} | {c['source_grade']} | {n} | {remains.strip()} |")
    lines += ["", "## Cards mapped only to a companion repository", "",
              "These kernels are pinned by commit and hash and their declarations exist in the "
              "snapshot, but they were not audited statement-by-statement in this repository, and "
              "four of the snapshots cannot even be re-elaborated here because they import a sibling "
              "module that was never pinned. Treat them as citations with a checked inventory.", "",
              "| Card | Grade | Companion kernels |", "| :--- | :--- | :--- |"]
    for c in external:
        refs = c['proof_references']
        where = sorted({r['repository'].split('/')[-1] for r in refs})
        n = sum(len(r['declarations']) for r in refs)
        lines.append(f"| {c['id']} | {c['source_grade']} | {n} in {', '.join(where)} |")
    OUT.write_text('\n'.join(lines) + '\n')
    print(f'{len(mapped)} mapped cards written to {OUT.relative_to(ROOT)}')


if __name__ == '__main__':
    main()
