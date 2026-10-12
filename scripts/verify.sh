#!/usr/bin/env bash
set -euo pipefail
cd "$(dirname "$0")/.."
lake build
python3 - <<'PY'
from pathlib import Path
import re
import subprocess

# Check the imported upstream proof modules as well as this project's sources.
upstream = Path('.lake/packages/eulers-gem/lean')
modules = set()
def collect(module):
    if module in modules:
        return
    modules.add(module)
    source = upstream / (module.replace('.', '/') + '.lean')
    for line in source.read_text().splitlines():
        if line.startswith('import '):
            for dependency in line.split()[1:]:
                if dependency.startswith('EulersGem.'):
                    collect(dependency)
collect('EulersGem.Embed')
collect('EulersGem.PolytopeFaces')
sources = [Path('EulerPolyhedron.lean'), *Path('EulerPolyhedron').glob('*.lean'),
           *(upstream / (module.replace('.', '/') + '.lean') for module in modules)]
for source in sources:
    if re.search(r'\b(sorry|admit|axiom)\b', source.read_text()):
        raise SystemExit(f'Unproved declaration or placeholder in {source}')

result = subprocess.run(['lake', 'env', 'lean', 'Audit.lean'],
                        text=True, stdout=subprocess.PIPE, stderr=subprocess.STDOUT)
print(result.stdout, end='')
if result.returncode:
    raise SystemExit(result.returncode)
expected = {'EulerPolyhedron.polyhedral_convexHull_finite',
            'EulersGem.IsPolytope.isPolyhedron',
            'EulerPolyhedron.faces_finite', 'EulerPolyhedron.euler_polyhedron'}
allowed = {'propext', 'Classical.choice', 'Quot.sound'}
seen = set()
for name, axioms in re.findall(r"'([^']+)' depends on axioms: \[([^\]]*)\]", result.stdout):
    seen.add(name)
    actual = {a.strip() for a in axioms.split(',') if a.strip()}
    if not actual <= allowed:
        raise SystemExit(f'Unexpected axioms for {name}: {actual - allowed}')
if seen != expected:
    raise SystemExit(f'Missing or unexpected axiom reports: {seen ^ expected}')
print('Verified: compiled proofs, geometric face finiteness, and standard axioms only.')
PY
