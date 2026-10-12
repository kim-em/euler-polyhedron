#!/usr/bin/env bash
set -euo pipefail
cd "$(dirname "$0")/.."
lake build
python3 - <<'PY'
from pathlib import Path
import re
import hashlib
import subprocess

for line in Path('vendor/SOURCE_SHA256.txt').read_text().splitlines():
    expected_hash, name = line.split('  ', 1)
    actual_hash = hashlib.sha256((Path('vendor') / name).read_bytes()).hexdigest()
    if actual_hash != expected_hash:
        raise SystemExit(f'Vendored source changed: {name}')

sources = [Path('EulerPolyhedron.lean'), *Path('EulerPolyhedron').glob('*.lean'),
           *Path('vendor/EulersGem').glob('*.lean')]
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
