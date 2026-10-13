#!/usr/bin/env bash
set -euo pipefail
cd "$(dirname "$0")/.."

# Verify the committed dependency lock against the actual dependency checkouts.
python3 - <<'PY'
from pathlib import Path
import json
import subprocess
import tomllib

config = tomllib.loads(Path('lakefile.toml').read_text())
manifest = json.loads(Path('lake-manifest.json').read_text())
packages = {p['name'].strip('«»'): p for p in manifest['packages']}
for requirement in config['require']:
    name = requirement['name']
    package = packages[name]
    for config_key, manifest_key in [('git', 'url'), ('rev', 'rev'), ('subDir', 'subDir')]:
        if requirement.get(config_key) != package.get(manifest_key):
            raise SystemExit(f'Dependency configuration disagrees with lock: {name}/{config_key}')
    checkout = Path(manifest['packagesDir']) / name
    def git(*args):
        return subprocess.check_output(['git', '-C', str(checkout), *args], text=True).strip()
    if git('rev-parse', 'HEAD') != package['rev']:
        raise SystemExit(f'Dependency checkout is at the wrong revision: {name}')
    if git('status', '--porcelain'):
        raise SystemExit(f'Dependency checkout has local changes: {name}')
    print(f'Checked dependency: {name} at {package["rev"]}', flush=True)
PY

lake build
lake env lean Audit.lean
lake env leanchecker --verbose EulerPolyhedron EulersGem
