#!/usr/bin/env bash
set -euo pipefail
cd "$(dirname "$0")/.."
for command in bwrap lake lean python3; do
  command -v "$command" >/dev/null || { echo "Missing command: $command" >&2; exit 1; }
done
prefix=$(lean --print-prefix)
for tool in lake leanexport leanchecker nanoda_bin con-ron; do
  test -x "$prefix/bin/$tool" || { echo "Toolchain does not bundle $tool" >&2; exit 1; }
done
config=$(mktemp)
trap 'rm -f "$config"' EXIT
python3 - comparator.json "$config" "$prefix" <<'PY'
import json
from pathlib import Path
import sys
source, destination, prefix = sys.argv[1:]
config = json.loads(Path(source).read_text())
if 'external_kernels' in config:
    raise SystemExit('external_kernels must not appear in the submitted config')
config.pop('enable_nanoda', None)
config['external_kernels'] = {
    'nanoda': [f'{prefix}/bin/nanoda_bin'],
    'con-ron': [f'{prefix}/bin/con-ron'],
}
Path(destination).write_text(json.dumps(config, indent=2) + '\n')
PY
lake comparator --config "$config"
