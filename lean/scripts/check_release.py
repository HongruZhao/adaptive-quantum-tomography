"""Check tracked release-file hashes without building Lean or running simulations."""
from pathlib import Path
import hashlib
import json
import sys

ROOT = Path(__file__).resolve().parents[1]

def main():
    manifest = json.loads((ROOT / "MANIFEST.json").read_text())
    errors = []
    for name, expected in manifest["sha256"].items():
        path = ROOT / name
        try:
            path.resolve().relative_to(ROOT.resolve())
        except ValueError:
            errors.append({"file": name, "reason": "path outside release"})
            continue
        if not path.is_file():
            errors.append({"file": name, "reason": "missing"})
        elif hashlib.sha256(path.read_bytes()).hexdigest() != expected:
            errors.append({"file": name, "reason": "hash differs"})
    print(json.dumps({"status": "FAIL" if errors else "PASS",
                      "tracked_files_checked": len(manifest["sha256"]),
                      "integrity_only": True,
                      "Lean_compilation_or_simulation_performed": False,
                      "errors": errors}, indent=2))
    return bool(errors)

if __name__ == "__main__":
    sys.exit(main())
