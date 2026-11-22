"""Packs a built manyan into a wheel for one platform, as ruff ships its own:
the executable is installed onto the PATH as it is, with no Python between,
so `pip install manyan` gives the same program as a release, workers and all.

    python3 python/wheel.py PLATFORM_TAG OUT_DIR FILE...

FILE is the executable and anything it needs beside it (cygwin1.dll on
Windows), or the library manyan.check loads (libmanyan.so or .dylib),
which goes in the package. The version is manyan.h's.
"""
import base64
import hashlib
import re
import sys
import zipfile
from pathlib import Path

HERE = Path(__file__).resolve().parent
ROOT = HERE.parent


def main(tag, out, *files):
    version = re.search(r'#define MANYAN_VERSION "(.*)"', (ROOT / "manyan.h").read_text()).group(1)
    dist = f"manyan-{version}"
    metadata = f"""Metadata-Version: 2.4
Name: manyan
Version: {version}
Summary: A fast model checker for TLA+, compatible with TLC and Apalache.
Author: Ju Lin
License-Expression: MIT
License-File: LICENSE
Project-URL: Repository, https://github.com/soasme/manyan
Requires-Python: >=3.8
Description-Content-Type: text/markdown

""" + (HERE / "README.md").read_text()
    wheel = f"Wheel-Version: 1.0\nGenerator: manyan wheel.py\nRoot-Is-Purelib: false\nTag: py3-none-{tag}\n"

    entries = [(f"manyan/{p.name}", p.read_bytes(), 0o644) for p in sorted((HERE / "manyan").glob("*.py"))]
    entries += [(f"manyan/{Path(f).name}" if Path(f).name.startswith("libmanyan.") else f"{dist}.data/scripts/{Path(f).name}",
                 Path(f).read_bytes(), 0o755) for f in files]
    entries += [(f"{dist}.dist-info/METADATA", metadata.encode(), 0o644),
                (f"{dist}.dist-info/WHEEL", wheel.encode(), 0o644),
                (f"{dist}.dist-info/licenses/LICENSE", (ROOT / "LICENSE").read_bytes(), 0o644)]

    record = f"{dist}.dist-info/RECORD"
    lines = []
    path = Path(out) / f"manyan-{version}-py3-none-{tag}.whl"
    path.parent.mkdir(parents=True, exist_ok=True)
    with zipfile.ZipFile(path, "w", zipfile.ZIP_DEFLATED) as z:
        for name, data, mode in entries:
            info = zipfile.ZipInfo(name, (1980, 1, 1, 0, 0, 0))
            info.external_attr = (0o100000 | mode) << 16
            info.compress_type = zipfile.ZIP_DEFLATED
            z.writestr(info, data)
            digest = base64.urlsafe_b64encode(hashlib.sha256(data).digest()).rstrip(b"=").decode()
            lines.append(f"{name},sha256={digest},{len(data)}")
        lines.append(f"{record},,")
        z.writestr(zipfile.ZipInfo(record, (1980, 1, 1, 0, 0, 0)), "\n".join(lines) + "\n")
    print(path)


if __name__ == "__main__":
    main(*sys.argv[1:])
