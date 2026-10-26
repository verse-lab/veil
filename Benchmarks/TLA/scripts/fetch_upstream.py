#!/usr/bin/env python3
"""Download the TLA+ models that configurations in Benchmarks/TLA check but the repository does not include.

German.tla, MultiPaxosUs.tla and FarmerGooseFox.tla come from repositories without a license, so
the repository only records where they are. Each file is downloaded at a pinned commit from GitHub
or GitLab, or from Software Heritage if that fails, and is written only if its SHA-256 is the
expected one. A file that is already there with the expected content is left alone; one with other
content is reported, and never overwritten. Git ignores the downloaded files.

  python3 Benchmarks/TLA/scripts/fetch_upstream.py              # next to the configurations
  python3 Benchmarks/TLA/scripts/fetch_upstream.py --dest DIR   # elsewhere

Python standard library only.
"""
import argparse
import hashlib
import http.client
import pathlib
import sys
import urllib.request

BENCHMARKS = pathlib.Path(__file__).resolve().parents[1]

# (file, URL at a pinned commit, SHA-256, Git blob hash, by which Software Heritage serves it)
FILES = [
    ("German.tla",
     "https://raw.githubusercontent.com/egolf-cs/scythe-fmcad2024/acb63604327eaca12e0fae80195124411047f56f/run_tool/sketches/German.tla",
     "360ca93d0ca932e907a8c5d5b79d3512103655dfde0ff8ca87f1e70ea8f72347",
     "12cf107daf11878e9d0898b340463bfe07b29c97"),
    ("MultiPaxosUs.tla",
     "https://raw.githubusercontent.com/sachand/HistVar/692e1e5b9c5e89f649af44613b62e557f6b569af/Multi-Paxos/MultiPaxosUs.tla",
     "17f3320cb9bac32a89894082792d7c7bee0793e0f9ed824f9fa3e1930d48808f",
     "a2fd28407355edc7b3cbdcb59f891ad86f462219"),
    # MultiPaxosUs.tla extends TLAPS, which tla2tools.jar does not include (BSD-2-Clause, like
    # Paxos/LICENSE, from the same commit)
    ("TLAPS.tla",
     "https://raw.githubusercontent.com/tlaplus/tlapm/5f5037fdd061be5df4a1bd1291cb22d3f43b8f31/library/TLAPS.tla",
     "9afe54984062748a0568966434cc0945d682f8cd89fdbc38f73b5579751b0c55",
     "d99c4bb1be3d09f9cd17504e0af2fa53dea16d07"),
    ("FarmerGooseFox.tla",
     "https://gitlab.com/hhan31/rivercrossing-tla/-/raw/6afafa30b6a03e96023c407f93ee75a17c67f5f5/FarmerGooseFox.tla",
     "39d2abfa5bd04cd4a06faa6add2a5c9e5cbcbb4ffabc8cdb2ec337dc8921206c",
     "d016e439a99532f6181e9e48a25837ae52fefabb"),
]
SOFTWARE_HERITAGE = "https://archive.softwareheritage.org/api/1/content/sha1_git:{}/raw/"


def sha256(data: bytes) -> str:
    return hashlib.sha256(data).hexdigest()


def download(urls, expected: str):
    """The content that the first of `urls` able to serve it with SHA-256 `expected` serves, and
    that URL."""
    errors = []
    for url in urls:
        try:
            with urllib.request.urlopen(url, timeout=60) as response:
                data = response.read()
        except (OSError, http.client.HTTPException) as e:
            errors.append(f"{url}: {e}")
            continue
        if sha256(data) == expected:
            return data, url
        errors.append(f"{url}: unexpected SHA-256 {sha256(data)}")
    raise RuntimeError("; ".join(errors))


def main():
    parser = argparse.ArgumentParser(description=__doc__.splitlines()[0])
    parser.add_argument("--dest", type=pathlib.Path, default=BENCHMARKS,
                        help="directory to write the files to (default: Benchmarks/TLA, next to the configurations)")
    args = parser.parse_args()
    args.dest.mkdir(parents=True, exist_ok=True)
    failed = False
    for name, url, expected, blob in FILES:
        path = args.dest / name
        if path.exists():
            if sha256(path.read_bytes()) == expected:
                print(f"{path}: already there")
            else:
                print(f"{path}: has other content than the pinned version; not overwritten", file=sys.stderr)
                failed = True
            continue
        try:
            data, source = download([url, SOFTWARE_HERITAGE.format(blob)], expected)
        except RuntimeError as e:
            print(f"{name}: download failed: {e}", file=sys.stderr)
            failed = True
            continue
        # Write it whole or not at all
        tmp = path.with_name(f".{name}.tmp")
        tmp.write_bytes(data)
        tmp.replace(path)
        print(f"{path}: downloaded from {source}")
    sys.exit(1 if failed else 0)


if __name__ == "__main__":
    main()
