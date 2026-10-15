#!/usr/bin/env python3
"""Build the complete verifier sources with serial or aggregate ordinary Lake.

Run from the repository root.  Logs record only this invocation; a restart does
not claim that skipped chains were checked here.  This is a development build,
not a substitute for the verifier's Comparator, axiom policy, or Nanoda gates.
"""

from __future__ import annotations

import argparse
from datetime import datetime, timezone
import hashlib
import json
import os
from pathlib import Path
import re
import shutil
import signal
import subprocess
import sys
import time


PINS = {
    "lean-toolchain": "3aac669c7a910ec2389f4e4f921b605adf6ebf2d1e0c9b9cd0be4d33f3f5db71",
    "lakefile.toml": "5ad072c0aca3c7ab777a99938f583ef92bc121101917b7818b5f53f1a384b08c",
    "lake-manifest.json": "484af05025301c3920dfeb644f6dbb7f02b05f596bf48831c9324e383694db25",
    "scripts/source-chains.json": "ee97a6c83f9dddcd5e63af28cfdf4f808b0db34db39d57fd374d492620841837",
}


def digest(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def save(path: Path, record: dict) -> None:
    temporary = path.with_suffix(".tmp")
    temporary.write_text(json.dumps(record, indent=2) + "\n")
    temporary.replace(path)


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--start-at", type=int, default=0,
                        help="first chain to build, using its zero-based index")
    parser.add_argument("--aggregate", action="store_true",
                        help="build every explicit planned module in one Lake invocation")
    parser.add_argument("--provisional", action="store_true",
                        help="mark this unfrozen snapshot check as provisional")
    args = parser.parse_args()
    root = Path.cwd()
    stamp = datetime.now(timezone.utc).strftime("%Y%m%dT%H%M%S.%fZ")
    logs = root / "verification" / "builds" / stamp
    logs.mkdir(parents=True)
    record_path = logs / "results.json"
    record = {"started_utc": stamp, "status": "preflight", "start_at": args.start_at,
              "lean_num_threads": 4, "required_sha256": PINS, "chains": [],
              "all_chains_built_in_this_invocation": False,
              "all_modules_built_in_this_invocation": False,
              "provisional": args.provisional,
              "validation_method": "aggregate_explicit_modules" if args.aggregate else "serial_chain_endpoints"}
    save(record_path, record)
    try:
        for name, expected in PINS.items():
            path = root / name
            if not path.is_file() or digest(path) != expected:
                raise ValueError(f"Missing or changed pinned file: {name}")
        if (root / "lakefile.lean").exists():
            raise ValueError("Unexpected lakefile.lean alongside the pinned lakefile.toml")
        if shutil.which("lake") is None:
            raise ValueError("lake is not on PATH; install the pinned Lean toolchain first")
        chains = json.loads((root / "scripts/source-chains.json").read_text())
        if not isinstance(chains, list) or not chains or any(
            not isinstance(c, list) or not c or any(
                not isinstance(m, str) or not re.fullmatch(r"Submission(?:\.[A-Za-z_][A-Za-z_0-9]*)*", m)
                for m in c) for c in chains
        ):
            raise ValueError("Invalid source-chain format")
        modules = [module for chain in chains for module in chain]
        source_paths = {m.replace(".", "/") + ".lean" for m in modules}
        actual_paths = {str(p.relative_to(root)).replace(os.sep, "/")
                        for p in (root / "Submission").rglob("*.lean")} | {"Submission.lean"}
        if len(modules) != len(set(modules)) or source_paths != actual_paths:
            raise ValueError("Source chains do not cover the current Submission sources exactly")
        if any(not (root / name).is_file() for name in source_paths):
            raise ValueError("A source file named in the chains is missing")
        if not 0 <= args.start_at < len(chains):
            raise ValueError(f"--start-at must be between 0 and {len(chains) - 1}")
        if args.aggregate and args.start_at != 0:
            raise ValueError("--aggregate requires --start-at 0 for complete source coverage")
        environment = dict(os.environ, LEAN_NUM_THREADS="4")
        version = subprocess.run(["lake", "env", "lean", "--version"], cwd=root,
                                 env=environment, capture_output=True, text=True)
        version_text = version.stdout + version.stderr
        (logs / "toolchain.log").write_text(version_text)
        record["toolchain_exit_code"] = version.returncode
        record["toolchain_output"] = version_text.strip()
        if version.returncode or not re.search(r"\bLean \(version 4\.33\.1[, )]", version_text):
            raise ValueError("Expected release Lean 4.33.1; see toolchain.log")
        record["observed_sha256"] = {name: digest(root / name) for name in PINS}
        if record["observed_sha256"] != PINS:
            raise ValueError("A pinned input changed while Lake checked its environment")
        record["source_sha256"] = {name: digest(root / name) for name in sorted(source_paths)}
        record.update(status="building", chain_count=len(chains), module_count=len(modules))
        save(record_path, record)

        if args.aggregate:
            invocations = [(None, "all_explicit_modules", ["lake", "build", *["+" + m for m in modules]])]
        else:
            invocations = [(i, chains[i][-1], ["lake", "build", chains[i][-1]])
                           for i in range(args.start_at, len(chains))]
        for index, target, command in invocations:
            log = logs / ("aggregate.log" if args.aggregate else f"{index:03d}_{target}.log")
            item = {"index": index, "target": target, "command": command,
                    "status": "running", "log": log.name}
            record["chains"].append(item)
            save(record_path, record)
            if args.aggregate:
                print(f"[aggregate] lake build {len(modules)} explicit planned modules", flush=True)
            else:
                print(f"[{index}/{len(chains)-1}] lake build {target}", flush=True)
            started = time.monotonic()
            with log.open("wb") as output:
                process = subprocess.Popen(item["command"], cwd=root, env=environment,
                                           stdout=output, stderr=subprocess.STDOUT,
                                           start_new_session=(os.name == "posix"))
                try:
                    code = process.wait()
                except KeyboardInterrupt:
                    if os.name == "posix":
                        os.killpg(process.pid, signal.SIGTERM)
                    else:
                        process.terminate()
                    try:
                        process.wait(timeout=5)
                    except subprocess.TimeoutExpired:
                        if os.name == "posix":
                            os.killpg(process.pid, signal.SIGKILL)
                        else:
                            process.kill()
                        process.wait()
                    code = 130
            item.update(status="succeeded" if code == 0 else "failed", exit_code=code,
                        seconds=round(time.monotonic() - started, 3), log_sha256=digest(log))
            record["exit_code"] = code
            save(record_path, record)
            print(f"  exit={code}; {item['seconds']} s; {log}", flush=True)
            if code:
                record["status"] = "interrupted" if code == 130 else "failed"
                return code if code > 0 else 1
        final_paths = {str(p.relative_to(root)).replace(os.sep, "/")
                       for p in (root / "Submission").rglob("*.lean")} | {"Submission.lean"}
        if final_paths != source_paths:
            raise ValueError("Submission source roster changed during the build")
        final_sources = {name: digest(root / name) for name in sorted(source_paths)}
        if final_sources != record["source_sha256"]:
            raise ValueError("Submission source bytes changed during the build")
        if {name: digest(root / name) for name in PINS} != PINS:
            raise ValueError("A pinned input changed during the build")
        record["source_inputs_unchanged_at_finish"] = True
        record["status"] = "succeeded"
        record["all_chains_built_in_this_invocation"] = args.start_at == 0
        record["all_modules_built_in_this_invocation"] = args.start_at == 0
        return 0
    except (ValueError, OSError, json.JSONDecodeError) as error:
        record.update(status="failed", error=str(error), exit_code=2)
        if record["chains"] and record["chains"][-1]["status"] == "running":
            record["chains"][-1].update(status="failed", error=str(error))
        print(f"ERROR: {error}", file=sys.stderr)
        return 2
    finally:
        record["finished_utc"] = datetime.now(timezone.utc).isoformat()
        save(record_path, record)
        print(f"Build record: {record_path}", flush=True)


if __name__ == "__main__":
    raise SystemExit(main())
