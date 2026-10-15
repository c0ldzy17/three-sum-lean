#!/usr/bin/env python3
"""Audit every submitted declaration using the pinned Lean axiom collector.

Run after a successful complete source build. This is a local axiom-policy
audit, not the hosted Comparator or independent Nanoda check.
"""

from __future__ import annotations

from datetime import datetime, timezone
import argparse
import hashlib
import json
from pathlib import Path
import re
import subprocess
import sys


MODULE = re.compile(r"Submission(?:\.[A-Za-z_][A-Za-z_0-9]*)*")


def digest(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--provisional", action="store_true",
                        help="mark this unfrozen snapshot audit as provisional")
    args = parser.parse_args()
    root = Path.cwd()
    stamp = datetime.now(timezone.utc).strftime("%Y%m%dT%H%M%S.%fZ")
    output = root / "verification" / "builds" / (stamp + "_axioms")
    output.mkdir(parents=True)
    record_path = output / "results.json"
    record: dict = {"started_utc": stamp, "status": "preflight", "provisional": args.provisional}
    try:
        if (root / "lean-toolchain").read_text().strip() != "leanprover/lean4:v4.33.1":
            raise ValueError("The axiom audit requires the pinned Lean 4.33.1 toolchain")
        files = sorted((root / "Submission").rglob("*.lean")) + [root / "Submission.lean"]
        modules = [".".join(p.relative_to(root).with_suffix("").parts) for p in files]
        if any(not MODULE.fullmatch(m) for m in modules):
            raise ValueError("Invalid submitted module path")
        chains = json.loads((root / "scripts" / "source-chains.json").read_text())
        planned = [m for c in chains for m in c]
        if len(planned) != len(set(planned)) or set(planned) != set(modules):
            raise ValueError("Source-chain plan does not cover every current Submission source exactly")
        initial = {str(p.relative_to(root)): digest(p) for p in files}
        record.update(source_sha256=initial, module_count=len(modules))
        version = subprocess.run(["lake", "env", "lean", "--version"],
                                 capture_output=True, text=True)
        version_text = version.stdout + version.stderr
        (output / "toolchain.log").write_text(version_text)
        record.update(toolchain_exit_code=version.returncode,
                      toolchain_output=version_text.strip())
        if version.returncode or not re.search(r"\bLean \(version 4\.33\.1[, )]", version_text):
            raise ValueError("Actual compiler is not the pinned Lean 4.33.1 release")
        audit = output / "FullSourceAxioms.lean"
        body = "\n".join("import " + m for m in modules) + "\nimport Lean\n\n"
        body += '''open Lean Elab Command

set_option maxHeartbeats 0

run_cmd do
  let env := (← getEnv).setExporting false
  let moduleNames := env.header.moduleNames
  let allowed : Array Name := #[`propext, `Classical.choice, `Quot.sound]
  let mut submitted : Array Name := #[]
  for (decl, info) in env.constants.toList do
    let some idx := env.getModuleIdxFor? decl | continue
    let origin := moduleNames[idx]!
    if (`Submission).isPrefixOf origin then
      match info with
      | .axiomInfo _ => throwError "Submitted axiom declaration: {decl}"
      | _ => pure ()
      submitted := submitted.push decl
  if submitted.isEmpty then
    throwError "No submitted declarations were audited"
  for decl in submitted do
    let axioms ← collectAxioms decl
    let forbidden := axioms.filter fun ax => !allowed.contains ax
    unless forbidden.isEmpty do
      throwError "Forbidden transitive axioms in {decl}: {forbidden}"
  let some bound := env.find? `Race.bound | throwError "Missing Race.bound"
  let boundAxioms ← collectAxioms `Race.bound
  logInfo m!"RACE_BOUND_TYPE {bound.type}"
  logInfo m!"RACE_BOUND_AXIOMS {boundAxioms}"
  logInfo m!"FULL_SOURCE_AXIOM_AUDIT PASS {submitted.size} declarations"
'''
        audit.write_text(body)
        command = ["lake", "env", "lean", "-j1", "-DautoImplicit=false", str(audit)]
        record.update(status="auditing", command=command,
                      audit_source_sha256=digest(audit))
        record_path.write_text(json.dumps(record, indent=2) + "\n")
        log = output / "audit.log"
        with log.open("wb") as target:
            result = subprocess.run(command, stdout=target, stderr=subprocess.STDOUT)
        current_files = sorted((root / "Submission").rglob("*.lean")) + [root / "Submission.lean"]
        final = {str(p.relative_to(root)): digest(p) for p in current_files}
        record.update(exit_code=result.returncode, log_sha256=digest(log))
        if final != initial:
            raise ValueError("Submitted sources changed during the axiom audit")
        if result.returncode:
            raise ValueError("Lean rejected the full-source axiom audit; see audit.log")
        text = log.read_text()
        if "FULL_SOURCE_AXIOM_AUDIT PASS " not in text:
            raise ValueError("Missing successful full-source axiom-audit marker")
        record.update(status="succeeded")
        print(text, end="")
        return 0
    except (OSError, ValueError, json.JSONDecodeError) as error:
        record.update(status="failed", error=str(error))
        print("ERROR: " + str(error), file=sys.stderr)
        return 1
    finally:
        record["finished_utc"] = datetime.now(timezone.utc).isoformat()
        record_path.write_text(json.dumps(record, indent=2) + "\n")
        print("Axiom audit record: " + str(record_path))


if __name__ == "__main__":
    raise SystemExit(main())
