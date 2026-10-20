#!/usr/bin/env python3
"""Exercise submission preparation locally with synthetic, unranked artifacts.

Never calls a model, executes a program, or adds an entry to submissions/.
"""
import argparse
import hashlib
import json
from pathlib import Path
import shutil
import tempfile
import zipfile

import yaml

import manage


def create_example(destination=None):
    if destination is None:
        destination = Path(tempfile.mkdtemp(prefix="vericontest-submission-"))
    else:
        destination = Path(destination).resolve()
        manage.require(not destination.exists(), "example output directory already exists; choose a new directory")
        manage.require(not destination.is_relative_to(manage.ROOT / "submissions"), "keep synthetic examples outside submissions/")
        destination.mkdir(parents=True)
    args = argparse.Namespace(id="local-example-agent", track="agent", task="End2End", input_mode="nl", split="codeforces")
    entry = manage.initialize(manage.ROOT, args, output_dir=destination)
    m = manage.load_yaml(entry / "metadata.yaml")
    m["system"].update(name="Local example — not a real system", version="fixture-1",
                       team="Local walkthrough", authors=["Synthetic example"], contact="Local only; do not submit",
                       description="Synthetic files demonstrating intake; no model or benchmark execution occurred.",
                       source_availability="unavailable",
                       models=[{"id": "fixture/no-model", "role": "No model invoked", "settings": {}}])
    exp = m["experiment"]
    exp.update(input_description="Synthetic fixture only; a real End2End run receives description and interface.",
               attempt_definition="One final output record per problem; no independent repeats.",
               attempt_schedule="One record per Codeforces problem, including unattempted problems.",
               candidate_selection="No candidate search; one intentionally invalid placeholder output.",
               human_intervention="All files were created by the local walkthrough script. This is not an eligible system run.")
    exp["generation_access"] = {key: "None; no generation was performed." for key in exp["generation_access"]}
    exp["budget"].update(scope="per problem", max_internal_candidates=0, max_repair_iterations=0,
                         max_llm_calls=0, max_input_tokens=0, max_output_tokens=0, max_wall_time_seconds=None,
                         notes="No model calls or evaluation. Wall time not measured; zero values mean no such operations.")
    m["benchmark"]["testcases"]["modifications"] = "No official testcases accessed; no evaluation performed."
    m["artifacts"].update(availability="pending", missing_records_and_redactions="Synthetic logs only; no real execution traces exist.")
    m["rerun"].update(available=False, method=None, access_notes="No system exists to rerun; local format example only.")
    m["notes"] = "Synthetic preparation walkthrough. Never submit or publish this example."
    rows = [json.loads(line) for line in (entry / "results.jsonl").read_text().splitlines()]
    bundle = destination / "bundle"
    (bundle / "artifacts").mkdir(parents=True)
    (bundle / "logs").mkdir()
    for row, status in zip(rows, ("produced", "failed", "timeout")):
        row["generation_status"] = status
        stem = row["problem_id"].split("/")[1]
        log = f"logs/{stem}.txt"
        row["logs"] = {"generation": log}
        row["notes"] = f"Synthetic {status} case; no program evaluation occurred."
        (bundle / log).write_text(row["notes"] + "\n")
        if status == "produced":
            program = f"artifacts/{stem}.rs"
            row["artifacts"] = {"program": program}
            (bundle / program).write_text('compile_error!("Synthetic format example; not a benchmark solution");\n')
    (entry / "results.jsonl").write_text("".join(json.dumps(row) + "\n" for row in rows))
    (entry / "README.md").write_text("""# Local submission example — never publish

## System and generation

This is a synthetic Agent / End2End intake example, not a system evaluation.
No model, tool, test, or verifier ran. One placeholder output, one generation
failure, and one generation timeout illustrate result encoding. All remaining
problems are not_attempted and remain in the declared Codeforces denominator.

## Evaluation

No checks were run. All three applicable checks are not_run. A generation timeout
does not imply a verifier or test timeout. There is no reported or official score,
no approved evaluation protocol, and no completed human specification review.

## Artifacts and fresh runs

bundle.zip contains this README, results.jsonl, artifacts/, and logs/ at its root.
All listed artifact and log paths are relative to that root. The intentionally
invalid Rust file is a format example only; do not execute it for a real score.
The actual ZIP SHA-256 is recorded in metadata. Availability stays pending because
this local ZIP has not been hosted or shared with maintainers. A real submission
must arrange access and change availability accordingly. No fresh runs exist.
""")
    for filename in ("README.md", "results.jsonl"):
        shutil.copyfile(entry / filename, bundle / filename)
    archive = destination / "bundle.zip"
    with zipfile.ZipFile(archive, "w", compression=zipfile.ZIP_DEFLATED) as z:
        for path in sorted(bundle.rglob("*")):
            if path.is_file():
                z.write(path, path.relative_to(bundle).as_posix())
    m["artifacts"]["archive_sha256"] = hashlib.sha256(archive.read_bytes()).hexdigest()
    (entry / "metadata.yaml").write_text(yaml.safe_dump(m, sort_keys=False, allow_unicode=True))
    public = manage.validate_entry(entry, *manage.load_config(manage.ROOT))
    manage.require(public["score"] is None and not public["rankable"], "local example must stay unranked")
    # Unlike registry validation, this local walkthrough also checks the bundle
    # it just created, to demonstrate how per-result paths are resolved.
    with zipfile.ZipFile(archive) as z:
        names = set(z.namelist())
        for row in rows:
            for path in [*row["artifacts"].values(), *row["logs"].values()]:
                manage.require(path in names, f"missing bundle member: {path}")
    (destination / "preview.json").write_text(json.dumps(public, indent=2) + "\n")
    print(f"Validated synthetic example: {entry}")
    print(f"Pinned local artifact bundle: {archive}")
    print(f"Scope: {len(rows)} problems; 1 produced, 1 failed, 1 timeout, {len(rows)-3} not attempted.")
    print("Status: submitted; official score: null; rankable: false. Public registry unchanged.")
    return destination


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--output-dir", type=Path, help="new directory outside submissions/; default: a new temporary directory")
    args = parser.parse_args()
    try:
        create_example(args.output_dir)
    except (ValueError, OSError) as exc:
        parser.exit(1, f"ERROR: {exc}\n")


if __name__ == "__main__":
    main()
