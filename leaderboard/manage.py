#!/usr/bin/env python3
"""Validate the submission registry and build static website data.

This tool never downloads artifacts, executes submitted code, or judges specs.
Review records are attestations approved by maintainers through PR review.
"""
from __future__ import annotations

import argparse
from collections import Counter
from datetime import date
import hashlib
import json
import math
from pathlib import Path, PurePosixPath
import re
import sys
from urllib.parse import urlsplit

import yaml

ROOT = Path(__file__).resolve().parent.parent
MODES = {"SpecGen": {"nl"}, "CodeGen": {"nl", "spec", "nl_spec"},
         "ProofGen": {"code_spec"}, "End2End": {"nl"}}
CHECKS = {"SpecGen": {"spec_tests"}, "CodeGen": {"code_tests"},
          "ProofGen": {"verus"}, "End2End": {"code_tests", "verus", "spec_tests"}}
CHECK_STATES = {"pass", "fail", "timeout", "unsupported", "error", "not_run", "not_applicable"}
ENTRY_FILES = ("metadata.yaml", "README.md", "problem_ids.txt", "results.jsonl")
SHA = re.compile(r"[0-9a-f]{40}|[0-9a-f]{64}")
ID = re.compile(r"[a-z0-9][a-z0-9_-]{0,119}")
LOGO = re.compile(r"static/logos/[a-z0-9][a-z0-9_-]*\.(svg|png|webp)")


class Invalid(ValueError):
    pass


def require(condition, message):
    if not condition:
        raise Invalid(message)


def mapping(value, name):
    require(isinstance(value, dict), f"{name} must be an object")
    return value


def text(value, name):
    require(isinstance(value, str) and bool(value.strip()), f"{name} must be nonempty text")
    require("REPLACE_ME" not in value, f"complete {name} (REPLACE_ME remains)")
    return value


def strings(value, name, nonempty=False):
    require(isinstance(value, list), f"{name} must be a list")
    for item in value:
        text(item, name)
    require(not nonempty or len(value) > 0, f"{name} must not be empty")
    require(len(value) == len(set(value)), f"{name} contains duplicates")
    return value


def url(value, name):
    text(value, name)
    parsed = urlsplit(value)
    require(parsed.scheme == "https" and bool(parsed.hostname) and not parsed.username
            and not parsed.password, f"{name} must be an HTTPS URL without credentials")
    return value


def iso_date(value, name):
    text(value, name)
    try:
        require(date.fromisoformat(value).isoformat() == value, f"invalid {name}")
    except ValueError as exc:
        raise Invalid(f"{name} must be YYYY-MM-DD") from exc


def pin(value, name, required=True):
    mapping(value, name)
    revision, digest = value.get("revision"), value.get("archive_sha256")
    if revision is not None:
        require(isinstance(revision, str) and SHA.fullmatch(revision), f"{name}.revision must be a full SHA")
    if digest is not None:
        require(isinstance(digest, str) and re.fullmatch(r"[0-9a-f]{64}", digest), f"invalid {name}.archive_sha256")
    require(not required or revision or digest, f"{name} needs an immutable revision or archive_sha256")


def relative(value, name):
    text(value, name)
    path = PurePosixPath(value)
    require(not path.is_absolute() and ".." not in path.parts and "\\" not in value
            and ":" not in value and path.parts, f"{name} must be a relative bundle path")


def unique_pairs(pairs):
    result = {}
    for key, value in pairs:
        require(key not in result, f"duplicate key: {key}")
        result[key] = value
    return result


class Loader(yaml.SafeLoader):
    pass


def yaml_mapping(loader, node):
    return unique_pairs((loader.construct_object(k), loader.construct_object(v)) for k, v in node.value)


Loader.add_constructor(yaml.resolver.BaseResolver.DEFAULT_MAPPING_TAG, yaml_mapping)


def load_json(path):
    return json.loads(path.read_text(), object_pairs_hook=unique_pairs,
                      parse_constant=lambda x: (_ for _ in ()).throw(Invalid(f"invalid JSON number: {x}")))


def load_yaml(path):
    return mapping(yaml.load(path.read_text(), Loader=Loader), str(path))


def problem_ids(path):
    ids = [line.strip() for line in path.read_text().splitlines() if line.strip()]
    strings(ids, str(path), nonempty=True)
    require(all(re.fullmatch(r"(?:leetcode/lc\d+|codeforces/cf\d+[A-Za-z]\d*)", p) for p in ids),
            f"invalid problem ID in {path}")
    return ids


def fingerprint(entry):
    digest = hashlib.sha256()
    for name in ENTRY_FILES:
        path = entry / name
        if name == "README.md" and not (path.exists() or path.is_symlink()):
            continue  # the methodology write-up is optional
        require(path.is_file() and not path.is_symlink(), f"missing or symlinked {path}")
        digest.update(name.encode() + b"\0" + hashlib.sha256(path.read_bytes()).digest())
    return digest.hexdigest()


def load_release(release, path):
    """Return the release and the problem IDs of each split it accepts."""
    mapping(release, "release")
    text(release.get("id"), "release.id")
    pin({"revision": release.get("benchmark_revision")}, "release benchmark")
    ids = problem_ids(path)
    require(hashlib.sha256(path.read_bytes()).hexdigest() == release.get("problem_ids_sha256"), "release problem-list checksum mismatch")
    counts = dict(Counter(p.split('/')[0] for p in ids))
    counts["full"] = len(ids)
    require(counts == release.get("counts"), "release counts do not match problem IDs")
    splits = {"full": ids, **{family: [p for p in ids if p.startswith(family + "/")] for family in ("leetcode", "codeforces")}}
    lite = release.get("lite")
    if lite is not None:
        mapping(lite, "release.lite")
        name = lite.get("problem_ids_path")
        require(isinstance(name, str) and re.fullmatch(r"lite_problem_ids[a-z0-9._-]*\.txt", name),
                "release.lite.problem_ids_path must name a lite_problem_ids*.txt file in leaderboard/")
        lite_path = path.parent / name
        lite_ids = problem_ids(lite_path)
        require(hashlib.sha256(lite_path.read_bytes()).hexdigest() == lite.get("problem_ids_sha256"), "Lite problem-list checksum mismatch")
        require(len(set(lite_ids)) == len(lite_ids) == lite.get("count") and set(lite_ids) <= set(ids),
                "Lite problems must be distinct problems of the release, matching release.lite.count")
        splits["lite"] = [p for p in ids if p in set(lite_ids)]
    return release, splits


def load_config(root):
    """Return the current release, every accepted release by ID, and the protocols.

    leaderboard/release.json is the current release. leaderboard/releases.json lists
    earlier releases that still accept submissions, each naming its problem list.
    """
    release, splits = load_release(load_json(root / "leaderboard/release.json"), root / "leaderboard/problem_ids.txt")
    # Detect accidental changes to the supported collection without a release update.
    actual = {f"{family}/{p.name}" for family in ("leetcode", "codeforces")
              for p in (root / "benchmark" / family).iterdir() if p.is_dir()}
    require(actual == set(splits["full"]), "current benchmark membership differs from supported release")
    releases = {release["id"]: (release, splits)}
    archive = root / "leaderboard/releases.json"
    earlier = load_json(archive) if archive.is_file() else []
    require(isinstance(earlier, list), "releases.json must be a list")
    for old in earlier:
        name = mapping(old, "release").get("problem_ids_path")
        require(isinstance(name, str) and re.fullmatch(r"problem_ids[a-z0-9._-]*\.txt", name),
                "release.problem_ids_path must name a problem_ids*.txt file in leaderboard/")
        old, old_splits = load_release(old, root / "leaderboard" / name)
        require(old["id"] not in releases, f"duplicate release {old['id']}")
        releases[old["id"]] = (old, old_splits)
    raw = load_json(root / "leaderboard/protocols.json")
    require(isinstance(raw, list), "protocols.json must be a list")
    protocols = {}
    for p in raw:
        mapping(p, "protocol")
        pid = text(p.get("id"), "protocol.id")
        require(ID.fullmatch(pid) and pid not in protocols, "invalid or duplicate protocol ID")
        require(p.get("task") in MODES and p.get("input_mode") in MODES[p["task"]], "invalid protocol task/input")
        require(p.get("track") in {"fixed_prompt", "agent"}, "invalid protocol track")
        require(p.get("release") in releases, "protocol names an unknown release")
        url(p.get("policy_url"), "protocol.policy_url")
        pin(p.get("testcases"), "protocol.testcases")
        url(p["testcases"].get("source"), "protocol.testcases.source")
        for name in ("evaluator_revision",):
            pin({"revision": p.get(name)}, f"protocol.{name}")
        for name in ("verus_version", "rustc_version", "environment", "resource_limits"):
            text(p.get(name), f"protocol.{name}")
        if p["task"] in {"SpecGen", "End2End"}:
            url(p.get("spec_review_policy_url"), "protocol.spec_review_policy_url")
        if p["track"] == "fixed_prompt":
            url(p.get("prompt_policy_url"), "protocol.prompt_policy_url")
        protocols[pid] = p
    return release, releases, protocols


def validate_entry(entry, release, releases, protocols):
    require(entry.is_dir() and not entry.is_symlink(), "entry must be a real directory")
    require(ID.fullmatch(entry.name), "entry directory must be a lowercase submission ID")
    digest = fingerprint(entry)
    require((entry / "review.json").is_file() and not (entry / "review.json").is_symlink(), "missing review.json")
    m = load_yaml(entry / "metadata.yaml")
    require(type(m.get("format_version")) is int and m["format_version"] == 1, "unsupported format_version")
    require(m.get("submission_id") == entry.name, "submission_id must match directory")
    iso_date(m.get("submitted_on"), "submitted_on")
    if (entry / "README.md").exists():
        text((entry / "README.md").read_text(), "methodology README")
    system = mapping(m.get("system"), "system")
    for key in ("name", "version", "team", "contact", "description"):
        text(system.get(key), f"system.{key}")
    strings(system.get("authors"), "system.authors", nonempty=True)
    require(system.get("category") in {"fixed_prompt", "agent"}, "invalid system.category")
    require(system.get("source_availability") in {"public", "private", "unavailable"}, "invalid source availability")
    for key in ("source_url", "report_url", "release_url"):
        if system.get(key) is not None:
            url(system[key], f"system.{key}")
    if system.get("organization") is not None:
        text(system["organization"], "system.organization")
    logo = system.get("logo")
    if logo is not None:
        text(logo, "system.logo")
        if LOGO.fullmatch(logo):
            require((entry.parent.parent / "docs" / logo).is_file(), "system.logo file is missing from docs/")
        else:
            url(logo, "system.logo")
    models = system.get("models")
    require(isinstance(models, list) and models, "list underlying models")
    for model in models:
        mapping(model, "model")
        text(model.get("id"), "model.id")
        if model.get("name") is not None:
            text(model["name"], "model.name")
        text(model.get("role"), "model.role")
        mapping(model.get("settings"), "model.settings")
    exp = mapping(m.get("experiment"), "experiment")
    task, mode = exp.get("task"), exp.get("input_mode")
    require(task in MODES and mode in MODES[task], "invalid task/input_mode combination")
    require(type(exp.get("independent_runs")) is int and exp["independent_runs"] == 1
            and type(exp.get("attempts_per_problem_per_run")) is int and exp["attempts_per_problem_per_run"] == 1,
            "initial registry requires one independent execution and one final output per problem")
    for key in ("input_description", "attempt_definition", "attempt_schedule", "candidate_selection", "human_intervention"):
        text(exp.get(key), f"experiment.{key}")
    access = mapping(exp.get("generation_access"), "generation_access")
    for key in ("official_positive_tests", "official_mutated_tests", "reference_code", "reference_specifications",
                "reference_proofs", "compiler_and_verus_feedback", "participant_created_tests", "web_and_other_retrieval"):
        text(access.get(key), f"generation_access.{key}")
    budget = mapping(exp.get("budget"), "budget")
    text(budget.get("scope"), "budget.scope")
    text(budget.get("notes"), "budget.notes")
    if budget.get("measured_usage_path") is not None:
        relative(budget["measured_usage_path"], "budget.measured_usage_path")
    total_cost = budget.get("total_cost_usd")
    if total_cost is not None:
        require(type(total_cost) in (int, float) and math.isfinite(total_cost) and total_cost >= 0,
                "budget.total_cost_usd must be a finite nonnegative USD amount or null")
        text(budget.get("cost_notes"), "budget.cost_notes")
    for key in ("max_internal_candidates", "max_repair_iterations", "max_llm_calls", "max_input_tokens", "max_output_tokens", "max_wall_time_seconds"):
        require(key in budget, f"missing budget.{key}")
        value = budget[key]
        require(value is None or (type(value) in (int, float) and math.isfinite(value) and value >= 0), f"invalid budget.{key}")
    benchmark = mapping(m.get("benchmark"), "benchmark")
    require(benchmark.get("release") in releases, f"benchmark.release must be one of: {', '.join(releases)}")
    entry_release, release_splits = releases[benchmark["release"]]
    require(benchmark.get("revision") == entry_release["benchmark_revision"], "benchmark.revision does not match the declared release")
    require(benchmark.get("problem_ids_path") == "problem_ids.txt", "use local problem_ids.txt")
    ids = problem_ids(entry / "problem_ids.txt")
    require(set(ids) <= set(release_splits["full"]), "unknown/obsolete problem IDs")
    split = benchmark.get("split")
    require(split in {"full", "leetcode", "codeforces", "lite", "custom"}, "invalid split")
    require(split in release_splits or split == "custom", f"release {benchmark['release']} has no {split} split")
    if split != "custom":
        expected = set(release_splits[split])
        require(set(ids) == expected, f"{split} requires all {len(expected)} problems, including failures")
    require(type(benchmark.get("problem_count")) is int and benchmark["problem_count"] == len(ids), "incorrect problem_count")
    text(benchmark.get("selection_and_exclusions"), "selection_and_exclusions")
    tests = mapping(benchmark.get("testcases"), "testcases")
    pin(tests, "testcases", required=False)
    if tests.get("source") is not None:
        url(tests["source"], "testcases.source")
        pin(tests, "testcases")
    else:
        require(not tests.get("revision") and not tests.get("archive_sha256"), "testcase pin requires source")
    text(tests.get("modifications"), "testcases.modifications")
    artifacts = mapping(m.get("artifacts"), "artifacts")
    require(artifacts.get("availability") in {"public", "private_by_arrangement", "pending"}, "invalid artifact availability")
    pin(artifacts, "artifacts", required=artifacts["availability"] != "pending")
    if artifacts.get("bundle_url") is not None:
        url(artifacts["bundle_url"], "artifacts.bundle_url")
    require(artifacts["availability"] != "public" or artifacts.get("bundle_url"), "public artifacts need a URL")
    text(artifacts.get("missing_records_and_redactions"), "missing_records_and_redactions")
    for key in ("results_path", "programs_path", "logs_path", "traces_path"):
        relative(artifacts.get(key), f"artifacts.{key}")
    if artifacts.get("readme_path") is not None:
        relative(artifacts["readme_path"], "artifacts.readme_path")
    traces = {"traces_url": artifacts.get("traces_url")} if artifacts.get("traces_url") is not None else {}
    # A full-split entry may also link trajectories restricted to another split, such as Lite.
    split_traces = artifacts.get("split_traces_urls") or {}
    mapping(split_traces, "artifacts.split_traces_urls")
    for view, link in split_traces.items():
        require(split == "full" and view in release_splits and view != "full",
                "artifacts.split_traces_urls is for the other splits of a full-split entry")
        traces[f"split_traces_urls.{view}"] = link
    for key, link in traces.items():
        url(link, f"artifacts.{key}")
        require(re.search(r"(?<![0-9a-f])(?:[0-9a-f]{40}|[0-9a-f]{64})(?![0-9a-f])", link),
                f"artifacts.{key} must be pinned with a full commit SHA or sha256")
    evaluation = mapping(m.get("evaluation"), "evaluation")
    strings(evaluation.get("commands"), "evaluation.commands")
    setting = evaluation.get("protocol_id")
    require(setting is None or setting in protocols, "unknown evaluation protocol_id")
    if setting is not None:
        p = protocols[setting]
        require((p["task"], p["input_mode"], p["track"]) == (task, mode, system["category"]), "protocol task/input/track mismatch")
        require(p["release"] == benchmark["release"], "protocol release mismatch")
        for key in ("source", "revision", "archive_sha256"):
            require(tests.get(key) == p["testcases"].get(key), f"protocol testcase {key} mismatch")
        for key in ("evaluator_revision", "verus_version", "rustc_version", "environment", "resource_limits"):
            require(evaluation.get(key) == p[key], f"protocol {key} mismatch")
    records = []
    for line in (entry / "results.jsonl").read_text().splitlines():
        if line.strip():
            records.append(mapping(json.loads(line, object_pairs_hook=unique_pairs), "result"))
    require(len(records) == len(ids) and {r.get("problem_id") for r in records} == set(ids), "results must contain exactly one record per listed problem")
    for r in records:
        require(r.get("run_id") == "run-1" and r.get("attempt_id") == "1", "use run-1 / attempt 1; independent repeats need separate entries")
        require(r.get("generation_status") in {"produced", "failed", "timeout", "not_attempted"}, "invalid generation_status")
        checks = mapping(r.get("checks"), "checks")
        require(set(checks) == {"code_tests", "verus", "spec_tests"}, "record all three component check statuses")
        for key, value in checks.items():
            require(value in CHECK_STATES, f"invalid {key} status")
            require((value == "not_applicable") == (key not in CHECKS[task]), f"incorrect applicability for {key}")
        paths = mapping(r.get("artifacts"), "result.artifacts")
        require(r["generation_status"] != "produced" or paths, "produced output needs an artifact path")
        for path_group in (paths, mapping(r.get("logs"), "result.logs")):
            for key, path in path_group.items():
                relative(path, f"result path {key}")
        text(r.get("notes"), "result.notes")
    cost_count = sum(r["generation_status"] != "not_attempted" for r in records)
    require(total_cost is None or cost_count > 0, "reported cost requires at least one attempted problem")
    review = mapping(load_json(entry / "review.json"), "review")
    status = review.get("status")
    require(status in {"submitted", "automated_checks_complete", "evaluation_checked"}, "invalid review status")
    checked = strings(review.get("checked_problem_ids"), "checked_problem_ids")
    require(set(checked) <= set(ids), "review includes problems outside submission")
    verdicts = mapping(review.get("verdicts"), "verdicts")
    require(set(verdicts) <= set(checked) and all(v in {"pass", "fail", "pending"} for v in verdicts.values()), "invalid review verdicts/scope")
    spec_review = review.get("spec_review")
    require(spec_review in {"pending", "complete", "not_required"}, "invalid spec_review")
    require((spec_review == "not_required") == (task not in {"SpecGen", "End2End"}), "incorrect spec_review applicability")
    require(review.get("artifact_origin") in {"submitter", "team_endpoint"}, "invalid artifact origin")
    reruns = strings(review.get("rerun_problem_ids"), "rerun_problem_ids")
    require(set(reruns) <= set(ids), "rerun scope outside submission")
    require(review["artifact_origin"] != "team_endpoint" or set(reruns) == set(ids), "team_endpoint origin requires fresh runs for entire submission; record partial reruns separately")
    if status == "submitted":
        require(not checked and not verdicts and not reruns and spec_review != "complete", "submitted entry cannot claim maintainer checks")
    else:
        require(review.get("submission_sha256") == digest, "review fingerprint is stale or missing; re-review changed submission")
        strings(review.get("reviewers"), "reviewers", nonempty=True)
        iso_date(review.get("reviewed_on"), "reviewed_on")
        url(review.get("report_url"), "review.report_url")
        require(checked, "review must state checked problem scope")
        require(artifacts["availability"] != "pending", "review requires pinned available artifacts")
        require(evaluation["commands"], "review requires evaluation commands")
        pin({"revision": evaluation.get("evaluator_revision")}, "evaluator")
        for key in ("verus_version", "rustc_version", "environment", "resource_limits"):
            text(evaluation.get(key), f"evaluation.{key}")
        if task != "ProofGen":
            url(tests.get("source"), "testcases.source")
            pin(tests, "testcases")
    score = None
    if status == "evaluation_checked":
        require(setting is not None, "ranking requires a published evaluation protocol")
        require(set(checked) == set(ids) and set(verdicts) == set(ids) and "pending" not in verdicts.values(), "final evaluation requires a verdict for every problem")
        require(spec_review != "pending", "human specification review is incomplete")
        for r in records:
            if verdicts[r["problem_id"]] == "pass":
                require(r["generation_status"] == "produced", "missing output cannot pass")
                for key in CHECKS[task] - {"spec_tests"}:
                    require(r["checks"][key] == "pass", f"accepted problem requires {key} pass")
                require(r["checks"]["spec_tests"] not in {"fail", "error", "timeout"}, "resolve failing spec tests before accepting a problem")
        score = 100 * sum(v == "pass" for v in verdicts.values()) / len(ids)
    # A full-split entry also covers every other split of its release completely, so
    # it is shown in the LeetCode, Codeforces and Lite views, scored on their problems.
    views = [v for v in release_splits if split == "full" or v == split]
    split_counts, split_scores = {}, {}
    for view in views:
        part = release_splits[view]
        split_counts[view] = len(part)
        split_scores[view] = (100 * sum(verdicts[p] == "pass" for p in part) / len(part)
                              if score is not None and part else None)
    return {"id": entry.name, "date": m["submitted_on"],
            "benchmark_release": benchmark["release"], "system": system["name"],
            "release_url": system.get("release_url"),
            "trajectory_availability": artifacts["availability"],
            "trajectory_url": artifacts.get("traces_url")
                              or (artifacts.get("bundle_url") if artifacts["availability"] == "public" else None),
            "trajectory_path": artifacts.get("traces_path") if artifacts["availability"] == "public" else None,
            "split_trajectory_urls": dict(split_traces),
            "version": system["version"], "team": system["team"],
            "org": system.get("organization") or system["team"], "org_logo": logo, "models": [v["id"] for v in models],
            "model_names": list(dict.fromkeys(v.get("name") or v["id"] for v in models)),
            "track": system["category"], "task": task, "input_mode": mode, "split": split,
            "problem_count": len(ids), "protocol_id": setting, "status": status, "score": score,
            "split_scores": split_scores, "split_problem_counts": split_counts,
            "rankable": score is not None and split != "custom", "budget": budget,
            "avg_cost_usd": total_cost / cost_count if total_cost is not None else None,
            "cost_problem_count": cost_count if total_cost is not None else None,
            "artifact_url": artifacts.get("bundle_url") if artifacts["availability"] == "public" else None,
            "artifact_availability": artifacts["availability"], "review_url": review.get("report_url"),
            "artifact_origin": review["artifact_origin"], "rerun_count": len(reruns),
            "checked_count": len(checked), "spec_review": spec_review,
            "component_counts": {k: dict(Counter(r["checks"][k] for r in records)) for k in ("code_tests", "verus", "spec_tests")},
            "entry_url": f"https://github.com/HIPREL-Group/VeriContest/tree/main/submissions/{entry.name}"}


def build(root):
    release, releases, protocols = load_config(root)
    entries = []
    for entry in sorted((root / "submissions").iterdir()):
        if entry.is_dir():
            try:
                entries.append(validate_entry(entry, release, releases, protocols))
            except (ValueError, TypeError, KeyError, OSError, yaml.YAMLError) as exc:
                raise Invalid(f"{entry.name}: {exc}") from exc
    return {"release": release,
            "releases": [{k: r[k] for k in ("id", "git_tag", "counts", "lite") if k in r} for r, _ in releases.values()],
            "protocols": list(protocols.values()), "entries": entries}


def initialize(root, args, output_dir=None):
    require(ID.fullmatch(args.id), "use a lowercase submission ID with letters, digits, hyphens or underscores")
    require(args.input_mode in MODES[args.task], "invalid task/input mode")
    release, releases, _ = load_config(root)
    chosen = getattr(args, "release", None) or release["id"]
    require(chosen in releases, f"--release must be one of: {', '.join(releases)}")
    release = releases[chosen][0]
    require(args.split in releases[chosen][1], f"release {chosen} has no {args.split} split")
    ids = releases[chosen][1][args.split]
    entry = (output_dir if output_dir is not None else root / "submissions") / args.id
    require(not entry.exists(), "entry already exists; refusing to overwrite")
    m = load_yaml(root / "templates/submission/metadata.template.yaml")
    m.update(submission_id=args.id, submitted_on=date.today().isoformat())
    m["system"]["category"] = args.track
    m["experiment"].update(task=args.task, input_mode=args.input_mode, independent_runs=1, attempts_per_problem_per_run=1)
    m["benchmark"].update(release=release["id"], revision=release["benchmark_revision"], split=args.split,
                          problem_count=len(ids), selection_and_exclusions="Complete declared split; no exclusions.")
    review = load_json(root / "templates/submission/review.template.json")
    if args.task not in {"SpecGen", "End2End"}:
        review["spec_review"] = "not_required"
    entry.mkdir(parents=True)
    (entry / "metadata.yaml").write_text(yaml.safe_dump(m, sort_keys=False))
    (entry / "review.json").write_text(json.dumps(review, indent=2) + "\n")
    (entry / "README.md").write_text((root / "templates/submission/README.template.md").read_text())
    (entry / "problem_ids.txt").write_text("\n".join(ids) + "\n")
    rows = [{"problem_id": p, "run_id": "run-1", "attempt_id": "1", "generation_status": "not_attempted",
             "artifacts": {}, "checks": {k: "not_run" if k in CHECKS[args.task] else "not_applicable"
                                        for k in ("code_tests", "verus", "spec_tests")},
             "logs": {}, "notes": "No output supplied yet."} for p in ids]
    (entry / "results.jsonl").write_text("".join(json.dumps(r) + "\n" for r in rows))
    print(f"Created {entry}. Fill metadata placeholders, complete or delete the optional README.md, "
          "and replace result records before validation.")
    return entry


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    commands = parser.add_subparsers(dest="command", required=True)
    p = commands.add_parser("init", help="scaffold one complete split without inventing results")
    p.add_argument("--id", required=True)
    p.add_argument("--track", choices=["fixed_prompt", "agent"], required=True)
    p.add_argument("--task", choices=list(MODES), default="End2End")
    p.add_argument("--input-mode", default="nl")
    p.add_argument("--split", choices=["full", "leetcode", "codeforces", "lite"], default="full")
    p.add_argument("--release", help="benchmark release ID (default: the current release)")
    p = commands.add_parser("validate", help="validate registry or one entry; never executes submissions")
    p.add_argument("--entry", type=Path)
    p = commands.add_parser("build", help="validate and emit static website data")
    p.add_argument("--output", type=Path, default=ROOT / "docs/static/leaderboard.json")
    p = commands.add_parser("fingerprint", help="hash pinned entry files for maintainer review")
    p.add_argument("entry", type=Path)
    args = parser.parse_args()
    try:
        if args.command == "init":
            initialize(ROOT, args)
        elif args.command == "fingerprint":
            print(fingerprint(args.entry))
        elif args.command == "validate" and args.entry:
            validate_entry(args.entry, *load_config(ROOT))
            print(f"Valid submission: {args.entry.name}")
        else:
            data = build(ROOT)
            if args.command == "build":
                args.output.parent.mkdir(parents=True, exist_ok=True)
                args.output.write_text(json.dumps(data, indent=2, allow_nan=False) + "\n")
                print(f"Built {args.output}")
            print(f"Validated {len(data['entries'])} submissions for {data['release']['id']}.")
    except (ValueError, KeyError, TypeError, OSError, yaml.YAMLError) as exc:
        print(f"ERROR: {exc}", file=sys.stderr)
        return 1
    return 0


if __name__ == "__main__":
    sys.exit(main())
