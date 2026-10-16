"""Model-track runner: the fixed VeriContest prompt, one sample per problem, no feedback.

Writes, under ``--out``:
  run.json                        settings of this run (disclose in metadata.yaml)
  programs/<family>/<problem>.rs  extracted final programs (input to score.py)
  programs/generation.jsonl       generation_status per problem
  trajectories/<family>/<problem>.json  exact prompt and raw response
"""
from __future__ import annotations

import argparse
import hashlib
import json
import os
import threading
import time
from concurrent.futures import ThreadPoolExecutor, as_completed
from datetime import datetime, timezone
from pathlib import Path

from . import backends
from .config import GENERATION, PROMPT_DIR, TASKS, release_info
from .extract import extract_program
from .problems import all_problem_ids, problem_dir, select
from .request_settings import request_parameters, validate_extra_body, validate_temperature, validate_token_limit


def build_prompt(task_key: tuple[str, str], problem_id: str) -> str:
    spec = TASKS[task_key]
    prompt = (PROMPT_DIR / spec["prompt"]).read_text()
    for placeholder, filename in spec["inputs"].items():
        prompt = prompt.replace("{{" + placeholder + "}}", (problem_dir(problem_id) / filename).read_text())
    return prompt


def _sha(text: str) -> str:
    return hashlib.sha256(text.encode()).hexdigest()


def run_one(backend, transport, task_key, pid, out: Path, temperature, extra_body,
            *, max_output_tokens: int | None = None) -> str:
    prompt = build_prompt(task_key, pid)
    params, extra = request_parameters(backend.name, backend.model, prompt,
                                      max_output_tokens, temperature, extra_body)
    record = {"problem_id": pid, "task": task_key[0], "input_mode": task_key[1],
              "prompt_template": TASKS[task_key]["prompt"], "prompt_sha256": _sha(prompt), "prompt": prompt,
              "request": {"backend": backend.name, "model": backend.model,
                          "max_output_tokens": max_output_tokens,
                          "temperature": temperature, "extra_body": extra,
                          "generation_parameters": {**params, **extra}},
              "started_at": datetime.now(timezone.utc).isoformat()}
    t0 = time.time()
    try:
        response = backend.complete(prompt, max_output_tokens, temperature, extra)
        record["response"] = response
        program = extract_program(response["text"], TASKS[task_key]["extract"])
        status = "produced" if program is not None else "failed"
        record["extraction"] = "ok" if program is not None else "empty response"
    except transport as exc:  # retries exhausted
        status, program = "failed", None
        record["error"] = f"{type(exc).__name__}: {exc}"
    except Exception as exc:  # request rejected (e.g. 400): record it, do not resample
        status, program = "failed", None
        record["error"] = f"{type(exc).__name__}: {exc}"
    record["elapsed_sec"] = round(time.time() - t0, 2)
    record["generation_status"] = status
    traj = out / "trajectories" / f"{pid}.json"
    traj.parent.mkdir(parents=True, exist_ok=True)
    traj.write_text(json.dumps(record, indent=2, default=str) + "\n")
    if program is not None:
        dest = out / "programs" / f"{pid}.rs"
        dest.parent.mkdir(parents=True, exist_ok=True)
        dest.write_text(program)
    return status


def main(argv=None):
    ap = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    ap.add_argument("--task", required=True, choices=sorted({t for t, _ in TASKS}))
    ap.add_argument("--input-mode", required=True)
    ap.add_argument("--backend", required=True, choices=backends.BACKENDS)
    ap.add_argument("--model", required=True, help="exact model ID sent to the API")
    ap.add_argument("--base-url", help="API base URL (e.g. a vLLM server)")
    ap.add_argument("--out", required=True, type=Path)
    ap.add_argument("--split", default="full", choices=["full", "leetcode", "codeforces"])
    ap.add_argument("--problems", help="comma-separated subset (debugging only; not a valid submission)")
    ap.add_argument("--concurrency", type=int, default=8)
    ap.add_argument("--max-output-tokens", type=int, default=GENERATION["max_output_tokens"],
                    help="optional model-specific output-token limit; omitted by default, required for anthropic")
    temperatures = ap.add_mutually_exclusive_group()
    temperatures.add_argument("--temperature", type=float, default=GENERATION["temperature"],
                              help="optional model-specific temperature; omitted from API requests by default")
    temperatures.add_argument("--no-temperature", dest="temperature", action="store_const", const=None,
                              help="explicitly omit temperature (the default; retained for compatibility)")
    ap.add_argument("--extra-body", default="{}",
                    help="JSON of provider-specific parameters, e.g. reasoning/thinking settings "
                         "(recorded for every problem; fixed prompt/model/sampling fields cannot be overridden)")
    ap.add_argument("--dry-run", action="store_true", help="write the prompts only; make no API calls")
    args = ap.parse_args(argv)

    key = (args.task, args.input_mode)
    if key not in TASKS:
        ap.error(f"invalid task/input mode {key}; valid: {sorted(TASKS)}")
    try:
        extra_body = validate_extra_body(json.loads(args.extra_body))
        temperature = validate_temperature(args.temperature)
        max_output_tokens = validate_token_limit(args.backend, args.max_output_tokens)
    except (ValueError, TypeError) as exc:
        ap.error(str(exc))
    ids = select(all_problem_ids(), args.problems, args.split)
    args.out.mkdir(parents=True, exist_ok=True)

    settings = {"task": args.task, "input_mode": args.input_mode, "backend": args.backend, "model": args.model,
                "base_url": args.base_url, "temperature": temperature, "extra_body": extra_body,
                "max_output_tokens": max_output_tokens, "samples_per_problem": 1,
                "max_transport_retries": GENERATION["max_transport_retries"],
                "prompt_template": TASKS[key]["prompt"],
                "prompt_template_sha256": _sha((PROMPT_DIR / TASKS[key]["prompt"]).read_text()),
                "split": args.split, "subset": bool(args.problems), "release": release_info()}
    run_json = args.out / "run.json"
    if run_json.is_file():
        previous = json.loads(run_json.read_text())
        changed = {k for k in settings if k != "started_at" and previous.get(k) != settings[k]}
        if changed:
            raise SystemExit(f"{args.out} holds a run with different settings ({sorted(changed)}); use a new --out")
    settings["started_at"] = datetime.now(timezone.utc).isoformat()
    run_json.write_text(json.dumps(settings, indent=2) + "\n")

    if args.dry_run:
        for pid in ids:
            dest = args.out / "prompts" / f"{pid}.md"
            dest.parent.mkdir(parents=True, exist_ok=True)
            dest.write_text(build_prompt(key, pid))
        print(f"Wrote {len(ids)} prompts to {args.out}/prompts (no API calls).")
        return

    # Resume: a problem with a trajectory is done. A returned response is never resampled.
    statuses = {}
    todo = []
    for pid in ids:
        traj = args.out / "trajectories" / f"{pid}.json"
        if traj.is_file():
            statuses[pid] = json.loads(traj.read_text())["generation_status"]
        else:
            todo.append(pid)
    backend, transport = backends.load(args.backend, args.model, GENERATION["max_transport_retries"], args.base_url)
    lock = threading.Lock()
    print(f"{len(todo)} to generate, {len(statuses)} already done.")
    with ThreadPoolExecutor(max_workers=args.concurrency) as pool:
        futures = {pool.submit(run_one, backend, transport, key, pid, args.out, temperature, extra_body,
                               max_output_tokens=max_output_tokens): pid
                   for pid in todo}
        for n, fut in enumerate(as_completed(futures), 1):
            pid = futures[fut]
            status = fut.result()
            with lock:
                statuses[pid] = status
            print(f"[{n}/{len(todo)}] {pid}: {status}", flush=True)

    manifest = args.out / "programs" / "generation.jsonl"
    manifest.parent.mkdir(parents=True, exist_ok=True)
    manifest.write_text("".join(json.dumps({"problem_id": p, "generation_status": statuses[p]}) + "\n" for p in ids))
    produced = sum(s == "produced" for s in statuses.values())
    print(f"\nproduced {produced}/{len(ids)}. Next: python3 evaluation/score.py --task {args.task} "
          f"--input-mode {args.input_mode} --outputs {args.out}/programs --out {args.out}/eval")


if __name__ == "__main__":
    main()
