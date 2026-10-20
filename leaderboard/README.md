# Leaderboard maintenance

This directory holds the submission registry and builds the website's leaderboard
data. Generation and scoring are in [evaluation/](../evaluation/README.md), and the
specification review standard is [SPEC_REVIEW.md](SPEC_REVIEW.md). See
[submissions/README.md](../submissions/README.md) for participant instructions.

## Files and commands

- `release.json` pins the current benchmark revision and split counts.
- `releases.json` lists earlier releases that still accept submissions, each with
  its revision, counts, and problem list.
- `problem_ids.txt` lists all 1,006 problems of the current release, bound by the manifest hash.
- `lite_problem_ids.txt` lists the 300 problems of VeriContest Lite, also pinned in
  `release.json`. `make_lite.py` selects it using `lite_measurements.jsonl`.
  See [LITE.md](LITE.md).
- `protocols.json` lists the published evaluation settings: for release 2026-10.1,
  one Model-track setting per task and input mode.
- `manage.py` scaffolds/validates entries and builds `docs/static/leaderboard.json`.
- `dry_run.py` prepares and validates a synthetic example in a new local directory,
  including a ZIP bundle. It never adds an entry to the public registry.
- `../submissions/<id>/` contains public submission and review records.

```bash
python3 -m pip install -r leaderboard/requirements.txt
python3 leaderboard/manage.py validate
python3 leaderboard/manage.py build
python3 leaderboard/dry_run.py
python3 leaderboard/make_lite.py select
python3 -m unittest discover -s leaderboard -p 'test_*.py'
node --test leaderboard/test_frontend.cjs
python3 -m http.server 8000 --directory docs
```

Open `http://localhost:8000` for a local preview. The page fetches generated JSON,
so opening the HTML directly through `file://` is not supported.
The homepage lists two benchmarks in its sidebar: VeriContest, with Full, LeetCode
and Codeforces coverage, and VeriContest Lite. It shows complete splits only; a
full-split entry also appears in the other three views, scored on their problems. Protocols remain
recorded for every checked result; the setting selector is hidden for zero or one
matching protocol and appears when multiple protocols need to be distinguished.

## Publish an evaluation setting

Before promoting an entry to `evaluation_checked`, add its agreed protocol to
`protocols.json` in a maintainer-reviewed PR. Each protocol has these fields:

| Field | Meaning |
|---|---|
| `id` | Stable lowercase identifier; do not change an existing setting in place |
| `label` | Optional display name |
| `release` | A release ID from `release.json` or `releases.json`, e.g. `2026-10.1` |
| `track` | `fixed_prompt` or `agent` |
| `task`, `input_mode` | An allowed pair from `MODES` in `manage.py` |
| `policy_url` | HTTPS link to the frozen evaluation/generation policy |
| `testcases` | Object with `source`, `revision` and/or `archive_sha256`; immutable testcase pin |
| `evaluator_revision` | Full evaluator commit SHA |
| `verus_version`, `rustc_version` | Exact versions used |
| `environment`, `resource_limits` | Pinned environment and compile/proof/test limits |
| `spec_review_policy_url` | Required for SpecGen/End2End; documented human review procedure |
| `prompt_policy_url` | Required for the Model track; standardized prompts/generation settings |

Use commit-pinned policy links. Explain all pass/fail rules, unsupported cases,
feedback restrictions, trust boundaries, and infrastructure-error handling in
the linked policy. Policies must cover input-precondition validity and sufficient
postconditions for SpecGen/End2End. Merely passing Verus is insufficient.

The submission's `evaluation.protocol_id` must match a protocol's task, input,
track, testcase pin, evaluator, toolchain, environment, and limits. Protocol IDs
are comparison groups, not a claim that all systems consume equal inference
compute. The UI displays declared budgets alongside scores.

## Check a submission

1. Validate the entry. Check that the methodology and all feedback comply with
   the chosen protocol. Arrange any private bundle access.
2. Retrieve the immutable bundle and check its integrity and complete artifact
   coverage. The metadata validator checks pin syntax, not remote availability.
3. Independently execute applicable tests and proof checks in an isolated
   environment without credentials, with explicit resource limits. Use the
   pinned custom checkers where required. Inspect code/contract correspondence
   and verifier trust boundaries. Record results and any infrastructure issues.
4. Complete required human specification review under the published procedure.
   Do not mark specs correct merely because tests or proofs pass. Unsupported
   translations need manual handling; unresolved cases keep evaluation pending.
5. Update component results to agree with the evaluation evidence and record
   final pass/fail verdicts in `review.json`.
6. Compute the entry fingerprint after the final metadata/result edits:

   ```bash
   python3 leaderboard/manage.py fingerprint submissions/<id>
   ```

7. Add the fingerprint, reviewer handles, ISO date, public report link,
   `checked_problem_ids`, and `spec_review` state to `review.json`. The report
   must identify the exact artifact revision, scope, procedures, and limitations.
8. Set `status` to `evaluation_checked` only when every problem has a final
   verdict and a published protocol is selected. Keep failures/missing outputs
   in the denominator. Validate again and obtain maintainer PR approval.

`review.json` starts from [the template](../templates/submission/review.template.json).
`verdicts` maps problem IDs to `pass`, `fail`, or `pending`. Final evaluation
requires every declared ID and no pending verdicts. For non-spec tasks,
`spec_review` is `not_required`; otherwise use `pending` or `complete`.
`automated_checks_complete` records the checked scope and evidence but never
publishes an official score. `evaluation_checked` derives the score from final
verdicts; custom subsets remain unranked.

`artifact_origin: team_endpoint` means all submitted outputs came from fresh
team-initiated executions, so `rerun_problem_ids` must cover the whole entry.
For a supplied artifact bundle with only sampled reruns, keep origin `submitter`
and record the sampled IDs. The UI states this scope separately from the score.

## Publication and GitHub settings

PR CI validates records and runs registry/ranking tests. It never downloads
artifact bundles, runs the submitted programs, or invokes models. The Pages
workflow validates and builds data from merged records, then deploys the existing
`docs/` site. No separate application server or database is required.

Repository administrators should require PR review and the **Validate leaderboard
submissions / validate** check on `main`, and require maintainer approval for
changes to review records, release metadata, protocols, and workflow code. These
GitHub settings are configured separately; files in this repository do not
activate branch protection. A submitter-supplied reviewer name is not an
independent attestation until a maintainer approves the record.

The small generated JSON is committed for easy previews and regenerated on
publication. Do not edit it by hand. Test fixtures live only in temporary
directories.

## Changes to releases and results

Each entry declares the benchmark release and revision it was evaluated on, and
the registry accepts any release in `release.json` or `releases.json`. Entries are
ranked only against entries under the same protocol, and every protocol belongs
to one release, so results from different releases are never ranked together.
If benchmark membership or scoring-relevant artifacts change, cut a new release
and add protocols for it; keep the previous release in `releases.json`. Do not
reinterpret historical paper scores as results on the 1,006-problem release.
Follow [RELEASING.md](../RELEASING.md) when cutting a release or upgrading Verus.
