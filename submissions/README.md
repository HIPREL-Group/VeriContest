# Submitting to the VeriContest leaderboard

Leaderboard entries live in this directory, one folder per run. To submit, add a
folder for your run and open a pull request. Use
[issues](https://github.com/HIPREL-Group/VeriContest/issues/new?template=submission.yml)
for questions or to arrange private access to your artifacts.

## Steps

1. **Run the evaluation.** Follow the [evaluation guide](../evaluation/README.md).
   Model-track entries use `evaluation/generate.py` with the fixed prompts; every
   entry is scored with `evaluation/score.py`.
2. **Create your entry.** Fork this repository and run

   ```bash
   python3 -m pip install -r leaderboard/requirements.txt
   python3 leaderboard/manage.py init --id <YYYYMMDD_system_task_split> \
     --track fixed_prompt --task End2End --input-mode nl --split full
   ```

   Use `--track agent` for the Agent track and `--release <id>` for an earlier
   release (default: the latest).
3. **Fill in the templates.** Replace every `REPLACE_ME` in `metadata.yaml` and
   `README.md`, and replace the generated records in `results.jsonl` with one
   record per problem, including failures. To show a logo, set `system.logo` to an
   HTTPS image URL or add the file under `docs/static/logos/`.
4. **Publish your artifacts.** Put the generated programs, logs, and a trajectory
   for every attempted problem in an artifact bundle, and pin it in `metadata.yaml`
   with a full commit SHA or the archive's SHA-256. The bundle can be public or
   shared privately with us.
5. **Open a pull request.** Run
   `python3 leaderboard/manage.py validate --entry submissions/<id>` and open a PR
   that adds `submissions/<id>/`. Leave `review.json` as generated; we check the
   results and complete it before the entry is ranked.

To see a complete example entry first, run `python3 leaderboard/dry_run.py`. It
builds one in a temporary directory and never touches this folder.

## Rules

- One run per entry and one final output per problem, covering a complete split
  (`full`, `leetcode`, `codeforces`, or `lite`). Failures and missing outputs stay in the
  denominator. A `full` entry is also shown in the LeetCode, Codeforces and
  [Lite](../leaderboard/LITE.md) views.
- Do not use the official test cases or reference answers during generation or
  selection, beyond the inputs the task provides.
- Trajectories are required. Model track: the request and the raw model response.
  Agent track: every model call, tool call, compiler and Verus call with its
  output, repair step, and the final candidate selection. A `full` entry may also
  link the trajectories of its Lite problems alone (`artifacts.split_traces_urls`),
  which the Lite view then shows.
- Proprietary systems are welcome; the methodology must be public, the pipeline
  source need not be.

Each entry is ranked only against entries evaluated under the same release and
evaluation setting ([`leaderboard/protocols.json`](../leaderboard/protocols.json)).
SpecGen and End2End specifications that cannot be tested automatically are
reviewed under the [specification review standard](../leaderboard/SPEC_REVIEW.md).
