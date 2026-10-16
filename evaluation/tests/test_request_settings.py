import contextlib
import importlib.util
import io
import json
from pathlib import Path
import sys
import tempfile
import unittest
from unittest.mock import patch

sys.path.insert(0, str(Path(__file__).resolve().parents[1]))
from vceval import generate
from vceval.request_settings import request_parameters, validate_extra_body, validate_token_limit


class RequestSettings(unittest.TestCase):
    def test_fixed_fields_and_aliases_cannot_be_overridden(self):
        for key in ("model", "messages", "input", "instructions", "system", "prompt",
                    "temperature", "top_p", "max_tokens", "max_output_tokens",
                    "max_completion_tokens", "max_new_tokens", "n", "best_of",
                    "tools", "previous_response_id", "stream"):
            for backend in ("openai-chat", "openai-responses", "anthropic"):
                with self.subTest(key=key, backend=backend):
                    with self.assertRaisesRegex(ValueError, "runner-controlled Model-track field"):
                        request_parameters(backend, "declared-model", "fixed-prompt", 16384, 0, {key: "override"})
        with self.assertRaisesRegex(ValueError, "config.temperature"):
            validate_extra_body({"config": {"temperature": 1}})

    def test_provider_options_are_retained_without_mutation(self):
        extra = {"reasoning": {"effort": "high"}, "seed": 42,
                 "chat_template_kwargs": {"enable_thinking": True}}
        params, forwarded = request_parameters("openai-chat", "model", "prompt", 16384, 0, extra)
        self.assertEqual(forwarded, extra)
        self.assertEqual(params["n"], 1)
        self.assertEqual(params["max_tokens"], 16384)
        forwarded["reasoning"]["effort"] = "low"
        self.assertEqual(extra["reasoning"]["effort"], "high")

    def test_no_temperature_is_explicit_and_cannot_be_undone(self):
        params, _ = request_parameters("anthropic", "model", "prompt", 16384, None,
                                       {"thinking": {"type": "enabled", "budget_tokens": 2048}})
        self.assertNotIn("temperature", params)
        with self.assertRaises(ValueError):
            request_parameters("anthropic", "model", "prompt", 16384, None, {"temperature": 1})

    def test_invalid_json_shapes_and_nonfinite_numbers(self):
        for value in (None, [], 1, "settings", {"x": float("nan")}, {"x": float("inf")}):
            with self.subTest(value=value), self.assertRaises(ValueError):
                validate_extra_body(value)

    def test_temperature_is_omitted_by_default_or_explicitly_configured(self):
        for flags, expected in (([], None), (["--no-temperature"], None),
                                (["--temperature", "0"], 0.0),
                                (["--temperature", "0.7"], 0.7)):
            with self.subTest(flags=flags), tempfile.TemporaryDirectory() as tmp:
                args = ["--task", "End2End", "--input-mode", "nl", "--backend", "openai-chat",
                        "--model", "model", "--out", tmp, "--problems", "lc1", "--dry-run"]
                with contextlib.redirect_stdout(io.StringIO()):
                    generate.main(args + flags)
                saved = json.loads((Path(tmp) / "run.json").read_text())
                self.assertEqual(saved["temperature"], expected)
                for backend in ("openai-chat", "openai-responses", "anthropic"):
                    params, _ = request_parameters(backend, "model", "prompt", 16384, saved["temperature"], {})
                    if expected is None:
                        self.assertNotIn("temperature", params)
                    else:
                        self.assertEqual(params["temperature"], expected)

    def test_invalid_or_conflicting_temperatures_do_not_start_run(self):
        for flags in (["--temperature", "nan"], ["--temperature", "inf"],
                      ["--temperature", "-1"], ["--temperature", "0", "--no-temperature"]):
            with self.subTest(flags=flags), tempfile.TemporaryDirectory() as tmp:
                out = Path(tmp) / "run"
                args = ["--task", "End2End", "--input-mode", "nl", "--backend", "openai-chat",
                        "--model", "model", "--out", str(out), "--dry-run"]
                with contextlib.redirect_stderr(io.StringIO()), self.assertRaises(SystemExit) as exc:
                    generate.main(args + flags)
                self.assertEqual(exc.exception.code, 2)
                self.assertFalse(out.exists())

    def test_optional_token_limit_and_values_above_old_cap(self):
        for backend, limit in (("openai-chat", None), ("openai-responses", None),
                               ("openai-chat", 32768), ("openai-responses", 65536),
                               ("anthropic", 32768)):
            with self.subTest(backend=backend, limit=limit), tempfile.TemporaryDirectory() as tmp:
                args = ["--task", "End2End", "--input-mode", "nl", "--backend", backend,
                        "--model", "model", "--out", tmp, "--problems", "lc1", "--dry-run"]
                if limit is not None:
                    args += ["--max-output-tokens", str(limit)]
                with contextlib.redirect_stdout(io.StringIO()):
                    generate.main(args)
                saved = json.loads((Path(tmp) / "run.json").read_text())
                self.assertEqual(saved["max_output_tokens"], limit)
                params, _ = request_parameters(backend, "model", "prompt", limit, None, {})
                key = "max_output_tokens" if backend == "openai-responses" else "max_tokens"
                if limit is None:
                    self.assertNotIn(key, params)
                else:
                    self.assertEqual(params[key], limit)

    def test_token_limit_errors_are_reported_before_run_creation(self):
        for backend, flags in (("anthropic", []), ("openai-chat", ["--max-output-tokens", "0"]),
                               ("openai-chat", ["--max-output-tokens", "-1"]),
                               ("openai-chat", ["--max-output-tokens", "1.5"])):
            with self.subTest(backend=backend, flags=flags), tempfile.TemporaryDirectory() as tmp:
                out = Path(tmp) / "run"
                args = ["--task", "End2End", "--input-mode", "nl", "--backend", backend,
                        "--model", "model", "--out", str(out), "--dry-run"]
                with contextlib.redirect_stderr(io.StringIO()), self.assertRaises(SystemExit) as exc:
                    generate.main(args + flags)
                self.assertEqual(exc.exception.code, 2)
                self.assertFalse(out.exists())
        for value in (True, 0, -1, 1.5):
            with self.assertRaises(ValueError):
                validate_token_limit("openai-chat", value)

    def test_resuming_cannot_change_declared_token_limit(self):
        with tempfile.TemporaryDirectory() as tmp:
            args = ["--task", "End2End", "--input-mode", "nl", "--backend", "openai-chat",
                    "--model", "model", "--out", tmp, "--problems", "lc1", "--dry-run"]
            with contextlib.redirect_stdout(io.StringIO()):
                generate.main(args)
            with self.assertRaisesRegex(SystemExit, "max_output_tokens"):
                generate.main(args + ["--max-output-tokens", "32768"])

    def test_cli_rejects_before_creating_run_or_loading_api(self):
        with tempfile.TemporaryDirectory() as tmp:
            out = Path(tmp) / "run"
            args = ["--task", "End2End", "--input-mode", "nl", "--backend", "openai-chat",
                    "--model", "model", "--out", str(out), "--dry-run"]
            for extra in ('{"n":2}', '[]', '{bad json', '{"temperature":NaN}'):
                with patch.object(generate.backends, "load") as load, \
                     contextlib.redirect_stderr(io.StringIO()), self.assertRaises(SystemExit) as exc:
                    generate.main(args + ["--extra-body", extra])
                self.assertEqual(exc.exception.code, 2)
                load.assert_not_called()
                self.assertFalse(out.exists())

    def test_dry_run_records_provider_options_and_prevents_resume_changes(self):
        with tempfile.TemporaryDirectory() as tmp:
            args = ["--task", "End2End", "--input-mode", "nl", "--backend", "openai-chat",
                    "--model", "model", "--out", tmp, "--problems", "lc1", "--dry-run"]
            with contextlib.redirect_stdout(io.StringIO()):
                generate.main(args + ["--extra-body", '{"reasoning_effort":"high"}'])
            saved = json.loads((Path(tmp) / "run.json").read_text())
            self.assertEqual(saved["extra_body"], {"reasoning_effort": "high"})
            with self.assertRaisesRegex(SystemExit, "different settings"):
                generate.main(args + ["--extra-body", '{"reasoning_effort":"low"}'])


@unittest.skipUnless(all(importlib.util.find_spec(m) for m in ("openai", "anthropic", "httpx")),
                     "install evaluation/requirements.txt for SDK transport tests")
class SDKRequests(unittest.TestCase):
    def test_all_backends_block_overrides_and_send_declared_parameters(self):
        import httpx
        import openai
        import anthropic
        from vceval.backends.openai_compat import ChatBackend, ResponsesBackend
        from vceval.backends.anthropic_messages import Backend

        for cls, sdk, extra in (
            (ChatBackend, openai.OpenAI, {"reasoning_effort": "high"}),
            (ResponsesBackend, openai.OpenAI, {"reasoning": {"effort": "high"}}),
            (Backend, anthropic.Anthropic, {"thinking": {"type": "enabled", "budget_tokens": 2048}}),
        ):
            sent = []

            def respond(request):
                sent.append(json.loads(request.content))
                # A local 400 lets us inspect the real SDK serialization without
                # constructing three response schemas. No network or credentials.
                return httpx.Response(400, json={"error": {"type": "invalid_request_error", "message": "fixture"}})

            backend = cls.__new__(cls)
            backend.model = "declared-model"
            backend.client = sdk(api_key="test-only", base_url="https://example.invalid",
                                 max_retries=0, http_client=httpx.Client(transport=httpx.MockTransport(respond)))
            try:
                with self.subTest(backend=backend.name):
                    with self.assertRaises(ValueError):
                        backend.complete("fixed-prompt", 16384, 0, {"model": "override"})
                    self.assertEqual(sent, [])
                    limit = 32768 if backend.name == "anthropic" else None
                    with tempfile.TemporaryDirectory() as tmp:
                        status = generate.run_one(backend, (), ("End2End", "nl"), "leetcode/lc1",
                                                  Path(tmp), None, extra, max_output_tokens=limit)
                        self.assertEqual(status, "failed")  # the mock's HTTP 400
                        record = json.loads((Path(tmp) / "trajectories/leetcode/lc1.json").read_text())
                    self.assertEqual(len(sent), 1)
                    logged = record["request"]["generation_parameters"]
                    for key, value in logged.items():
                        self.assertEqual(sent[0][key], value)
                    self.assertEqual(sent[0]["model"], "declared-model")
                    self.assertEqual(record["request"]["max_output_tokens"], limit)
                    token_key = "max_output_tokens" if backend.name == "openai-responses" else "max_tokens"
                    if limit is None:
                        self.assertNotIn(token_key, sent[0])
                    else:
                        self.assertEqual(sent[0][token_key], limit)
                    self.assertNotIn("temperature", sent[0])
                    for key, value in extra.items():
                        self.assertEqual(sent[0][key], value)
                    with self.assertRaises((openai.APIStatusError, anthropic.APIStatusError)):
                        backend.complete("fixed-prompt", 32768, 0.7, extra)
                    self.assertEqual(len(sent), 2)
                    self.assertEqual(sent[1]["temperature"], 0.7)
                    self.assertEqual(sent[1][token_key], 32768)
            finally:
                backend.client.close()
