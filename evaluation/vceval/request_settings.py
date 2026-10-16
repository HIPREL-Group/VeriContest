"""Keep provider extensions separate from the fixed Model-track request.

Provider-specific reasoning settings remain configurable and recorded. They
are not automatically approved for ranking: the published protocol and review
must establish comparability. This protects the supplied runner against silent
overrides, not against a modified runner or a server ignoring its request.
"""
from __future__ import annotations

from copy import deepcopy
import math


# Include aliases used by compatible endpoints, even if not sent by our SDKs.
# Temperature and token limits have explicit CLI options and must not be
# shadowed by extra_body. Reject rather than discard: records describe the run.
RESERVED_FIELDS = frozenset({
    "model", "model_name", "messages", "prompt", "input", "instructions", "system",
    "previous_response_id", "conversation", "tools", "tool_choice", "functions", "function_call",
    "max_tokens", "max_completion_tokens", "max_output_tokens", "max_new_tokens",
    "min_tokens", "min_new_tokens", "n", "best_of", "num_return_sequences",
    "temperature", "top_p", "top_k", "min_p", "typical_p", "do_sample",
    "stop", "stop_sequences", "stream", "stream_options", "extra_body",
})


def validate_extra_body(value: object) -> dict:
    """Validate before writing a run or contacting a provider.

    Check nested objects too: compatible providers can nest generation
    parameters in their own config objects. Accept JSON values only.
    """
    if not isinstance(value, dict):
        raise ValueError("--extra-body must be a JSON object")

    def visit(node, path):
        if isinstance(node, dict):
            for key, child in node.items():
                if not isinstance(key, str):
                    raise ValueError("--extra-body object keys must be strings")
                location = f"{path}.{key}" if path else key
                if key in RESERVED_FIELDS:
                    raise ValueError(f"--extra-body cannot set runner-controlled Model-track field '{location}'; "
                                     "use the runner's declared options or a different evaluation protocol")
                visit(child, location)
        elif isinstance(node, list):
            for i, child in enumerate(node):
                visit(child, f"{path}[{i}]")
        elif type(node) is float:
            if not math.isfinite(node):
                raise ValueError(f"--extra-body requires finite JSON numbers: {path}")
        elif node is not None and type(node) not in (str, bool, int):
            raise ValueError(f"--extra-body contains a non-JSON value: {path}")

    visit(value, "")
    return deepcopy(value)


def validate_temperature(value: float | None) -> float | None:
    if value is not None and (type(value) not in (int, float)
                              or not math.isfinite(value) or value < 0):
        raise ValueError("--temperature must be a finite nonnegative number")
    return value


def validate_token_limit(backend: str, value: int | None) -> int | None:
    if value is not None and (type(value) is not int or value <= 0):
        raise ValueError("--max-output-tokens must be a positive integer")
    if backend == "anthropic" and value is None:
        raise ValueError("the Anthropic API requires --max-output-tokens; choose a model-supported "
                         "value (VeriContest does not impose a shared limit)")
    return value


def request_parameters(backend: str, model: str, prompt: str, max_tokens: int | None,
                       temperature: float | None, extra_body: dict) -> tuple[dict, dict]:
    """Build the parameters used by both the API adapter and trajectory log."""
    extra = validate_extra_body(extra_body)
    temperature = validate_temperature(temperature)
    max_tokens = validate_token_limit(backend, max_tokens)
    if backend == "openai-responses":
        params = {"model": model, "input": prompt}
        token_field = "max_output_tokens"
    elif backend in ("openai-chat", "anthropic"):
        params = {"model": model, "messages": [{"role": "user", "content": prompt}]}
        token_field = "max_tokens"
        if backend == "openai-chat":
            params["n"] = 1
    else:
        raise ValueError(f"unknown backend: {backend}")
    if max_tokens is not None:
        params[token_field] = max_tokens
    if temperature is not None:
        params["temperature"] = temperature
    return params, extra
