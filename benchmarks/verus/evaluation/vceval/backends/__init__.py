"""Model API backends for the Model-track runner. Each SDK lives in its own
module and is imported only when selected."""
from __future__ import annotations

BACKENDS = ("openai-chat", "openai-responses", "anthropic")


def load(name: str, model: str, max_retries: int, base_url: str | None):
    if name == "anthropic":
        from . import anthropic_messages as mod
        return mod.Backend(model, max_retries, base_url), mod.transport_errors()
    from . import openai_compat as mod
    cls = mod.ChatBackend if name == "openai-chat" else mod.ResponsesBackend
    return cls(model, max_retries, base_url), mod.transport_errors()
