"""Anthropic Messages API backend (official ``anthropic`` SDK)."""
from __future__ import annotations

import anthropic
from ..request_settings import request_parameters


class Backend:
    name = "anthropic"

    def __init__(self, model: str, max_retries: int, base_url: str | None = None):
        self.model = model
        # The SDK retries connection errors, 408/409/429 and >=500 with backoff.
        self.client = anthropic.Anthropic(max_retries=max_retries, base_url=base_url)

    def complete(self, prompt: str, max_tokens: int | None, temperature: float | None, extra_body: dict) -> dict:
        params, extra = request_parameters(self.name, self.model, prompt, max_tokens, temperature, extra_body)
        # Streaming avoids HTTP timeouts on long generations.
        with self.client.messages.stream(**params, extra_body=extra or None) as stream:
            message = stream.get_final_message()
        text = "".join(block.text for block in message.content if block.type == "text")
        thinking = "".join(block.thinking for block in message.content if block.type == "thinking")
        stop_details = getattr(message, "stop_details", None)
        return {
            "text": text,
            "reasoning": thinking or None,
            "finish_reason": message.stop_reason,
            "stop_details": stop_details.model_dump() if hasattr(stop_details, "model_dump") else stop_details,
            "usage": message.usage.model_dump(),
            "response_id": message.id,
            "served_model": message.model,
        }


def transport_errors() -> tuple[type[BaseException], ...]:
    return (anthropic.APIConnectionError, anthropic.RateLimitError, anthropic.InternalServerError)
