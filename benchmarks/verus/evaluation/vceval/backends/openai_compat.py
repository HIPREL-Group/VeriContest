"""OpenAI-compatible backends: Chat Completions (vLLM, DeepSeek, Qwen, Gemini's
OpenAI endpoint, ...) and the OpenAI Responses API."""
from __future__ import annotations

import openai
from ..request_settings import request_parameters


class ChatBackend:
    name = "openai-chat"

    def __init__(self, model: str, max_retries: int, base_url: str | None = None):
        self.model = model
        self.client = openai.OpenAI(max_retries=max_retries, base_url=base_url, timeout=3600)

    def complete(self, prompt: str, max_tokens: int | None, temperature: float | None, extra_body: dict) -> dict:
        params, extra = request_parameters(self.name, self.model, prompt, max_tokens, temperature, extra_body)
        resp = self.client.chat.completions.create(**params, extra_body=extra or None)
        choice = resp.choices[0]
        return {
            "text": choice.message.content or "",
            "reasoning": getattr(choice.message, "reasoning_content", None),
            "finish_reason": choice.finish_reason,
            "usage": resp.usage.model_dump() if resp.usage else None,
            "response_id": resp.id,
            "served_model": resp.model,
        }


class ResponsesBackend:
    name = "openai-responses"

    def __init__(self, model: str, max_retries: int, base_url: str | None = None):
        self.model = model
        self.client = openai.OpenAI(max_retries=max_retries, base_url=base_url, timeout=3600)

    def complete(self, prompt: str, max_tokens: int | None, temperature: float | None, extra_body: dict) -> dict:
        params, extra = request_parameters(self.name, self.model, prompt, max_tokens, temperature, extra_body)
        resp = self.client.responses.create(**params, extra_body=extra or None)
        incomplete = getattr(resp, "incomplete_details", None)
        return {
            "text": resp.output_text or "",
            "reasoning": None,
            "finish_reason": resp.status if not incomplete else f"incomplete:{incomplete.reason}",
            "usage": resp.usage.model_dump() if resp.usage else None,
            "response_id": resp.id,
            "served_model": resp.model,
        }


def transport_errors() -> tuple[type[BaseException], ...]:
    return (openai.APIConnectionError, openai.RateLimitError, openai.InternalServerError)
