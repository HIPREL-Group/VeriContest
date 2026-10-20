// Model-track baselines on VeriContest v2026.10.1 (1,006 problems), pass@1 (%); the same results as the leaderboard.
// Columns: nl2spec (SpecGen), nl2code / spec2code / nlspec2code (CodeGen),
//          proof (ProofGen, spec+code->proof), e2e (end-to-end verified synthesis).
window.VC_RESULTS = [
  { model: "GPT-5.5",           provider: "OpenAI",    nl2spec: 57.16, nl2code: 97.51, spec2code: 77.44, nlspec2code: 84.49, proof: 13.82, e2e: 6.76 },
  { model: "Gemini 3.1 Pro",    provider: "Google",    nl2spec: 22.56, nl2code: 94.14, spec2code: 80.62, nlspec2code: 89.86, proof: 12.92, e2e: 3.68 },
  { model: "Claude Opus 4.7",   provider: "Anthropic", nl2spec: 27.24, nl2code: 95.43, spec2code: 77.24, nlspec2code: 80.62, proof: 12.52, e2e: 3.58 },
  { model: "Claude Sonnet 4.6", provider: "Anthropic", nl2spec: 17.30, nl2code: 93.84, spec2code: 82.01, nlspec2code: 83.80, proof: 13.52, e2e: 3.48 },
  { model: "GPT-5.4 mini",      provider: "OpenAI",    nl2spec: 7.85,  nl2code: 83.90, spec2code: 54.57, nlspec2code: 63.02, proof: 6.36,  e2e: 1.49 },
  { model: "DeepSeek V4 Pro",   provider: "DeepSeek",  nl2spec: 12.13, nl2code: 92.05, spec2code: 66.80, nlspec2code: 73.06, proof: 5.47,  e2e: 1.29 },
  { model: "Gemini 3 Flash",    provider: "Google",    nl2spec: 22.66, nl2code: 53.08, spec2code: 32.50, nlspec2code: 36.58, proof: 6.16,  e2e: 1.29 },
  { model: "DeepSeek V4 Flash", provider: "DeepSeek",  nl2spec: 9.74,  nl2code: 82.21, spec2code: 64.31, nlspec2code: 64.51, proof: 6.36,  e2e: 1.19 },
  { model: "GLM-4.7-Flash",     provider: "Zhipu",     nl2spec: 3.68,  nl2code: 43.34, spec2code: 17.10, nlspec2code: 22.17, proof: 5.27,  e2e: 0.70 },
  { model: "Qwen3.6-27B",       provider: "Qwen",      nl2spec: 0.40,  nl2code: 82.50, spec2code: 43.94, nlspec2code: 51.59, proof: 4.57,  e2e: 0.20 },
];

// The four headline evaluation tasks used by the capability-gap chart.
window.VC_GAP_TASKS = [
  { key: "nl2code", label: "Code\n(nl→code)" },
  { key: "nl2spec", label: "Spec\n(nl→spec)" },
  { key: "proof",   label: "Proof\n(spec+code→proof)" },
  { key: "e2e",     label: "End-to-End" },
];

window.VC_PROVIDER_COLORS = {
  OpenAI:   "#10a37f",
  Anthropic:"#d97757",
  Google:   "#4285f4",
  DeepSeek: "#4d6bfe",
  Qwen:     "#a24bf0",
  Zhipu:    "#2f6df6",
};

// Test-time scaling on proof generation (spec+code -> proof), accuracy (%), k = 1..20.
// pass@k: best of k independent samples. repair@k: iterative repair of failed proofs.
window.VC_SCALING = {
  ks: Array.from({ length: 20 }, (_, i) => i + 1),
  models: [
    { tag: "qwen36", label: "Qwen3.6-27B", color: "#1f77b4" },
    { tag: "glm47", label: "GLM-4.7-Flash", color: "#d62728" },
  ],
  pass: {
    qwen36: [4.57, 5.96, 6.46, 6.56, 6.86, 6.86, 7.16, 7.16, 7.16, 7.46, 7.65, 7.65, 7.75, 7.75, 7.85, 7.85, 7.85, 7.95, 7.95, 7.95],
    glm47:  [5.27, 5.57, 5.77, 5.96, 6.06, 6.26, 6.36, 6.36, 6.36, 6.36, 6.36, 6.46, 6.56, 6.56, 6.66, 6.76, 6.76, 6.86, 6.86, 6.86],
  },
  repair: {
    qwen36: [7.08, 7.51, 7.93, 8.25, 8.77, 9.20, 9.30, 9.41, 9.62, 9.83, 10.15, 10.36, 10.68, 10.68, 10.89, 11.31, 11.31, 11.63, 11.84, 11.84],
    glm47:  [6.77, 6.98, 7.08, 7.08, 7.08, 7.08, 7.08, 7.08, 7.19, 7.19, 7.51, 7.51, 7.61, 7.61, 7.72, 7.72, 7.72, 7.72, 7.72, 7.72],
  },
};
