// Leaderboard data: pass@1 accuracy (%) as reported in the VeriContest paper.
// Columns: nl2spec (SpecGen), nl2code / spec2code / nlspec2code (CodeGen),
//          proof (ProofGen, spec+code->proof), e2e (end-to-end verified synthesis).
window.VC_LEADERBOARD = [
  { model: "GPT-5.5",           provider: "OpenAI",   nl2spec: 48.31, nl2code: 92.18, spec2code: 67.65, nlspec2code: 74.52, proof: 13.95, e2e: 5.29 },
  { model: "Claude Opus 4.7",   provider: "Anthropic", nl2spec: 20.82, nl2code: 90.17, spec2code: 67.76, nlspec2code: 72.30, proof: 12.68, e2e: 2.22 },
  { model: "Claude Sonnet 4.6", provider: "Anthropic", nl2spec: 13.11, nl2code: 88.37, spec2code: 74.31, nlspec2code: 75.59, proof: 13.21, e2e: 2.85 },
  { model: "Gemini 3.1 Pro",    provider: "Google",   nl2spec: 19.03, nl2code: 88.79, spec2code: 68.18, nlspec2code: 77.70, proof: 13.53, e2e: 2.64 },
  { model: "DeepSeek V4 Pro",   provider: "DeepSeek", nl2spec: 7.93,  nl2code: 87.00, spec2code: 62.68, nlspec2code: 67.44, proof: 5.60,  e2e: 1.06 },
  { model: "DeepSeek V4 Flash", provider: "DeepSeek", nl2spec: 4.77,  nl2code: 79.49, spec2code: 59.51, nlspec2code: 60.19, proof: 4.86,  e2e: 1.06 },
  { model: "GPT-5.4 mini",      provider: "OpenAI",   nl2spec: 2.36,  nl2code: 78.75, spec2code: 51.59, nlspec2code: 58.14, proof: 7.08,  e2e: 1.06 },
  { model: "Qwen 3.6",          provider: "Qwen",     nl2spec: 0.32,  nl2code: 77.91, spec2code: 41.44, nlspec2code: 48.94, proof: 4.86,  e2e: 0.21 },
  { model: "Gemini 3 Flash",    provider: "Google",   nl2spec: 14.59, nl2code: 49.15, spec2code: 31.92, nlspec2code: 34.99, proof: 6.34,  e2e: 0.95 },
  { model: "GLM-4.7-Flash",     provider: "Zhipu",    nl2spec: 1.48,  nl2code: 41.12, spec2code: 17.65, nlspec2code: 21.46, proof: 5.50,  e2e: 0.21 },
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

// Test-time scaling on proof generation (spec+code -> proof), pass@1 (%), k = 1..20.
// pass@k: best of k independent samples. repair@k: iterative repair of failed proofs.
window.VC_SCALING = {
  ks: Array.from({ length: 20 }, (_, i) => i + 1),
  models: [
    { tag: "qwen36", label: "Qwen3.6-27B", color: "#1f77b4" },
    { tag: "glm47", label: "GLM-4.7-Flash", color: "#d62728" },
  ],
  pass: {
    qwen36: [4.86, 6.45, 6.98, 7.08, 7.40, 7.51, 7.72, 7.72, 7.72, 8.03, 8.25, 8.25, 8.35, 8.35, 8.46, 8.46, 8.46, 8.56, 8.56, 8.67],
    glm47:  [5.50, 5.81, 5.92, 6.13, 6.34, 6.55, 6.66, 6.66, 6.77, 6.77, 6.77, 6.87, 6.98, 6.98, 7.08, 7.19, 7.19, 7.29, 7.29, 7.40],
  },
  repair: {
    qwen36: [7.08, 7.51, 7.93, 8.25, 8.77, 9.20, 9.30, 9.41, 9.62, 9.83, 10.15, 10.36, 10.68, 10.68, 10.89, 11.31, 11.31, 11.63, 11.84, 11.84],
    glm47:  [6.77, 6.98, 7.08, 7.08, 7.08, 7.08, 7.08, 7.08, 7.19, 7.19, 7.51, 7.51, 7.61, 7.61, 7.72, 7.72, 7.72, 7.72, 7.72, 7.72],
  },
};
