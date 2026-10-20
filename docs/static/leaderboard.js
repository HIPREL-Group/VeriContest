'use strict';

// Pure selection logic is also exercised by Node's built-in test runner.
// A full-split entry also appears in the LeetCode, Codeforces and Lite views, scored on that split,
// and links that split's trajectories when it has them.
function leaderboardSplitView(entry, split) {
  const scores = entry.split_scores;
  if (!scores) return entry.split === split ? entry : null;
  if (!Object.prototype.hasOwnProperty.call(scores, split)) return null;
  const traces = (entry.split_trajectory_urls || {})[split];
  return { ...entry, score: scores[split], problem_count: entry.split_problem_counts[split],
    submitted_problem_count: entry.problem_count, ...(traces ? { trajectory_url: traces } : {}) };
}

function selectLeaderboardEntries(entries, filters) {
  const group = entries.map((e) => leaderboardSplitView(e, filters.split)).filter((e) => e &&
    e.track === filters.track && e.task === filters.task && e.input_mode === filters.inputMode &&
    (!filters.protocol || e.protocol_id === filters.protocol || e.status !== 'evaluation_checked'));
  const ranked = group.filter((e) => e.rankable && e.status === 'evaluation_checked' &&
    Number.isFinite(e.score) && filters.protocol && e.protocol_id === filters.protocol)
    .sort((a, b) => b.score - a.score || a.system.localeCompare(b.system));
  const ranks = new Map();
  ranked.forEach((entry, i) => ranks.set(entry.id,
    i && entry.score === ranked[i - 1].score ? ranks.get(ranked[i - 1].id) : i + 1));
  const query = (filters.query || '').toLowerCase();
  return group.map((entry) => ({ ...entry, rank: ranks.get(entry.id) || null }))
    .filter((e) => [e.system, e.team, e.org || '', ...e.models, ...(e.model_names || [])].join(' ').toLowerCase().includes(query))
    .sort((a, b) => (a.rank ?? Infinity) - (b.rank ?? Infinity) || a.system.localeCompare(b.system) || a.id.localeCompare(b.id));
}

// Column sorting. Rows arrive in rank order, and the sort is stable, so ties keep it;
// missing values stay last in both directions.
const LEADERBOARD_SORT_KEYS = {
  'RANK': 'rank', 'AGENT': 'system', 'MODEL': 'models', 'PASS@1': 'score', 'TRAJS': 'trajs',
  'AVG. $': 'cost', 'ORG': 'org', 'DATE': 'date', 'RELEASE': 'release'
};
const LEADERBOARD_FIRST_DIRECTION = { score: 'desc', date: 'desc', trajs: 'asc', cost: 'asc' };

function leaderboardSortValue(entry, key) {
  switch (key) {
    case 'rank': return entry.rank;
    case 'system': return entry.system;
    case 'models': return (entry.model_names || entry.models || []).join(', ');
    case 'score': return Number.isFinite(entry.score) ? entry.score : null;
    case 'trajs': return entry.trajectory_url ? 0 : entry.trajectory_availability === 'private_by_arrangement' ? 1 : null;
    case 'cost': return Number.isFinite(entry.avg_cost_usd) ? entry.avg_cost_usd : null;
    case 'org': return entry.org || entry.team;
    case 'date': return entry.date || null;
    case 'release': return entry.benchmark_release || null;
    default: return null;
  }
}

function sortLeaderboardRows(rows, sort) {
  if (!sort || sort.key === 'rank' && sort.dir === 'asc') return rows.slice();
  const sign = sort.dir === 'desc' ? -1 : 1;
  return rows.slice().sort((a, b) => {
    const x = leaderboardSortValue(a, sort.key), y = leaderboardSortValue(b, sort.key);
    if (x === null || x === undefined) return y === null || y === undefined ? 0 : 1;
    if (y === null || y === undefined) return -1;
    const order = typeof x === 'number' && typeof y === 'number' ? x - y :
      String(x).localeCompare(String(y), undefined, { numeric: true, sensitivity: 'base' });
    return sign * order;
  });
}

function leaderboardSafeUrl(value) {
  try {
    const u = new URL(value);
    return u.protocol === 'https:' && !u.username && !u.password ? u.href : null;
  } catch (_) { return null; }
}

function leaderboardLogoSrc(value) {
  if (typeof value !== 'string') return null;
  return /^static\/logos\/[a-z0-9][a-z0-9_-]*\.(svg|png|webp)$/.test(value) ? `./${value}` : leaderboardSafeUrl(value);
}

async function initLeaderboard() {
  const body = document.getElementById('lbBody');
  if (!body) return;
  let columnCount = document.querySelectorAll('#lbTable thead th').length;
  const status = document.getElementById('lbSummary');
  const taskSelect = document.getElementById('lbTask');
  const splitSelect = document.getElementById('lbSplit');
  const protocolSelect = document.getElementById('lbProtocol');
  const search = document.getElementById('lbSearch');
  const trackButtons = Array.from(document.querySelectorAll('[data-lb-track]'));
  const benchButtons = Array.from(document.querySelectorAll('[data-lb-bench]'));
  const state = { bench: 'full', track: 'fixed_prompt', task: 'End2End', inputMode: 'nl', split: 'full', protocol: '', query: '',
    sort: { key: 'rank', dir: 'asc' } };
  const labels = { submitted: 'Submitted', automated_checks_complete: 'Automated checks complete', evaluation_checked: 'Evaluation checked' };
  let data;
  const node = (tag, content, className) => {
    const el = document.createElement(tag);
    if (content !== undefined) el.textContent = content;
    if (className) el.className = className;
    return el;
  };
  const link = (label, href) => {
    const safe = leaderboardSafeUrl(href);
    if (!safe) return node('span', label);
    const el = node('a', label);
    el.href = safe;
    el.rel = 'noopener noreferrer';
    return el;
  };
  try {
    const response = await fetch('./static/leaderboard.json');
    if (!response.ok) throw new Error(`HTTP ${response.status}`);
    data = await response.json();
    if (!Array.isArray(data.entries) || !Array.isArray(data.protocols) || !data.release) throw new Error('Invalid registry data');
  } catch (_) {
    status.textContent = 'Leaderboard data could not be loaded. Reload this page or browse submissions on GitHub.';
    body.replaceChildren();
    const row = node('tr');
    const cell = node('td'); cell.colSpan = columnCount;
    cell.append(link('Browse the submission registry', 'https://github.com/HIPREL-Group/VeriContest/tree/main/submissions'));
    row.append(cell); body.append(row);
    return;
  }
  const counts = { full: data.release.counts.full, lite: data.release.lite ? data.release.lite.count : null };
  benchButtons.forEach((b) => {
    const count = counts[b.dataset.lbBench];
    b.hidden = count === null;
    if (count !== null) b.querySelector('[data-lb-bench-count]').textContent = count.toLocaleString();
  });
  const hashBench = () => (window.location.hash === '#lite' && counts.lite !== null ? 'lite' : 'full');

  // VeriContest Lite is its own benchmark in the sidebar; the coverage menu splits the full one.
  function benchmark(bench) {
    state.bench = bench;
    benchButtons.forEach((b) => {
      const active = b.dataset.lbBench === bench;
      b.classList.toggle('is-current', active);
      if (active) b.setAttribute('aria-current', 'page'); else b.removeAttribute('aria-current');
    });
    const lite = state.bench === 'lite';
    state.split = lite ? 'lite' : splitSelect.value;
    document.getElementById('lbSplitControl').hidden = lite;
    document.querySelector('.lb-controls').classList.toggle('no-coverage', lite);
    document.getElementById('lbRelease').replaceChildren(
      document.createTextNode(lite ? 'VeriContest Lite · ' : 'VeriContest · '),
      node('strong', counts[state.bench].toLocaleString(), 'lb-count'),
      document.createTextNode(' problems')
    );
    const note = document.getElementById('lbBenchNote');
    if (lite) {
      note.replaceChildren(document.createTextNode(`A fixed ${counts.lite}-problem subset with the full benchmark's mix of sources, ` +
        'difficulty levels and proof sizes. Full-benchmark entries are also scored on it. '),
        Object.assign(node('a', 'How Lite is selected'), { href: './lite.html#selection' }));
    } else {
      note.textContent = `The full benchmark: ${data.release.counts.leetcode.toLocaleString()} LeetCode and ` +
        `${data.release.counts.codeforces.toLocaleString()} Codeforces problems.`;
    }
  }

  function settings() {
    const matches = data.protocols.filter((p) => p.task === state.task && p.input_mode === state.inputMode && p.track === state.track);
    const old = state.protocol;
    protocolSelect.replaceChildren();
    const all = node('option', matches.length ? 'All settings (no combined ranking)' : 'Evaluation setting pending');
    all.value = ''; protocolSelect.append(all);
    matches.forEach((p) => { const option = node('option', p.label || p.id); option.value = p.id; protocolSelect.append(option); });
    state.protocol = matches.some((p) => p.id === old) ? old : matches.length === 1 ? matches[0].id : '';
    protocolSelect.value = state.protocol;
    protocolSelect.disabled = !matches.length;
    document.getElementById('lbProtocolControl').hidden = matches.length < 2;
    document.querySelector('.lb-controls').classList.toggle('has-protocols', matches.length > 1);
  }
  function render() {
    const agentTrack = state.track === 'agent';
    const columns = ['RANK', ...(agentTrack ? ['AGENT'] : []), 'MODEL', 'PASS@1', 'TRAJS', ...(agentTrack ? ['AVG. $'] : []), 'ORG', 'DATE', 'RELEASE'];
    const titles = {
      'PASS@1': 'Official checked score; pending submissions have no score',
      'TRAJS': 'Execution trajectories: tool calls, repair steps, and candidate selection',
      'AVG. $': 'Submitter-reported average generation cost in USD per attempted problem, including failures and timeouts',
      'ORG': 'Organization; for Model-track entries, the developer of the model',
      'DATE': 'Submission date',
      'RELEASE': 'Benchmark release the entry was evaluated on'
    };
    const columnClasses = {
      'RANK': 'lb-col-rank', 'AGENT': 'lb-col-name', 'MODEL': agentTrack ? 'lb-col-models' : 'lb-col-name',
      'PASS@1': 'lb-col-score', 'TRAJS': 'lb-col-trajs', 'AVG. $': 'lb-col-cost', 'ORG': 'lb-col-org',
      'DATE': 'lb-col-date', 'RELEASE': 'lb-col-release'
    };
    if (!columns.some((label) => LEADERBOARD_SORT_KEYS[label] === state.sort.key)) state.sort = { key: 'rank', dir: 'asc' };
    document.querySelector('#lbTable thead tr').replaceChildren(...columns.map((label) => {
      const th = node('th'); th.scope = 'col';
      th.className = columnClasses[label];
      const key = LEADERBOARD_SORT_KEYS[label];
      const active = state.sort.key === key;
      const button = node('button', label, 'lb-sort');
      button.type = 'button';
      button.title = `${titles[label] ? titles[label] + '. ' : ''}Click to sort`;
      if (active) {
        th.setAttribute('aria-sort', state.sort.dir === 'asc' ? 'ascending' : 'descending');
        button.classList.add(state.sort.dir === 'asc' ? 'is-asc' : 'is-desc');
      }
      button.addEventListener('click', () => {
        state.sort = active ? { key, dir: state.sort.dir === 'asc' ? 'desc' : 'asc' } :
          { key, dir: LEADERBOARD_FIRST_DIRECTION[key] || 'asc' };
        render();
        const again = document.querySelector(`#lbTable thead th:nth-child(${columns.indexOf(label) + 1}) .lb-sort`);
        if (again) again.focus();
      });
      th.append(button);
      return th;
    }));
    columnCount = columns.length;
    document.getElementById('lbTable').classList.toggle('is-agent', agentTrack);
    const rows = sortLeaderboardRows(selectLeaderboardEntries(data.entries, state), state.sort);
    document.getElementById('lbTable').classList.toggle('is-empty', rows.length === 0);
    body.replaceChildren();
    status.textContent = rows.length ? '' :
      'No submissions in this view yet. Submissions are open.';
    status.hidden = !status.textContent;
    const settingNote = document.getElementById('lbSettingNote');
    settingNote.textContent = state.split === 'custom' ?
      'Custom subsets are partial evaluations and are not ranked.' : state.protocol ? '' :
      protocolSelect.disabled ? 'Official scores will appear after an evaluation protocol is published and the required reviews are complete.' :
      'Select an evaluation setting to compare ranks. Settings with different tests or evaluation rules are kept separate.';
    settingNote.hidden = !settingNote.textContent;
    if (!rows.length) {
      const row = node('tr'); const cell = node('td', 'Be the first to submit a system in this view.', 'lb-empty');
      cell.colSpan = columnCount; row.append(cell); body.append(row); return;
    }
    rows.forEach((entry, index) => {
      const row = node('tr', undefined, 'lb-row');
      row.append(node('td', entry.rank === null ? '—' : String(entry.rank), 'rank-cell'));
      const identity = node('td');
      const modelNames = (entry.model_names || entry.models).join(', ');
      const disclosure = node('div', undefined, 'lb-details');
      disclosure.id = `lbDetails${index}`; disclosure.hidden = true;
      const toggle = node('button', 'Details', 'lb-details-toggle');
      toggle.type = 'button';
      toggle.setAttribute('aria-expanded', 'false'); toggle.setAttribute('aria-controls', disclosure.id);
      toggle.addEventListener('click', () => {
        disclosure.hidden = !disclosure.hidden;
        toggle.setAttribute('aria-expanded', String(!disclosure.hidden));
      });
      const heading = node('div', undefined, 'lb-identity');
      heading.append(link(agentTrack ? entry.system : modelNames, entry.entry_url), toggle);
      identity.append(heading);
      row.append(identity);
      if (agentTrack) row.append(node('td', modelNames));
      const score = node('td', undefined, 'num lb-score');
      if (entry.score === null) {
        score.append(node('span', '—'), node('div', labels[entry.status] || entry.status, 'lb-secondary'));
      } else {
        const bar = node('div', undefined, 'lb-bar');
        const fill = node('span');
        fill.style.width = `${Math.min(100, Math.max(0, entry.score))}%`;
        bar.append(fill);
        score.append(node('span', `${entry.score.toFixed(2)}%`, 'lb-score-value'), bar);
      }
      row.append(score);
      const trajectories = node('td', undefined, 'lb-trajs');
      if (entry.trajectory_url) {
        const trajectoryLink = link('View', entry.trajectory_url);
        trajectoryLink.title = 'Execution trajectories (pinned)';
        trajectories.append(trajectoryLink);
      } else {
        trajectories.textContent = ({private_by_arrangement: 'Private', pending: 'Pending'})[entry.trajectory_availability] || '—';
        trajectories.title = 'See submission methodology for trajectory availability and redactions.';
      }
      row.append(trajectories);
      if (agentTrack) {
        const cost = node('td', Number.isFinite(entry.avg_cost_usd) ?
          (entry.avg_cost_usd > 0 && entry.avg_cost_usd < .01 ? '<$0.01' : `$${entry.avg_cost_usd.toFixed(2)}`) : '—', 'num lb-cost');
        cost.title = Number.isFinite(entry.avg_cost_usd) ?
          `Submitter-reported generation cost averaged over ${entry.cost_problem_count} attempted problems, including failures and timeouts.` : 'Cost not reported';
        row.append(cost);
      }
      const org = node('td', undefined, 'lb-org');
      const orgName = entry.org || entry.team;
      const logoSrc = leaderboardLogoSrc(entry.org_logo);
      if (logoSrc) {
        const logo = node('img', undefined, 'lb-org-logo');
        logo.src = logoSrc; logo.alt = orgName; logo.title = orgName; logo.loading = 'lazy';
        logo.addEventListener('error', () => logo.replaceWith(document.createTextNode(orgName)), { once: true });
        org.append(logo);
      } else org.textContent = orgName;
      row.append(org);
      const submitted = node('td', entry.date || '—', 'lb-date');
      submitted.title = 'Submission date'; row.append(submitted);
      const benchmarkRelease = entry.benchmark_release || data.release.id;
      const release = node('td', undefined, 'lb-release');
      const releaseTag = ((data.releases || [data.release]).find((r) => r.id === benchmarkRelease) || {}).git_tag;
      const releaseLink = link(benchmarkRelease, releaseTag ?
        `https://github.com/HIPREL-Group/VeriContest/releases/tag/${encodeURIComponent(releaseTag)}` : null);
      releaseLink.title = `Benchmark release ${benchmarkRelease}`;
      release.append(releaseLink); row.append(release);
      const progress = node('p');
      progress.append(node('span', labels[entry.status] || entry.status, `lb-status ${entry.status}`));
      if (entry.spec_review === 'pending') progress.append(node('div', 'Specification review pending', 'lb-secondary'));
      disclosure.append(progress);
      const submittedCount = entry.submitted_problem_count || entry.problem_count;
      const coverage = entry.split === state.split ? `${entry.problem_count} problems` :
        `${entry.problem_count} problems in this view, from a ${entry.split}-split submission of ${submittedCount}`;
      disclosure.append(node('p', `System: ${entry.system}. Organization: ${orgName}. Submitted by: ${entry.team}. Coverage: ${coverage}.`));
      disclosure.append(node('p', `Model checkpoints: ${entry.models.join(', ')}.`));
      const systemVersion = node('p', 'System version: ');
      systemVersion.append(link(entry.version, entry.release_url), document.createTextNode('.'));
      disclosure.append(systemVersion);
      disclosure.append(node('p', `Submitted ${entry.date}. Benchmark release: ${benchmarkRelease}. Setting: ${entry.protocol_id || 'pending'}.`));
      disclosure.append(node('p', `Artifacts: ${entry.artifact_origin === 'team_endpoint' ? 'team-initiated generation' : 'provided by submitter'}. Fresh-run scope: ${entry.rerun_count}/${submittedCount}. Checked scope: ${entry.checked_count}/${submittedCount}.`));
      const budget = entry.budget;
      if (Number.isFinite(entry.avg_cost_usd)) disclosure.append(node('p', `Reported generation cost: $${budget.total_cost_usd} across ${entry.cost_problem_count} attempted problems. ${budget.cost_notes || ''}`));
      disclosure.append(node('p', `Budget (${budget.scope}): ${budget.max_llm_calls ?? 'undeclared'} LLM calls, ${budget.max_repair_iterations ?? 'undeclared'} repair iterations, ${budget.max_wall_time_seconds ?? 'undeclared'} seconds. ${budget.notes}`));
      disclosure.append(node('p', 'Submitter-reported component checks (not final task scores):'));
      Object.entries(entry.component_counts).forEach(([key, values]) => disclosure.append(node('p', `${key}: ${Object.entries(values).map(([k, v]) => `${v} ${k}`).join(', ')}`)));
      const links = node('p'); links.append(link('Submission', entry.entry_url));
      if (entry.artifact_url) links.append(document.createTextNode(' · '), link('Artifacts', entry.artifact_url));
      else links.append(document.createTextNode(` · Artifacts: ${entry.artifact_availability.replaceAll('_', ' ')}`));
      if (entry.review_url) links.append(document.createTextNode(' · '), link('Review', entry.review_url));
      disclosure.append(links); identity.append(disclosure); body.append(row);
    });
  }
  benchButtons.forEach((button) => button.addEventListener('click', (event) => {
    event.preventDefault();
    window.history.replaceState(null, '', button.dataset.lbBench === 'lite' ? '#lite' : '#leaderboard');
    benchmark(button.dataset.lbBench); render();
  }));
  window.addEventListener('hashchange', () => { benchmark(hashBench()); render(); });
  trackButtons.forEach((button) => button.addEventListener('click', () => {
    state.track = button.dataset.lbTrack;
    trackButtons.forEach((b) => { const active = b === button; b.classList.toggle('is-active', active); b.setAttribute('aria-pressed', String(active)); });
    settings(); render();
  }));
  taskSelect.addEventListener('change', () => { [state.task, state.inputMode] = taskSelect.value.split(':'); settings(); render(); });
  splitSelect.addEventListener('change', () => { state.split = splitSelect.value; render(); });
  protocolSelect.addEventListener('change', () => { state.protocol = protocolSelect.value; render(); });
  search.addEventListener('input', () => { state.query = search.value.trim(); render(); });
  benchmark(hashBench()); settings(); render();
}

if (typeof module !== 'undefined') module.exports = { selectLeaderboardEntries, sortLeaderboardRows, leaderboardSafeUrl, leaderboardLogoSrc };
