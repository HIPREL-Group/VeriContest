'use strict';

document.addEventListener('DOMContentLoaded', () => {
  initNav();
  initReveal();
  initGapChart();
  initScalingCharts();
  initCompositionChart();
  initExplorer();
  initLeaderboard();
  initCopyBibtex();
});

/* ------------------------------------------------------------------ */
/* Navigation: burger + active-section highlight                       */
/* ------------------------------------------------------------------ */
function initNav() {
  const burger = document.querySelector('.navbar-burger');
  const menu = document.getElementById('navMenu');
  if (burger && menu) {
    burger.addEventListener('click', () => {
      burger.classList.toggle('is-active');
      menu.classList.toggle('is-active');
    });
    menu.querySelectorAll('a').forEach((a) =>
      a.addEventListener('click', () => {
        burger.classList.remove('is-active');
        menu.classList.remove('is-active');
      })
    );
  }

  const links = [...document.querySelectorAll('.nav-link')];
  const sections = links
    .map((l) => document.querySelector(l.getAttribute('href')))
    .filter(Boolean);
  const spy = new IntersectionObserver(
    (entries) => {
      entries.forEach((e) => {
        if (e.isIntersecting) {
          const id = '#' + e.target.id;
          links.forEach((l) =>
            l.classList.toggle('is-current', l.getAttribute('href') === id)
          );
        }
      });
    },
    { rootMargin: '-45% 0px -50% 0px' }
  );
  sections.forEach((s) => spy.observe(s));
}

/* ------------------------------------------------------------------ */
/* Reveal-on-scroll                                                    */
/* ------------------------------------------------------------------ */
function initReveal() {
  const els = document.querySelectorAll('.reveal');
  const io = new IntersectionObserver(
    (entries) => {
      entries.forEach((e) => {
        if (e.isIntersecting) {
          e.target.classList.add('is-visible');
          io.unobserve(e.target);
        }
      });
    },
    { threshold: 0.12 }
  );
  els.forEach((el) => io.observe(el));
}

/* ------------------------------------------------------------------ */
/* Capability-gap chart                                                */
/* ------------------------------------------------------------------ */
function initGapChart() {
  const canvas = document.getElementById('gapChart');
  const select = document.getElementById('gapModel');
  const compare = document.getElementById('gapCompare');
  if (!canvas || !window.Chart || !window.VC_LEADERBOARD) return;

  const data = window.VC_LEADERBOARD;
  const tasks = window.VC_GAP_TASKS;
  data.forEach((m, i) => {
    const o = document.createElement('option');
    o.value = i;
    o.textContent = m.model;
    select.appendChild(o);
  });

  const bestPerTask = tasks.map((t) =>
    Math.max(...data.map((m) => m[t.key]))
  );

  const labels = tasks.map((t) => t.label.split('\n'));
  const accent = '#b5121b';

  const chart = new Chart(canvas, {
    type: 'bar',
    data: {
      labels,
      datasets: [
        {
          label: data[0].model,
          data: tasks.map((t) => data[0][t.key]),
          backgroundColor: accent,
          borderRadius: 6,
          categoryPercentage: 0.6,
          barPercentage: 0.8,
        },
      ],
    },
    options: {
      responsive: true,
      maintainAspectRatio: true,
      aspectRatio: 2.4,
      plugins: {
        legend: { display: false },
        tooltip: {
          callbacks: { label: (c) => `${c.parsed.y.toFixed(2)}%` },
        },
      },
      scales: {
        y: {
          beginAtZero: true,
          max: 100,
          ticks: { callback: (v) => v + '%' },
          grid: { color: '#eee' },
        },
        x: { grid: { display: false } },
      },
    },
  });

  function render() {
    const m = data[+select.value];
    chart.data.datasets = [
      {
        label: m.model,
        data: tasks.map((t) => m[t.key]),
        backgroundColor: accent,
        borderRadius: 6,
        categoryPercentage: 0.6,
        barPercentage: compare.checked ? 0.9 : 0.8,
      },
    ];
    if (compare.checked) {
      chart.data.datasets.push({
        label: 'Best-in-class',
        data: bestPerTask,
        backgroundColor: 'rgba(30,30,30,0.15)',
        borderRadius: 6,
        categoryPercentage: 0.6,
        barPercentage: 0.9,
      });
    }
    chart.options.plugins.legend.display = compare.checked;
    chart.update();
  }
  select.addEventListener('change', render);
  compare.addEventListener('change', render);
}

/* ------------------------------------------------------------------ */
/* Scaling charts: pass@k (sampling) and repair@k (proof repair)       */
/* ------------------------------------------------------------------ */
function initScalingCharts() {
  const S = window.VC_SCALING;
  if (!S || !window.Chart) return;

  const makeChart = (canvasId, seriesByTag) => {
    const canvas = document.getElementById(canvasId);
    if (!canvas) return;
    const datasets = S.models.map((m) => ({
      label: m.label,
      data: seriesByTag[m.tag],
      borderColor: m.color,
      backgroundColor: m.color,
      pointBackgroundColor: m.color,
      borderWidth: 2,
      pointRadius: 2.5,
      pointHoverRadius: 4,
      tension: 0.25,
    }));
    new Chart(canvas, {
      type: 'line',
      data: { labels: S.ks, datasets },
      options: {
        responsive: true,
        maintainAspectRatio: true,
        aspectRatio: 1.5,
        interaction: { mode: 'index', intersect: false },
        plugins: {
          legend: { position: 'top', labels: { boxWidth: 14, usePointStyle: true } },
          tooltip: { callbacks: { label: (c) => `${c.dataset.label}: ${c.parsed.y.toFixed(2)}%` } },
        },
        scales: {
          x: { title: { display: true, text: 'k' }, grid: { display: false } },
          y: { ticks: { callback: (v) => v + '%' }, grid: { color: '#eee' } },
        },
      },
    });
  };

  makeChart('passChart', S.pass);
  makeChart('repairChart', S.repair);
}

/* ------------------------------------------------------------------ */
/* Dataset composition donut                                           */
/* ------------------------------------------------------------------ */
function initCompositionChart() {
  const canvas = document.getElementById('compChart');
  if (!canvas || !window.Chart) return;
  new Chart(canvas, {
    type: 'doughnut',
    data: {
      labels: ['LeetCode (690)', 'Codeforces (256)', 'Extended (61)'],
      datasets: [
        {
          data: [690, 256, 61],
          backgroundColor: ['#b5121b', '#e08a2e', '#c9c9d1'],
          borderWidth: 2,
          borderColor: '#fff',
        },
      ],
    },
    options: {
      responsive: true,
      maintainAspectRatio: true,
      aspectRatio: 1.15,
      cutout: '58%',
      plugins: {
        legend: { position: 'bottom', labels: { padding: 14 } },
      },
    },
  });
}

/* ------------------------------------------------------------------ */
/* Problem explorer                                                    */
/* ------------------------------------------------------------------ */
function initExplorer() {
  const listEl = document.getElementById('problemList');
  const detailEl = document.getElementById('problemDetail');
  if (!listEl) return;

  const state = { source: 'all', all: [], selected: null };

  const levelBadge = (p) =>
    p.levelKind === 'rating'
      ? `<span class="lvl-badge rating-badge">Rating ${escapeHtml(p.level)}</span>`
      : `<span class="lvl-badge diff-${p.level}">${escapeHtml(p.level)}</span>`;

  fetch('./static/problems.json')
    .then((r) => r.json())
    .then((problems) => {
      state.all = problems;
      renderList();
      if (problems.length) select(problems[0]);
    })
    .catch(() => {
      listEl.innerHTML =
        '<p class="has-text-grey p-4">Could not load problems.json.</p>';
    });

  document.querySelectorAll('.explorer-controls .filter-chips').forEach((group) => {
    const dim = group.dataset.filter;
    group.addEventListener('click', (e) => {
      const chip = e.target.closest('.chip');
      if (!chip) return;
      group.querySelectorAll('.chip').forEach((c) => c.classList.remove('is-active'));
      chip.classList.add('is-active');
      state[dim] = chip.dataset.val;
      renderList();
    });
  });

  function filtered() {
    return state.all.filter(
      (p) => state.source === 'all' || p.source === state.source
    );
  }

  function renderList() {
    const items = filtered();
    if (!items.length) {
      listEl.innerHTML = '<p class="has-text-grey p-4">No matching problems.</p>';
      return;
    }
    listEl.innerHTML = items
      .map(
        (p) => `
      <div class="problem-item ${state.selected && state.selected.id === p.id ? 'is-selected' : ''}" data-id="${p.id}">
        <div class="pi-head">
          <span class="pi-title">${escapeHtml(p.title)}</span>
          ${levelBadge(p)}
        </div>
        <div class="pi-meta">
          <span class="src-badge src-${p.source}">${p.source}</span>
          <span class="pi-id">#${escapeHtml(p.displayId)}</span>
          ${p.tags.slice(0, 3).map((t) => `<span class="pi-tag">${escapeHtml(t)}</span>`).join('')}
        </div>
      </div>`
      )
      .join('');
    listEl.querySelectorAll('.problem-item').forEach((el) =>
      el.addEventListener('click', () => {
        const p = state.all.find((x) => x.id === el.dataset.id);
        if (p) select(p);
      })
    );
  }

  function select(p) {
    state.selected = p;
    listEl.querySelectorAll('.problem-item').forEach((el) =>
      el.classList.toggle('is-selected', el.dataset.id === p.id)
    );
    renderDetail(p);
  }

  function renderDetail(p) {
    const descHtml = window.marked ? marked.parse(p.description) : `<pre>${escapeHtml(p.description)}</pre>`;
    detailEl.innerHTML = `
      <div class="detail-head">
        <div>
          <h3 class="detail-title">${escapeHtml(p.title)}</h3>
          <div class="detail-sub">
            <span class="src-badge src-${p.source}">${p.source}</span>
            ${levelBadge(p)}
            <a class="prob-link" href="${escapeHtml(p.url)}" target="_blank" rel="noopener">
              ${p.source} #${escapeHtml(p.displayId)}
              <i class="fas fa-arrow-up-right-from-square"></i>
            </a>
            <span class="detail-meta">${escapeHtml(p.meta || '')}</span>
          </div>
        </div>
      </div>
      <div class="tabs is-small detail-tabs">
        <ul>
          <li class="is-active" data-tab="d-desc"><a>Description</a></li>
          <li data-tab="d-spec"><a>Specification</a></li>
          <li data-tab="d-code"><a>Code</a></li>
          <li data-tab="d-proof"><a>Verus Proof</a></li>
        </ul>
      </div>
      <div id="d-desc" class="detail-panel content">${descHtml}</div>
      <div id="d-spec" class="detail-panel is-hidden"><pre><code class="language-rust">${escapeHtml(p.spec)}</code></pre></div>
      <div id="d-code" class="detail-panel is-hidden"><pre><code class="language-rust">${escapeHtml(p.code)}</code></pre></div>
      <div id="d-proof" class="detail-panel is-hidden"><pre><code class="language-rust">${escapeHtml(p.proof)}</code></pre></div>
    `;
    detailEl.querySelectorAll('.detail-tabs li').forEach((tab) =>
      tab.addEventListener('click', () => {
        detailEl.querySelectorAll('.detail-tabs li').forEach((t) => t.classList.remove('is-active'));
        tab.classList.add('is-active');
        const target = tab.dataset.tab;
        detailEl.querySelectorAll('.detail-panel').forEach((pan) =>
          pan.classList.toggle('is-hidden', pan.id !== target)
        );
        highlightIn(detailEl);
      })
    );
    highlightIn(detailEl);
  }
}

/* ------------------------------------------------------------------ */
/* Leaderboard: sort + provider filter + search                        */
/* ------------------------------------------------------------------ */
function initLeaderboard() {
  const body = document.getElementById('lbBody');
  const table = document.getElementById('lbTable');
  const search = document.getElementById('lbSearch');
  const provWrap = document.getElementById('lbProviders');
  if (!body || !window.VC_LEADERBOARD) return;

  const rows = window.VC_LEADERBOARD;
  const cols = ['nl2spec', 'nl2code', 'spec2code', 'nlspec2code', 'proof', 'e2e'];
  const best = {};
  cols.forEach((c) => (best[c] = Math.max(...rows.map((r) => r[c]))));

  const state = { key: 'nl2code', dir: -1, provider: 'all', q: '' };

  // provider chips
  const providers = ['all', ...new Set(rows.map((r) => r.provider))];
  provWrap.innerHTML = providers
    .map(
      (p) =>
        `<span class="chip ${p === 'all' ? 'is-active' : ''}" data-val="${p}">${p === 'all' ? 'All' : p}</span>`
    )
    .join('');
  provWrap.addEventListener('click', (e) => {
    const chip = e.target.closest('.chip');
    if (!chip) return;
    provWrap.querySelectorAll('.chip').forEach((c) => c.classList.remove('is-active'));
    chip.classList.add('is-active');
    state.provider = chip.dataset.val;
    render();
  });

  search.addEventListener('input', () => {
    state.q = search.value.trim().toLowerCase();
    render();
  });

  table.querySelectorAll('th.sortable').forEach((th) => {
    th.addEventListener('click', () => {
      const key = th.dataset.key;
      if (state.key === key) state.dir *= -1;
      else {
        state.key = key;
        state.dir = key === 'model' ? 1 : -1;
      }
      render();
    });
  });

  function render() {
    // sort indicators
    table.querySelectorAll('th.sortable').forEach((th) => {
      const ic = th.querySelector('.sort-ic');
      if (!ic) return;
      if (th.dataset.key === state.key) {
        ic.className = 'fas sort-ic ' + (state.dir === 1 ? 'fa-sort-up' : 'fa-sort-down') + ' is-active-sort';
      } else {
        ic.className = 'fas fa-sort sort-ic';
      }
    });

    let view = rows.filter((r) => {
      if (state.provider !== 'all' && r.provider !== state.provider) return false;
      if (state.q && !r.model.toLowerCase().includes(state.q)) return false;
      return true;
    });
    view = view.slice().sort((a, b) => {
      if (state.key === 'model') return state.dir * a.model.localeCompare(b.model);
      return state.dir * (a[state.key] - b[state.key]);
    });

    const medals = ['🥇', '🥈', '🥉'];
    const colorOf = (p) =>
      (window.VC_PROVIDER_COLORS && window.VC_PROVIDER_COLORS[p]) || '#888';
    // columns that begin a task group get a vertical separator
    const sep = new Set(['nl2spec', 'nl2code', 'proof', 'e2e']);

    body.innerHTML = view
      .map((r, i) => {
        const color = colorOf(r.provider);
        const rankCell =
          i < 3
            ? `<span class="medal">${medals[i]}</span>`
            : `<span class="rank-num">${i + 1}</span>`;
        const cell = (c) => {
          const isBest = r[c] === best[c];
          const cls = ['num', isBest ? 'is-best' : '', sep.has(c) ? 'col-sep' : '']
            .filter(Boolean)
            .join(' ');
          return `<td class="${cls}"><span class="v">${r[c].toFixed(2)}</span></td>`;
        };
        return `<tr class="lb-row ${i === 0 ? 'is-champion' : ''}">
          <td class="rank-cell">${rankCell}</td>
          <td class="model-cell col-sep">
            <span class="prov-avatar" style="background:${color}">${escapeHtml(r.provider[0])}</span>
            <span class="model-info">
              <span class="model-name">${escapeHtml(r.model)}</span>
              <span class="model-prov">${escapeHtml(r.provider)}</span>
            </span>
          </td>
          ${cols.map(cell).join('')}
        </tr>`;
      })
      .join('');
    if (!view.length) {
      body.innerHTML =
        '<tr><td colspan="8" class="has-text-centered has-text-grey p-4">No models match.</td></tr>';
    }
  }
  render();
}

/* ------------------------------------------------------------------ */
/* Copy BibTeX                                                         */
/* ------------------------------------------------------------------ */
function initCopyBibtex() {
  const btn = document.getElementById('copyBib');
  const pre = document.getElementById('bibtex');
  if (!btn || !pre) return;
  btn.addEventListener('click', () => {
    navigator.clipboard.writeText(pre.innerText.trim()).then(() => {
      btn.querySelector('span:last-child').textContent = 'Copied!';
      btn.classList.add('is-success');
      setTimeout(() => {
        btn.querySelector('span:last-child').textContent = 'Copy';
        btn.classList.remove('is-success');
      }, 1600);
    });
  });
}

/* ------------------------------------------------------------------ */
/* helpers                                                             */
/* ------------------------------------------------------------------ */
function highlightIn(root) {
  if (!window.hljs) return;
  // only highlight the Rust artifact panels; leave description example blocks plain
  root
    .querySelectorAll('pre code.language-rust:not(.hljs)')
    .forEach((el) => hljs.highlightElement(el));
}

function escapeHtml(s) {
  return String(s)
    .replace(/&/g, '&amp;')
    .replace(/</g, '&lt;')
    .replace(/>/g, '&gt;');
}
