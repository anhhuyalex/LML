/* Shared static statistics viewer. No network services or chart dependencies. */
"use strict";

(function () {
  function histogram(values, choice) {
    const frequencies = new Map();
    for (const value of Object.values(values)) {
      if (!Number.isSafeInteger(value) || value < 0) throw Error("Invalid statistic count");
      frequencies.set(value, (frequencies.get(value) || 0) + 1);
    }
    const maximum = Math.max(0, ...frequencies.keys());
    const bins = [{min: 0, max: 0, count: frequencies.get(0) || 0}];
    if (choice === "exact") {
      for (const value of [...frequencies.keys()].filter(v => v > 0).sort((a, b) => a - b)) {
        bins.push({min: value, max: value, count: frequencies.get(value)});
      }
    } else {
      if (![10, 20, 50].includes(Number(choice))) throw Error("Invalid number of bars");
      const width = Math.max(1, Math.ceil(maximum / (Number(choice) - 1)));
      for (let min = 1; min <= maximum; min += width) {
        bins.push({min, max: Math.min(maximum, min + width - 1), count: 0});
      }
      for (const [value, count] of frequencies) {
        if (value > 0) bins[1 + Math.floor((value - 1) / width)].count += count;
      }
    }
    return bins;
  }

  // The same binning function is exercised by Node's dependency-free tests.
  if (typeof module !== "undefined") module.exports = {histogram};
  if (typeof document === "undefined") return;

  const $ = id => document.getElementById(id);
  const label = bin => bin.min === bin.max ? String(bin.min) : `${bin.min}–${bin.max}`;
  const element = (tag, text, className) => {
    const node = document.createElement(tag);
    if (text !== undefined) node.textContent = text;
    if (className) node.className = className;
    return node;
  };
  let bundle, state, metric;

  function readState() {
    const params = new URLSearchParams(location.search);
    const selected = bundle.metrics.find(m => m.id === params.get("metric")) || bundle.metrics[0];
    const bins = ["10", "20", "50", "exact"].includes(params.get("bins")) ? params.get("bins") : "20";
    const available = histogram(selected.values, bins);
    const range = params.has("min") && params.has("max") ? available.find(b =>
      b.min === Number(params.get("min")) && b.max === Number(params.get("max"))) : null;
    return {metric: selected.id, bins, range: range || null,
      query: params.get("q") || "", page: Math.max(1, Number(params.get("page")) || 1)};
  }

  function remember(replace) {
    const url = new URL(location.href);
    url.search = "";
    url.hash = "stats";
    url.searchParams.set("metric", state.metric);
    url.searchParams.set("bins", state.bins);
    if (state.range) {
      url.searchParams.set("min", state.range.min);
      url.searchParams.set("max", state.range.max);
    }
    if (state.query) url.searchParams.set("q", state.query);
    if (state.page > 1) url.searchParams.set("page", state.page);
    history[replace ? "replaceState" : "pushState"](null, "", url);
  }

  function selectRange(bin) {
    state.range = {min: bin.min, max: bin.max};
    state.page = 1;
    draw(true);
    remember(false);
    $("stats-selection").focus({preventScroll: true});
    $("stats-selection").scrollIntoView({block: "nearest", behavior: "smooth"});
  }

  function drawChart() {
    const bins = histogram(metric.values, state.bins);
    const peak = Math.max(1, ...bins.map(bin => bin.count));
    const chart = $("stats-chart");
    const bars = element("div", undefined, "stats-bars");
    bars.style.gridTemplateColumns = `repeat(${bins.length}, minmax(46px, 1fr))`;
    const table = $("stats-counts").tBodies[0];
    table.replaceChildren();
    for (const bin of bins) {
      const button = element("button", undefined, "stats-bar");
      button.type = "button";
      button.dataset.min = bin.min;
      button.dataset.max = bin.max;
      button.dataset.count = bin.count;
      button.setAttribute("aria-label", `${label(bin)} uses: ${bin.count} declarations`);
      button.setAttribute("aria-pressed", String(!!state.range &&
        state.range.min === bin.min && state.range.max === bin.max));
      button.disabled = bin.count === 0;
      button.title = button.getAttribute("aria-label");
      button.append(element("span", bin.count, "stats-bar-count"));
      const column = element("span", undefined, "stats-column");
      const fill = element("span", undefined, "stats-fill");
      fill.style.height = `${100 * bin.count / peak}%`;
      column.append(fill);
      button.append(column, element("span", label(bin), "stats-bar-label"));
      button.onclick = () => selectRange(bin);
      bars.append(button);
      const row = element("tr");
      const range = element("th");
      range.scope = "row";
      const choose = element("button", label(bin));
      choose.type = "button";
      choose.disabled = bin.count === 0;
      choose.onclick = () => selectRange(bin);
      range.append(choose);
      row.append(range, element("td", bin.count));
      table.append(row);
    }
    chart.replaceChildren(bars);
  }

  function drawRows() {
    const needle = state.query.toLocaleLowerCase();
    const rows = bundle.declarations.filter(d => {
      const count = metric.values[d.id];
      return (!state.range || (count >= state.range.min && count <= state.range.max)) &&
        (!needle || `${d.name} ${d.module}`.toLocaleLowerCase().includes(needle));
    }).sort((a, b) => metric.values[b.id] - metric.values[a.id] || a.name.localeCompare(b.name));
    const pages = Math.max(1, Math.ceil(rows.length / 50));
    state.page = Math.min(pages, Math.max(1, Math.floor(state.page)));
    const start = (state.page - 1) * 50;
    const table = $("stats-declarations").tBodies[0];
    table.replaceChildren();
    for (const declaration of rows.slice(start, start + 50)) {
      const row = element("tr");
      row.dataset.name = declaration.name;
      row.append(element("td", declaration.name), element("td", declaration.kind),
        element("td", declaration.module), element("td", metric.values[declaration.id]));
      const links = element("td", undefined, "stats-links");
      for (const [text, key] of [["Documentation", "documentation"], ["Source", "source"]]) {
        const link = element("a", text);
        link.href = declaration[key];
        links.append(link);
      }
      row.append(links);
      table.append(row);
    }
    $("stats-selection").textContent = state.range ? `Declarations with ${label(state.range)} uses` : "All declarations";
    $("stats-count").textContent = rows.length ?
      `${rows.length} declarations. Showing ${start + 1}–${Math.min(start + 50, rows.length)}.` :
      "No declarations match this selection.";
    $("stats-page").textContent = `Page ${state.page} of ${pages}`;
    $("stats-prev").disabled = state.page <= 1;
    $("stats-next").disabled = state.page >= pages;
  }

  function draw(chart) {
    metric = bundle.metrics.find(m => m.id === state.metric);
    $("stats-metric").value = state.metric;
    $("stats-bins").value = state.bins;
    $("stats-search").value = state.query;
    $("stats-chart-title").textContent = metric.title;
    $("stats-explanation").textContent = metric.explanation;
    $("stats-notes").textContent = metric.notes || "";
    $("stats-x-label").textContent = metric.x_label;
    $("stats-y-label").textContent = metric.y_label;
    if (chart) drawChart();
    drawRows();
  }

  async function start() {
    const response = await fetch(new URL("stats/data.json", document.baseURI));
    if (!response.ok) throw Error(`Statistics download failed (${response.status})`);
    bundle = await response.json();
    if (bundle.schema_version !== 1 || !bundle.metrics.length ||
        bundle.metrics.some(m => m.display !== "histogram" || m.subject !== "declaration")) {
      throw Error("Unsupported statistics format");
    }
    const version = $("stats-version");
    version.append(document.createTextNode("Repository version "));
    const commit = element("a", bundle.build.revision.slice(0, 12));
    commit.href = `${bundle.build.repository}/commit/${bundle.build.revision}`;
    version.append(commit, document.createTextNode(`. Lean ${bundle.build.lean.split(":v").pop()}.`));
    $("stats-population").textContent = `${bundle.population.included} named public declarations included; ` +
      `${bundle.population.collected - bundle.population.included} other collected declarations excluded.`;
    for (const item of bundle.metrics) {
      const option = element("option", item.title);
      option.value = item.id;
      $("stats-metric").append(option);
    }
    state = readState();
    draw(true);
    remember(true);
    $("stats-bins").onchange = event => {
      state.bins = event.target.value;
      state.range = null;
      state.page = 1;
      draw(true);
      remember(false);
    };
    $("stats-metric").onchange = event => {
      state.metric = event.target.value;
      state.range = null;
      state.page = 1;
      draw(true);
      remember(false);
    };
    $("stats-search").oninput = event => {
      state.query = event.target.value;
      state.page = 1;
      draw(false);
      remember(true);
    };
    $("stats-clear").onclick = () => {
      state.range = null;
      state.query = "";
      state.page = 1;
      draw(true);
      remember(false);
    };
    for (const [id, step] of [["stats-prev", -1], ["stats-next", 1]]) {
      $(id).onclick = () => { state.page += step; draw(false); remember(false); };
    }
    window.addEventListener("popstate", () => { state = readState(); draw(true); });
    document.documentElement.dataset.statsReady = "true";
  }

  start().catch(error => {
    $("stats-error").hidden = false;
    $("stats-error").textContent = `Unable to load statistics: ${error.message}`;
    console.error(error);
  });
})();
