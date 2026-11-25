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

  const inRange = (value, bin) => value >= bin.min && (bin.max === null || value <= bin.max);
  function timingHistogram(values) {
    const ends = [100, 500, 1000, 5000, 10000, 50000];
    const bins = ends.map((end, i) => ({min: ends[i - 1] || 0, max: end - 1, count: 0}));
    bins.push({min: ends.at(-1), max: null, count: 0});
    for (const value of Object.values(values)) {
      if (!Number.isSafeInteger(value) || value < 0) throw Error("Invalid timing");
      bins.find(bin => inRange(value, bin)).count++;
    }
    return bins;
  }
  // The same binning functions are exercised by Node's dependency-free tests.
  if (typeof module !== "undefined") module.exports = {histogram, timingHistogram};
  if (typeof document === "undefined") return;

  const $ = id => document.getElementById(id);
  const label = bin => bin.min === bin.max ? String(bin.min) : `${bin.min}–${bin.max}`;
  const isTiming = metric => metric.unit === "tenth_ms";
  const metricBins = (metric, choice) => isTiming(metric) ? timingHistogram(metric.values) :
    histogram(metric.values, choice);
  const timeLabel = tenths => tenths >= 10000 ? `${tenths / 10000} s` : `${tenths / 10} ms`;
  function rangeLabel(bin) {
    if (!isTiming(metric)) return label(bin) + " uses";
    if (bin.max === null) return timeLabel(bin.min) + " or longer";
    if (bin.min === 0) return "Under " + timeLabel(bin.max + 1);
    return `${timeLabel(bin.min)} to under ${timeLabel(bin.max + 1)}`;
  }
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
    const available = metricBins(selected, bins);
    const range = params.has("min") && params.has("max") ? available.find(b =>
      b.min === Number(params.get("min")) &&
      b.max === (params.get("max") === "open" ? null : Number(params.get("max")))) : null;
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
      url.searchParams.set("max", state.range.max ?? "open");
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
    const bins = metricBins(metric, state.bins);
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
      button.dataset.max = bin.max ?? "open";
      button.dataset.count = bin.count;
      button.setAttribute("aria-label", `${rangeLabel(bin)}: ${bin.count} declarations`);
      button.setAttribute("aria-pressed", String(!!state.range &&
        state.range.min === bin.min && state.range.max === bin.max));
      button.disabled = bin.count === 0;
      button.title = button.getAttribute("aria-label");
      button.append(element("span", bin.count, "stats-bar-count"));
      const column = element("span", undefined, "stats-column");
      const fill = element("span", undefined, "stats-fill");
      fill.style.height = `${100 * bin.count / peak}%`;
      column.append(fill);
      const text = isTiming(metric) ? rangeLabel(bin) : label(bin);
      button.append(column, element("span", text, "stats-bar-label"));
      button.onclick = () => selectRange(bin);
      bars.append(button);
      const row = element("tr");
      const range = element("th");
      range.scope = "row";
      const choose = element("button", text);
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
      return Object.hasOwn(metric.values, d.id) && (!state.range || inRange(count, state.range)) &&
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
        element("td", declaration.module), element("td", isTiming(metric) ?
          timeLabel(metric.values[declaration.id]) : metric.values[declaration.id]));
      const links = element("td", undefined, "stats-links");
      for (const [text, key] of [["Documentation", "documentation"], ["Source", "source"]]) {
        const link = element("a", text);
        link.href = declaration[key];
        links.append(link);
      }
      row.append(links);
      table.append(row);
    }
    $("stats-selection").textContent = state.range ? `Declarations with ${rangeLabel(state.range)}` :
      isTiming(metric) ? "Measured declarations" : "All declarations";
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
    const timing = isTiming(metric);
    const measured = timing ? Object.keys(metric.values).length : null;
    $("stats-bin-control").hidden = timing;
    $("stats-method-label").textContent = timing ? "How we measured time" : "How the counts work";
    $("stats-range-heading").textContent = timing ? "Time range" : "Uses";
    $("stats-value-heading").textContent = timing ? "Time" : "Uses";
    const summary = $("stats-timing-summary");
    summary.hidden = !timing;
    if (timing) {
      summary.textContent = measured ? `Measured ${measured} of ${metric.eligible} declarations. ` +
        `Median ${timeLabel(metric.summary.median)}. 90th percentile ${timeLabel(metric.summary.p90)}.` :
        bundle.profiling ? `Measured 0 of ${metric.eligible} declarations.` :
        "No timing data for this revision.";
    }
    const empty = timing && !measured;
    $("stats-chart-content").hidden = empty;
    $("stats-list-content").hidden = empty;
    if (!empty) {
      if (chart) drawChart();
      drawRows();
    }
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
