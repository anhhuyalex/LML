// Checks for the pure functions of book-nav.js (run by check_nav_js.py, or: node check_nav.cjs).
"use strict";
const assert = require("assert");
const path = require("path");
const nav = require(path.join(__dirname, "../../typstverso/templates/html/book-nav.js"));

const check = (name, body) => { body(); console.log("ok  " + name); };

check("clampWidth keeps the width between the minimum and the smaller of 560 and half the window", () => {
  assert.strictEqual(nav.clampWidth(100, 1400), 160);
  assert.strictEqual(nav.clampWidth(900, 1400), 560);
  assert.strictEqual(nav.clampWidth(900, 800), 400);
  assert.strictEqual(nav.clampWidth(300.4, 1400), 300);
  assert.strictEqual(nav.clampWidth(NaN, 1400), 240);
  assert.strictEqual(nav.clampWidth(400, 200), 160); // a tiny window never goes below the minimum
});

check("widthAfterKey: arrows, Shift, Home, End, Enter; other keys are ignored", () => {
  assert.strictEqual(nav.widthAfterKey("ArrowRight", false, 240, 1400), 256);
  assert.strictEqual(nav.widthAfterKey("ArrowLeft", true, 240, 1400), 176);
  assert.strictEqual(nav.widthAfterKey("ArrowLeft", false, 160, 1400), 160);
  assert.strictEqual(nav.widthAfterKey("Home", false, 300, 1400), 160);
  assert.strictEqual(nav.widthAfterKey("End", false, 300, 1400), 560);
  assert.strictEqual(nav.widthAfterKey("Enter", false, 300, 1400), 240);
  assert.strictEqual(nav.widthAfterKey("a", false, 300, 1400), null);
});

check("pageName and homeHref", () => {
  assert.strictEqual(nav.pageName("/LML/talagrand/s04.html"), "s04.html");
  assert.strictEqual(nav.pageName("/LML/talagrand/"), "");
  assert.strictEqual(nav.homeHref("https:"), "./");
  assert.strictEqual(nav.homeHref("file:"), "index.html");
});

check("formatSize", () => {
  assert.strictEqual(nav.formatSize(51.4e6), "51 MB");
  assert.strictEqual(nav.formatSize(250e3), "250 kB");
  assert.strictEqual(nav.formatSize(10), "1 kB");
});

const TOC = {
  title: "Book", home: "./", pdf: "book.pdf", links: [],
  sections: [
    {id: "s00", part: 0, title: "Intro", href: "s00.html", pages: 1, bytes: 5e5, headings: []},
    {id: "s04", part: 4, title: "Latala", href: "s04.html", pages: 34, bytes: 12e6, headings: [
      {level: 2, title: "4.1 A", id: "heading-2"}, {level: 3, title: "4.1.1 B", id: "heading-3"},
      {level: 2, title: "4.2 C", id: "heading-4"}]},
    {id: "s05", part: 5, title: "Decorrelation", href: "s05.html", pages: 2, bytes: 3e6, headings: [
      {level: 2, title: "5.1 D", id: "heading-2"}]},
  ],
};

check("nestHeadings nests by level and prefixes the links", () => {
  const tree = nav.nestHeadings(TOC.sections[1].headings, "s04.html");
  assert.deepStrictEqual(tree.map(e => e.title), ["4.1 A", "4.2 C"]);
  assert.deepStrictEqual(tree[0].children.map(e => e.href), ["s04.html#heading-3"]);
  assert.deepStrictEqual(tree[1].children, []);
});

check("buildTreeModel: one current section, with in-page links; others link to their page", () => {
  const model = nav.buildTreeModel(TOC, "s04.html");
  assert.deepStrictEqual(model.map(s => s.current), [false, true, false]);
  assert.deepStrictEqual(model.map(s => s.label), ["Intro", "4 Latala", "5 Decorrelation"]);
  assert.strictEqual(model[1].href, "#page-1");
  assert.strictEqual(model[1].headings[0].href, "#heading-2");
  assert.strictEqual(model[2].href, "s05.html");
  assert.strictEqual(model[2].headings[0].href, "s05.html#heading-2");
  assert.strictEqual(model[1].meta, "34 pages · 12 MB");
  assert.strictEqual(model[0].meta, "1 page · 500 kB");
});

check("buildTreeModel on an unknown page marks no section as current", () => {
  assert.ok(nav.buildTreeModel(TOC, "").every(section => !section.current));
});

check("neighbours", () => {
  const sections = TOC.sections;
  assert.deepStrictEqual(nav.neighbours(sections, "s04.html"), {previous: sections[0], next: sections[2]});
  assert.deepStrictEqual(nav.neighbours(sections, "s00.html"), {previous: null, next: sections[1]});
  assert.deepStrictEqual(nav.neighbours(sections, "nope.html"), {previous: null, next: null});
});

check("headingAtOffset picks the last heading at or above the offset", () => {
  const anchors = [{id: "a", top: -500}, {id: "b", top: 20}, {id: "c", top: 400}];
  assert.strictEqual(nav.headingAtOffset(anchors, 60), "b");
  assert.strictEqual(nav.headingAtOffset(anchors, 1000), "c");
  assert.strictEqual(nav.headingAtOffset(anchors.slice(2), 60), null);
  assert.strictEqual(nav.headingAtOffset([], 60), null);
});

check("saved preferences survive missing, corrupt or blocked storage", () => {
  const memory = new Map();
  const store = nav.makeStore(() => ({getItem: k => memory.get(k) ?? null, setItem: (k, v) => memory.set(k, v)}));
  assert.strictEqual(nav.loadWidth(store, 1400), 240);               // nothing saved
  store.write(nav.KEYS.width, "320");
  assert.strictEqual(nav.loadWidth(store, 1400), 320);
  store.write(nav.KEYS.width, "banana");
  assert.strictEqual(nav.loadWidth(store, 1400), 240);               // corrupt
  store.write(nav.KEYS.openSections, "{not json");
  assert.deepStrictEqual([...nav.loadOpenSections(store)], []);
  store.write(nav.KEYS.openSections, '["s05"]');
  assert.deepStrictEqual([...nav.loadOpenSections(store)], ["s05"]);
  const blocked = nav.makeStore(() => { throw new Error("SecurityError"); });
  assert.strictEqual(blocked.read("x"), null);
  blocked.write("x", "y");                                           // must not throw
  assert.strictEqual(nav.loadWidth(blocked, 1400), 240);
});
