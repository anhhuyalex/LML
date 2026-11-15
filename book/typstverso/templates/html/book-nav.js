/* The Contents pane of the book pages (LML addition to the vendored TypstVerso reader).

   What it does, in the order of the file:
     1. Pure helpers (no DOM): width limits, keys, the whole-book tree model, scroll position.
        They are exported for Node (`module.exports`) and tested in book/talagrand/checks.
     2. Saved preferences: pane width, collapsed or not (localStorage), open sections (sessionStorage).
     3. Layout: apply the saved state before the first paint; hide/show button; splitter (mouse, touch,
        keyboard).
     4. Contents: fetch toc.json (written by make_toc.py) and show every section of the book, with the
        current one open and the heading on screen highlighted.

   The page works without this file or without toc.json: reader.js still writes the outline of the
   current section, and book.html has a plain "Book home" link. Pages are loaded as
   <script src="book-nav.js"> in <head>, so step 3's saved state is applied before anything is drawn. */
"use strict";

const bookNav = (() => {
  // ---------------------------------------------------------------- 1. pure helpers

  const WIDTH = {initial: 240, min: 160, max: 560, step: 16, bigStep: 64};
  const SCROLL_SPY_OFFSET = 60; // px below the top of the window where a heading counts as "current"

  /** A pane width in px that is allowed: between WIDTH.min and the smaller of WIDTH.max and half the window. */
  function clampWidth(width, viewportWidth) {
    if (!Number.isFinite(width)) return WIDTH.initial;
    const max = Math.min(WIDTH.max, viewportWidth / 2);
    return Math.round(Math.max(WIDTH.min, Math.min(width, max)));
  }

  /** The width after a key press on the splitter, or null if the key does nothing there. */
  function widthAfterKey(key, shift, width, viewportWidth) {
    const step = shift ? WIDTH.bigStep : WIDTH.step;
    const target = {ArrowLeft: width - step, ArrowRight: width + step,
                    Home: WIDTH.min, End: WIDTH.max, Enter: WIDTH.initial}[key];
    return target === undefined ? null : clampWidth(target, viewportWidth);
  }

  /** "s04.html" from "/LML/talagrand/s04.html"; "" for a folder URL such as "/LML/talagrand/". */
  function pageName(pathname) {
    return pathname.slice(pathname.lastIndexOf("/") + 1);
  }

  /** Opened from disk, "./" would show a folder listing. */
  function homeHref(protocol) {
    return protocol === "file:" ? "index.html" : "./";
  }

  function formatSize(bytes) {
    return bytes >= 1e6 ? Math.round(bytes / 1e6) + " MB" : Math.max(1, Math.round(bytes / 1e3)) + " kB";
  }

  function sectionLabel(section) {
    return section.part === 0 ? section.title : section.part + " " + section.title;
  }

  /** Nest a flat, ordered list of headings by their level (2 = top of the list, 3 inside it, ...). */
  function nestHeadings(headings, hrefBase) {
    const roots = [];
    const open = []; // the chain of enclosing entries, deepest last
    for (const heading of headings) {
      const entry = {title: heading.title, id: heading.id, href: hrefBase + "#" + heading.id, children: []};
      while (open.length && open[open.length - 1].level >= heading.level) open.pop();
      (open.length ? open[open.length - 1].entry.children : roots).push(entry);
      open.push({level: heading.level, entry});
    }
    return roots;
  }

  /** What the tree shows: one entry per section; links stay inside the page for the current section. */
  function buildTreeModel(toc, currentPage) {
    return toc.sections.map(section => {
      const current = section.href === currentPage;
      const base = current ? "" : section.href;
      return {
        id: section.id,
        current,
        label: sectionLabel(section),
        href: current ? "#page-1" : section.href,
        meta: section.pages + (section.pages === 1 ? " page" : " pages") + " · " + formatSize(section.bytes),
        headings: nestHeadings(section.headings, base),
      };
    });
  }

  /** The sections before and after the current one (either may be null, both null if not found). */
  function neighbours(sections, currentPage) {
    const index = sections.findIndex(section => section.href === currentPage);
    if (index < 0) return {previous: null, next: null};
    return {previous: sections[index - 1] || null, next: sections[index + 1] || null};
  }

  /** The id of the last heading whose top edge is at or above `offset`; anchors are in page order. */
  function headingAtOffset(anchors, offset) {
    let found = null;
    for (const anchor of anchors) {
      if (anchor.top > offset) break;
      found = anchor.id;
    }
    return found;
  }

  // ---------------------------------------------------------------- 2. saved preferences

  const KEYS = {width: "talagrand-book.nav.width", collapsed: "talagrand-book.nav.collapsed",
                openSections: "talagrand-book.nav.open"};

  /** Reads and writes a Web Storage area; storage may be missing or blocked, then nothing is saved. */
  function makeStore(getStorage) {
    return {
      read(key) { try { return getStorage().getItem(key); } catch (error) { return null; } },
      write(key, value) { try { getStorage().setItem(key, value); } catch (error) { /* not saved */ }},
    };
  }

  function loadWidth(store, viewportWidth) {
    return clampWidth(parseFloat(store.read(KEYS.width)), viewportWidth);
  }

  function loadOpenSections(store) {
    try {
      const saved = JSON.parse(store.read(KEYS.openSections));
      return new Set(Array.isArray(saved) ? saved : []);
    } catch (error) {
      return new Set();
    }
  }

  // ---------------------------------------------------------------- 3. layout

  function applyWidth(root, width) {
    root.style.setProperty("--nav-width", width + "px");
  }

  function applyCollapsed(root, collapsed) {
    if (collapsed) root.dataset.nav = "collapsed";
    else delete root.dataset.nav;
  }

  /** Called while <head> is parsed: the saved state is in place before the pages are drawn. */
  function applySavedLayout(win, local) {
    const root = win.document.documentElement;
    applyWidth(root, loadWidth(local, win.innerWidth));
    applyCollapsed(root, local.read(KEYS.collapsed) === "1");
  }

  /** The hide/show buttons and the Alt+C shortcut. */
  function mountCollapse(win, local) {
    const doc = win.document, root = doc.documentElement;
    const hide = doc.getElementById("nav-hide"), show = doc.getElementById("nav-show");

    function reflect(collapsed) { // the buttons follow the state; the layout itself is the data-nav attribute
      hide.setAttribute("aria-expanded", String(!collapsed));
      show.setAttribute("aria-expanded", String(!collapsed));
      show.hidden = !collapsed;
    }

    function setCollapsed(collapsed) {
      applyCollapsed(root, collapsed);
      local.write(KEYS.collapsed, collapsed ? "1" : "0");
      reflect(collapsed);
      (collapsed ? show : hide).focus();
    }

    hide.addEventListener("click", () => setCollapsed(true));
    show.addEventListener("click", () => setCollapsed(false));
    win.addEventListener("keydown", event => {
      if (!event.altKey || event.ctrlKey || event.metaKey || event.code !== "KeyC") return;
      event.preventDefault();
      setCollapsed(root.dataset.nav !== "collapsed");
    });
    reflect(root.dataset.nav === "collapsed");
  }

  /** The splitter between the pane and the pages. */
  function mountResizer(win, local) {
    const doc = win.document, root = doc.documentElement;
    const resizer = doc.getElementById("nav-resizer"), pane = doc.getElementById("contents-pane");
    let width = loadWidth(local, win.innerWidth);
    let grabOffset = null; // distance from the pointer to the splitter's centre, while dragging

    function setWidth(requested, save) {
      width = clampWidth(requested, win.innerWidth);
      applyWidth(root, width);
      resizer.setAttribute("aria-valuenow", String(width));
      if (save) local.write(KEYS.width, String(width));
    }

    function splitterCentre() {
      const box = resizer.getBoundingClientRect();
      return box.left + box.width / 2;
    }

    resizer.setAttribute("aria-valuemin", String(WIDTH.min));
    resizer.setAttribute("aria-valuemax", String(clampWidth(WIDTH.max, win.innerWidth)));
    resizer.addEventListener("pointerdown", event => {
      if (event.button !== 0) return;
      grabOffset = event.clientX - splitterCentre();
      resizer.setPointerCapture(event.pointerId); // the page's hover buttons must not take the moves
      doc.body.classList.add("nav-dragging");
      event.preventDefault();
    });
    resizer.addEventListener("pointermove", event => {
      if (grabOffset === null) return;
      const paneLeft = pane.getBoundingClientRect().left;
      setWidth(event.clientX - grabOffset - paneLeft - resizer.offsetWidth / 2, false);
    });
    const endDrag = () => {
      if (grabOffset === null) return;
      grabOffset = null;
      doc.body.classList.remove("nav-dragging");
      local.write(KEYS.width, String(width));
    };
    resizer.addEventListener("pointerup", endDrag);
    resizer.addEventListener("pointercancel", endDrag);
    resizer.addEventListener("keydown", event => {
      const next = widthAfterKey(event.key, event.shiftKey, width, win.innerWidth);
      if (next === null) return;
      event.preventDefault();
      setWidth(next, true);
    });
    resizer.addEventListener("dblclick", () => setWidth(WIDTH.initial, true));
    win.addEventListener("resize", () => setWidth(width, false));
    setWidth(width, false);
  }

  // ---------------------------------------------------------------- 4. contents of the whole book

  function element(doc, tag, className, text) {
    const node = doc.createElement(tag);
    if (className) node.className = className;
    if (text !== undefined) node.textContent = text;
    return node;
  }

  function link(doc, href, text) {
    const anchor = element(doc, "a", "", text);
    anchor.href = href;
    return anchor;
  }

  function renderHeadings(doc, entries) {
    const list = element(doc, "ol");
    for (const entry of entries) {
      const item = element(doc, "li");
      const anchor = link(doc, entry.href, entry.title);
      anchor.dataset.heading = entry.id;
      item.append(anchor);
      if (entry.children.length) item.append(renderHeadings(doc, entry.children));
      list.append(item);
    }
    return list;
  }

  /** One section: a <details> whose summary is the section link. (Clicking the title opens that
      section's page; the triangle only folds the list of headings.) */
  function renderSection(doc, entry, isOpen) {
    const details = element(doc, "details");
    details.dataset.section = entry.id;
    details.open = entry.current || isOpen;
    if (entry.current) details.setAttribute("aria-current", "page");
    const summary = element(doc, "summary");
    summary.append(link(doc, entry.href, entry.label), element(doc, "span", "tree-meta", entry.meta));
    details.append(summary);
    if (entry.headings.length) details.append(renderHeadings(doc, entry.headings));
    return details;
  }

  function renderLinks(doc, className, links) {
    const row = element(doc, "p", className);
    for (const item of links) row.append(link(doc, item.href, item.title));
    return row;
  }

  function renderNeighbours(doc, sections, currentPage) {
    const {previous, next} = neighbours(sections, currentPage);
    const links = [];
    if (previous) links.push({href: previous.href, title: "← " + sectionLabel(previous)});
    if (next) links.push({href: next.href, title: sectionLabel(next) + " →"});
    return renderLinks(doc, "tree-neighbours", links);
  }

  function renderTree(doc, toc, currentPage, openSections) {
    const list = element(doc, "ol");
    for (const entry of buildTreeModel(toc, currentPage)) {
      const item = element(doc, "li");
      item.append(renderSection(doc, entry, openSections.has(entry.id)));
      list.append(item);
    }
    const extras = toc.pdf ? [{href: toc.pdf, title: "Whole book (PDF)"}] : [];
    return [list, renderNeighbours(doc, toc.sections, currentPage),
            renderLinks(doc, "tree-links", extras.concat(toc.links))];
  }

  /** Remember which sections the reader opened, for the next page of this tab. */
  function rememberOpenSections(container, session) {
    container.addEventListener("toggle", () => {
      const open = Array.from(container.querySelectorAll("details[open]")).map(node => node.dataset.section);
      session.write(KEYS.openSections, JSON.stringify(open));
    }, true); // `toggle` does not bubble
  }

  /** Mark the heading the reader is looking at, in the pane's list of the current section. */
  function mountScrollSpy(win, container) {
    const doc = win.document;
    const links = Array.from(container.querySelectorAll("details[aria-current] a[data-heading]"));
    let scheduled = false;

    function update() {
      scheduled = false;
      const anchors = Array.from(doc.querySelectorAll(".heading-anchor"))
        .map(node => ({id: node.id, top: node.getBoundingClientRect().top}));
      const currentId = headingAtOffset(anchors, SCROLL_SPY_OFFSET);
      for (const anchor of links) {
        if (anchor.dataset.heading === currentId) {
          anchor.setAttribute("aria-current", "location");
          anchor.scrollIntoView({block: "nearest"});
        } else {
          anchor.removeAttribute("aria-current");
        }
      }
    }

    win.addEventListener("scroll", () => {
      if (!scheduled) { scheduled = true; win.requestAnimationFrame(update); }
    }, {passive: true});
    update();
  }

  function mountContents(win, session, toc) {
    const doc = win.document;
    const container = doc.getElementById("book-tree");
    const currentPage = pageName(win.location.pathname);
    container.replaceChildren(...renderTree(doc, toc, currentPage, loadOpenSections(session)));
    container.hidden = false;
    doc.getElementById("section-outline").hidden = true; // the tree contains the same headings
    rememberOpenSections(container, session);
    mountScrollSpy(win, container);
  }

  function fetchToc(win) {
    return win.fetch("toc.json").then(response => {
      if (!response.ok) throw new Error("toc.json: HTTP " + response.status);
      return response.json();
    });
  }

  // ---------------------------------------------------------------- start

  function start(win) {
    const local = makeStore(() => win.localStorage), session = makeStore(() => win.sessionStorage);
    applySavedLayout(win, local);
    win.document.addEventListener("DOMContentLoaded", () => {
      win.document.getElementById("book-home").href = homeHref(win.location.protocol);
      mountCollapse(win, local);
      mountResizer(win, local);
      fetchToc(win).then(toc => mountContents(win, session, toc))
        .catch(error => console.warn("Contents of the whole book not shown:", error));
    });
  }

  return {WIDTH, KEYS, clampWidth, widthAfterKey, pageName, homeHref, formatSize, nestHeadings,
          buildTreeModel, neighbours, headingAtOffset, makeStore, loadWidth, loadOpenSections, start};
})();

if (typeof module === "object" && module.exports) module.exports = bookNav; // Node, for the checks
else bookNav.start(window);
