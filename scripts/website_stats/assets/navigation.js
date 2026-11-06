/* Keep Stats navigation separate from the Referee application's release-specific code. */
"use strict";
(() => {
  const links = document.getElementById("nav-links");
  if (links) {
    const addStats = () => {
      if (links.querySelector("[data-lml-stats]")) return;
      const sorries = links.querySelector('a[href="#/sorries"]');
      if (!sorries) return;
      const link = document.createElement("a");
      link.href = "stats/";
      link.textContent = "Stats";
      link.dataset.lmlStats = "true";
      sorries.after(link);
    };
    new MutationObserver(addStats).observe(links, {childList: true});
    addStats();
  }
  if (document.body.dataset.lmlStats === "true") {
    document.getElementById("menu").onclick = () =>
      document.getElementById("side").classList.toggle("open");
    const theme = localStorage.getItem("referee-site:theme");
    if (theme === "light" || theme === "dark") document.documentElement.dataset.theme = theme;
  }
})();
