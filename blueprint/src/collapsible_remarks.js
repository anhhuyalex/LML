/* Make remarks collapsible, like proofs: click the heading to expand or collapse.
 * Remarks start collapsed; following a link to a remark (or the "#" anchor) expands it. */
$(document).ready(function() {
  function setOpen(wrapper, open) {
    var arrow = wrapper.children("div.remark_thmheading").children("span.expand-remark");
    var content = wrapper.children("div.remark_thmcontent");
    arrow.html(open ? "▼" : "▶");
    if (open) { content.show(); } else { content.hide(); }
  }

  $("div.remark_thmwrapper").each(function() {
    var wrapper = $(this);
    var heading = wrapper.children("div.remark_thmheading");
    heading.addClass("collapsible-remark-heading");
    heading.children("span.remark_thmcaption").before('<span class="expand-remark">▶</span> ');
    setOpen(wrapper, false);
  });

  $("div.remark_thmheading").click(function(event) {
    /* clicks on links and buttons in the heading (uses-graph popup, "#" anchor) do not toggle */
    if ($(event.target).closest("a, button, div.modal-container").length) { return; }
    var wrapper = $(this).parent();
    var content = wrapper.children("div.remark_thmcontent");
    var open = !content.is(":visible");
    wrapper.children("div.remark_thmheading").children("span.expand-remark").html(open ? "▼" : "▶");
    content.slideToggle();
  });

  function openFromHash() {
    var id = decodeURIComponent(window.location.hash.replace(/^#/, ""));
    if (!id) { return; }
    var target = document.getElementById(id);
    if (!target) { return; }
    var wrapper = $(target).closest("div.remark_thmwrapper");
    if (wrapper.length) {
      setOpen(wrapper, true);
      target.scrollIntoView();
    }
  }
  openFromHash();
  $(window).on("hashchange", openFromHash);

  /* in-page links to a remark expand it too, even when the hash does not change */
  $("a[href*='#rmk:']").click(function() {
    var id = $(this).attr("href").split("#")[1];
    var wrapper = $(document.getElementById(id)).closest("div.remark_thmwrapper");
    if (wrapper.length) { setOpen(wrapper, true); }
  });
});
