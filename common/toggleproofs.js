function toggleDisplay(id) {
  var el = document.getElementById(id);
  if (el.style.display === "none" || el.classList.contains('hidden')) {
    el.style.display = "block";
    el.classList.remove('hidden');
  } else {
    el.style.display = "none";
    el.classList.add('hidden');
  }
}

function hideAll(cls) {
  var els = document.getElementsByClassName(cls);
  for (var i = 0; i < els.length; i++) {
    els[i].classList.add('hidden');
    els[i].style.display = "none";
  }
}

document.addEventListener("DOMContentLoaded", function () {
  hideAll('proofscript');
});

