/* Prime Tools — BigInt number theory, all local. */
(function () {
  "use strict";
  var $ = S3.$, $$ = S3.$$;
  var KEY = "prime.v1";
  var TWO64 = 1n << 64n;
  var MR_BASES = [2n, 3n, 5n, 7n, 11n, 13n, 17n, 19n, 23n, 29n, 31n, 37n]; // deterministic for n < 2^64

  // ---------- small primes ----------
  function sieve(n) { var s = new Uint8Array(n + 1), out = []; for (var i = 2; i <= n; i++) { if (s[i]) continue; out.push(i); for (var j = i * i; j <= n; j += i) s[j] = 1; } return out; }
  var SMALL = sieve(100000), SMALLB = SMALL.map(BigInt);

  // ---------- arithmetic ----------
  function babs(a) { return a < 0n ? -a : a; }
  function gcd(a, b) { a = babs(a); b = babs(b); while (b) { var t = a % b; a = b; b = t; } return a; }
  function modpow(b, e, m) { var r = 1n; b %= m; while (e > 0n) { if (e & 1n) r = r * b % m; e >>= 1n; b = b * b % m; } return r; }
  function bitLength(n) { return n.toString(2).length; }
  function randBelow(n) { // uniform-ish BigInt in [0, n)
    var bytes = new Uint8Array(Math.ceil(bitLength(n) / 8) + 8); crypto.getRandomValues(bytes);
    var x = 0n; bytes.forEach(function (b) { x = (x << 8n) | BigInt(b); }); return x % n;
  }
  function isqrt(n) { if (n < 2n) return n; var x = BigInt(Math.floor(Math.sqrt(Number(n)))); if (x === 0n) x = 1n; for (;;) { var y = (x + n / x) >> 1n; if (y >= x) { while (x * x > n) x--; while ((x + 1n) * (x + 1n) <= n) x++; return x; } x = y; } }

  // ---------- Miller–Rabin ----------
  function strongProbable(n, a, d, s) {
    a %= n; if (a === 0n) return true;
    var x = modpow(a, d, n);
    if (x === 1n || x === n - 1n) return true;
    for (var i = 1; i < s; i++) { x = x * x % n; if (x === n - 1n) return true; if (x === 1n) return false; }
    return false;
  }
  // → {prime, method: "trial" | "deterministic" | "probabilistic", rounds}
  function isPrime(n, extraRounds) {
    n = BigInt(n);
    if (n < 2n) return { prime: false, method: "definition" };
    for (var i = 0; i < 168; i++) { var p = SMALLB[i]; if (n === p) return { prime: true, method: "trial" }; if (n % p === 0n) return { prime: false, method: "trial", witness: p }; }
    if (n < 1000000n) return { prime: true, method: "trial" }; // no factor up to 997 < √n
    var d = n - 1n, s = 0; while ((d & 1n) === 0n) { d >>= 1n; s++; }
    for (i = 0; i < MR_BASES.length; i++) if (!strongProbable(n, MR_BASES[i], d, s)) return { prime: false, method: "Miller-Rabin", witness: MR_BASES[i] };
    if (n < TWO64) return { prime: true, method: "deterministic", rounds: MR_BASES.length };
    var k = extraRounds === undefined ? 24 : extraRounds;
    for (i = 0; i < k; i++) { var a = 2n + randBelow(n - 3n); if (!strongProbable(n, a, d, s)) return { prime: false, method: "Miller-Rabin", witness: a }; }
    return { prime: true, method: "probabilistic", rounds: MR_BASES.length + k };
  }

  // ---------- Pollard rho (Brent) ----------
  function rho(n, budget) {
    if (n % 2n === 0n) return 2n;
    budget = budget || 4000000;
    var used = 0;
    for (var c = 1n; c < 40n; c++) {
      var y = 2n, m = 128, g = 1n, r = 1, q = 1n, x = 0n, ys = 0n;
      var f = function (v) { return (v * v + c) % n; };
      while (g === 1n) {
        x = y;
        for (var i = 0; i < r; i++) y = f(y);
        var k = 0;
        while (k < r && g === 1n) {
          ys = y;
          var lim = Math.min(m, r - k);
          for (i = 0; i < lim; i++) { y = f(y); q = q * babs(x - y) % n; }
          g = gcd(q, n); k += m; used += lim;
          if (used > budget) return null;
        }
        r *= 2;
      }
      if (g === n) { do { ys = f(ys); g = gcd(babs(x - ys), n); used++; } while (g === 1n && used < budget); }
      if (g !== n && g !== 1n) return g;
    }
    return null;
  }

  // → {factors: Map(p → e) with BigInt keys, unfactored: [BigInt], probable: bool}
  function factor(n) {
    n = babs(BigInt(n));
    var F = new Map(), rest = [], probable = false;
    function addF(p, e) { var k = p.toString(); F.set(k, (F.get(k) || 0) + (e || 1)); }
    if (n < 2n) return { factors: F, unfactored: rest, probable: false };
    for (var i = 0; i < SMALLB.length && SMALLB[i] * SMALLB[i] <= n; i++) {
      var p = SMALLB[i];
      while (n % p === 0n) { n /= p; addF(p); }
    }
    if (n > 1n && n < 10000000000n) { addF(n); n = 1n; } // no factor below 10^5, so n < 10^10 is prime
    var stack = n > 1n ? [n] : [];
    while (stack.length) {
      var m = stack.pop();
      if (m === 1n) continue;
      var t = isPrime(m);
      if (t.prime) { addF(m); if (t.method === "probabilistic") probable = true; continue; }
      var r2 = isqrt(m); if (r2 * r2 === m) { stack.push(r2, r2); continue; }
      var d = rho(m);
      if (!d) { rest.push(m); continue; }
      stack.push(d, m / d);
    }
    var sorted = new Map(Array.from(F).sort(function (a, b) { var x = BigInt(a[0]), y = BigInt(b[0]); return x < y ? -1 : x > y ? 1 : 0; }));
    return { factors: sorted, unfactored: rest, probable: probable };
  }

  // ---------- divisors / arithmetic functions ----------
  function divisorInfo(fr, n) {
    var count = 1n, sigma = 1n, phi = n;
    fr.factors.forEach(function (e, ps) {
      var p = BigInt(ps); count *= BigInt(e + 1);
      sigma *= (p ** BigInt(e + 1) - 1n) / (p - 1n);
      phi = phi / p * (p - 1n);
    });
    var list = null;
    if (!fr.unfactored.length && count <= 20000n) {
      list = [1n];
      fr.factors.forEach(function (e, ps) {
        var p = BigInt(ps), next = [];
        list.forEach(function (dv) { var pk = 1n; for (var k = 0; k <= e; k++) { next.push(dv * pk); pk *= p; } });
        list = next;
      });
      list.sort(function (a, b) { return a < b ? -1 : a > b ? 1 : 0; });
    }
    return { count: count, sigma: sigma, phi: phi, list: list };
  }
  function nextPrime(n) { n = BigInt(n); if (n < 2n) return 2n; var c = n + 1n; if (c > 2n && c % 2n === 0n) c++; for (var i = 0; i < 200000; i++, c += 2n) if (isPrime(c, 8).prime) return c; return null; }
  function prevPrime(n) { n = BigInt(n); if (n <= 2n) return null; if (n === 3n) return 2n; var c = n - 1n; if (c % 2n === 0n) c--; for (var i = 0; i < 200000 && c >= 3n; i++, c -= 2n) if (isPrime(c, 8).prime) return c; return c === 1n ? 2n : null; }

  // ---------- Euclid ----------
  function euclidSteps(a, b) {
    var lines = []; a = babs(a); b = babs(b);
    if (a < b) { var t = a; a = b; b = t; }
    if (b === 0n) { lines.push("gcd(" + a + ", 0) = " + a); return { g: a, lines: lines }; }
    while (b) { var q = a / b, r = a % b; lines.push(a + " = " + q + " × " + b + " + " + r); a = b; b = r; }
    return { g: a, lines: lines };
  }
  function gcdLcm(nums) {
    var g = nums[0], l = nums[0], steps = [];
    for (var i = 1; i < nums.length; i++) {
      var e = euclidSteps(g, nums[i]);
      steps.push({ head: "gcd(" + g + ", " + nums[i] + ")", lines: e.lines.concat(["→ " + e.g]) });
      var gl = gcd(l, nums[i]), nl = gl === 0n ? 0n : babs(l * nums[i]) / gl;
      steps.push({ head: "lcm(" + l + ", " + nums[i] + ") = " + babs(l) + " × " + babs(nums[i]) + " ÷ " + gl + " = " + nl, lines: [] });
      g = e.g; l = nl;
    }
    return { gcd: babs(g), lcm: babs(l), steps: steps };
  }

  // ---------- segmented sieve (Numbers, below 10^15) ----------
  var RANGE_MAX = 10000000, HI_MAX = 1e15;
  function primesInRange(lo, hi) {
    lo = Math.max(2, Math.floor(lo)); hi = Math.floor(hi);
    if (hi < lo) return [];
    var lim = Math.floor(Math.sqrt(hi)), base = lim <= 100000 ? SMALL.filter(function (p) { return p <= lim; }) : sieve(lim);
    var size = hi - lo + 1, mark = new Uint8Array(size), out = [];
    base.forEach(function (p) {
      var start = Math.max(p * p, Math.ceil(lo / p) * p);
      for (var j = start; j <= hi; j += p) mark[j - lo] = 1;
    });
    for (var i = 0; i < size; i++) if (!mark[i]) out.push(lo + i);
    return out;
  }

  // ---------- input: whole numbers or a tiny expression (+ − × ^ and brackets), BigInt, no eval ----------
  function parseBig(src) {
    var s = String(src).replace(/[٠-٩]/g, function (c) { return c.charCodeAt(0) - 0x660; }).replace(/[−–]/g, "-").replace(/[×·]/g, "*").replace(/\*\*/g, "^").replace(/[,_\s']/g, "");
    if (!s) return null;
    var i = 0;
    function peek() { return s[i]; }
    function expr() { var v = term(); while (peek() === "+" || peek() === "-") { var op = s[i++]; var w = term(); v = op === "+" ? v + w : v - w; } return v; }
    function term() { var v = power(); while (peek() === "*") { i++; v *= power(); } return v; }
    function power() {
      var b = atom();
      if (peek() === "^") { i++; var e = power(); if (e < 0n) throw new Error("Negative powers aren't whole numbers"); if (e > 100000n || (b > 1n && BigInt(bitLength(b)) * e > 1000000n)) throw new Error("That power is too large"); return b ** e; }
      return b;
    }
    function atom() {
      if (peek() === "-") { i++; return -atom(); }
      if (peek() === "(") { i++; var v = expr(); if (s[i++] !== ")") throw new Error("Missing )"); return v; }
      var m = /^\d+/.exec(s.slice(i));
      if (!m) throw new Error(i < s.length ? "Unexpected “" + s[i] + "”" : "Incomplete expression");
      i += m[0].length;
      if (s[i] === "!") { i++; var n = BigInt(m[0]); if (n > 5000n) throw new Error("Factorial too large"); var f = 1n; for (var k = 2n; k <= n; k++) f *= k; return f; }
      return BigInt(m[0]);
    }
    var v = expr();
    if (i < s.length) throw new Error("Unexpected “" + s[i] + "”");
    return v;
  }

  // ---------- formatting ----------
  var SUP = "⁰¹²³⁴⁵⁶⁷⁸⁹";
  function sup(n) { return String(n).split("").map(function (d) { return SUP[d]; }).join(""); }
  function group(n) { var s = n.toString(), neg = s[0] === "-"; if (neg) s = s.slice(1); return (neg ? "−" : "") + (s.length > 4 ? s.replace(/\B(?=(\d{3})+(?!\d))/g, ",") : s); }
  function factorText(fr, plain) {
    var parts = [];
    fr.factors.forEach(function (e, p) { parts.push(plain ? p + (e > 1 ? "^" + e : "") : p + (e > 1 ? sup(e) : "")); });
    fr.unfactored.forEach(function (m) { parts.push(plain ? "(" + m + ")" : "(" + m + " composite)"); });
    return parts.join(plain ? " * " : " × ");
  }

  // ---------- UI: check ----------
  var lastSummary = "";
  function stat(label, v, cls) { return S3.h("div", { "class": "stat " + (cls || "") }, [S3.h("b", { text: v }), S3.h("span", { text: label })]); }
  var token = 0;
  function check() {
    var raw = $("#num").value, v = $("#verdict"), st = $("#nstats"), dv = $("#divs");
    S3.store(KEY, { num: raw, gcd: $("#gcdIn").value, lo: $("#lo").value, hi: $("#hi").value });
    v.textContent = ""; st.textContent = ""; dv.textContent = ""; lastSummary = "";
    if (!raw.trim()) { v.appendChild(S3.h("div", { "class": "empty" }, [S3.h("b", { text: "Type a number" }), "Primality, factors and divisors appear here."])); return; }
    var n;
    try { n = parseBig(raw); } catch (e) { v.appendChild(S3.h("div", { "class": "pt-err", text: e.message })); return; }
    if (n === null) return;
    if (n.toString().length > 400) { v.appendChild(S3.h("div", { "class": "pt-err", text: "Please keep it under 400 digits." })); return; }
    var neg = n < 0n, a = babs(n), t = isPrime(a);
    var label = a < 2n ? (a === 0n ? "0 is neither prime nor composite" : "1 is neither prime nor composite (by definition)") : t.prime ? (t.method === "probabilistic" ? "Probable prime" : "Prime") : "Composite";
    var how = a < 2n ? "" : t.method === "trial" ? "Checked by trial division." : t.method === "deterministic" ? "Deterministic Miller-Rabin (12 bases, exact for every number below 2⁶⁴)." :
      t.method === "probabilistic" ? "Miller-Rabin with " + t.rounds + " bases. Above 2⁶⁴ this is probabilistic: the chance a composite passes is below 4⁻" + t.rounds + "." :
      "Miller-Rabin: base " + t.witness + " proves it composite.";
    v.appendChild(S3.h("div", { "class": "pt-head" }, [
      S3.h("span", { "class": "chip " + (a < 2n ? "" : t.prime ? "ok" : "warn"), text: label }),
      S3.h("b", { "class": "mono pt-n", text: (neg ? "−" : "") + group(a) }),
      S3.h("span", { "class": "faint", text: a.toString().length + " digit" + (a.toString().length === 1 ? "" : "s") + (neg ? " · sign ignored for factors" : "") })
    ]));
    if (how) v.appendChild(S3.h("p", { "class": "faint pt-p", text: how }));
    if (a < 2n) return;
    var my = ++token;
    v.appendChild(S3.h("p", { "class": "faint pt-p", id: "working", text: "Factoring…" }));
    setTimeout(function () {
      if (my !== token) return;
      var t0 = performance.now(), fr = factor(a), ms = performance.now() - t0, info = divisorInfo(fr, a);
      var w = $("#working"); if (w) w.remove();
      v.appendChild(S3.h("div", { "class": "pt-fact mono", text: (t.prime ? group(a) : factorText(fr)) }));
      if (fr.unfactored.length) v.appendChild(S3.h("p", { "class": "pt-p pt-warn", text: "A composite part was too hard to split in the time allowed (Pollard rho); it is shown in brackets." }));
      else if (fr.probable) v.appendChild(S3.h("p", { "class": "faint pt-p", text: "Factors above 2⁶⁴ are probable primes." }));
      var np = nextPrime(a), pp = prevPrime(a), full = !fr.unfactored.length;
      [["divisors", full ? group(info.count) : "—"], ["sum of divisors σ", full ? group(info.sigma) : "—"], ["Euler φ", full ? group(info.phi) : "—"],
        ["previous prime", pp === null ? "none" : group(pp)], ["next prime", np === null ? "—" : group(np)], ["time", ms < 1 ? "< 1 ms" : Math.round(ms) + " ms"]]
        .forEach(function (x) { st.appendChild(stat(x[0], x[1])); });
      if (full && info.sigma === 2n * a) st.appendChild(stat("σ(n) = 2n", "Perfect number", "pt-perfect"));
      if (info.list) {
        var shown = info.list.slice(0, 600);
        dv.appendChild(S3.h("details", { "class": "pt-steps", open: info.list.length <= 120 }, [S3.h("summary", { text: "All " + info.list.length + " divisors" }),
          S3.h("div", { "class": "pt-dlist mono", text: shown.map(String).join(", ") + (info.list.length > shown.length ? ", …" : "") })]));
      }
      lastSummary = a + (t.prime ? " is prime" : " = " + factorText(fr, true)) + (full ? "\ndivisors: " + info.count + ", σ = " + info.sigma + ", φ = " + info.phi : "") +
        (pp !== null ? "\nprevious prime: " + pp : "") + (np !== null ? "\nnext prime: " + np : "");
    }, 10);
  }

  // ---------- UI: gcd ----------
  function gcdUi() {
    var raw = $("#gcdIn").value, box = $("#gstats"), ol = $("#gsteplist");
    box.textContent = ""; ol.textContent = "";
    var nums = [];
    try { nums = raw.split(/[\s,;]+/).filter(Boolean).map(parseBig); } catch (e) { box.appendChild(S3.h("div", { "class": "pt-err", text: e.message })); $("#gsteps").hidden = true; return; }
    if (nums.length < 2) { box.appendChild(S3.h("p", { "class": "faint pt-p", text: "Type two or more whole numbers." })); $("#gsteps").hidden = true; return; }
    if (nums.length > 50) nums = nums.slice(0, 50);
    var r = gcdLcm(nums);
    box.appendChild(stat("GCD (greatest common divisor)", group(r.gcd)));
    box.appendChild(stat("LCM (least common multiple)", group(r.lcm)));
    if (nums.length === 2 && r.gcd === 1n) box.appendChild(S3.h("span", { "class": "chip ok", text: "coprime" }));
    $("#gsteps").hidden = false;
    r.steps.forEach(function (s) { ol.appendChild(S3.h("li", {}, [S3.h("b", { text: s.head })].concat(s.lines.length ? [S3.h("div", { "class": "mono pt-eu", text: s.lines.join("\n") })] : []))); });
  }

  // ---------- UI: range ----------
  var rangeList = [];
  function rangeUi() {
    var lo = Number(String($("#lo").value).replace(/[,_\s]/g, "")), hi = Number(String($("#hi").value).replace(/[,_\s]/g, "")), box = $("#rlist");
    box.textContent = ""; rangeList = [];
    S3.store(KEY, { num: $("#num").value, gcd: $("#gcdIn").value, lo: $("#lo").value, hi: $("#hi").value });
    if (!Number.isFinite(lo) || !Number.isFinite(hi) || !Number.isInteger(lo) || !Number.isInteger(hi)) { $("#rcount").textContent = "Enter whole numbers"; return; }
    if (hi >= HI_MAX) { $("#rcount").textContent = "Keep “To” below 10¹⁵"; return; }
    if (hi - lo + 1 > RANGE_MAX) { $("#rcount").textContent = "At most 10,000,000 numbers at a time"; return; }
    rangeList = primesInRange(lo, hi);
    $("#rcount").textContent = rangeList.length.toLocaleString() + " prime" + (rangeList.length === 1 ? "" : "s");
    var shown = rangeList.slice(0, 3000);
    box.textContent = shown.join(", ") + (rangeList.length > shown.length ? ", … (" + (rangeList.length - shown.length).toLocaleString() + " more in the .txt)" : "");
  }

  // ---------- wiring ----------
  var saved = S3.store(KEY) || {};
  $("#num").value = saved.num != null ? saved.num : "600851475143";
  $("#gcdIn").value = saved.gcd != null ? saved.gcd : "84, 126, 210";
  $("#lo").value = saved.lo || "1"; $("#hi").value = saved.hi || "100";
  $("#num").addEventListener("input", S3.debounce(check, 250));
  $("#gcdIn").addEventListener("input", S3.debounce(gcdUi, 200));
  $("#lo").addEventListener("input", S3.debounce(rangeUi, 300));
  $("#hi").addEventListener("input", S3.debounce(rangeUi, 300));
  $$("[data-try]").forEach(function (b) { b.addEventListener("click", function () { $("#num").value = b.dataset.try; check(); }); });
  $("#rcopy").addEventListener("click", function () { if (!rangeList.length) return S3.toast("No primes to copy", "error"); S3.copy(rangeList.join(", ")); S3.done(); });
  $("#rtxt").addEventListener("click", function () { if (!rangeList.length) return S3.toast("No primes to save", "error"); S3.download(rangeList.join("\n") + "\n", "primes-" + $("#lo").value + "-" + $("#hi").value + ".txt", "text/plain"); S3.done(); });
  $("#num").addEventListener("keydown", function (e) { if (e.key === "Enter") { check(); S3.done(); } });
  $("#ncopy").addEventListener("click", function () { if (!lastSummary) return S3.toast("Nothing to copy yet", "error"); S3.copy(lastSummary); S3.done(); });
  check(); gcdUi(); rangeUi();

  window.S3_DEMO = function () { $("#num").value = "600851475143"; check(); $("#gcdIn").value = "84, 126, 210"; gcdUi(); $("#lo").value = "1"; $("#hi").value = "200"; rangeUi(); return new Promise(function (r) { setTimeout(r, 300); }); };

  // ---------- self-test: known primes, Carmichael numbers, strong pseudoprimes, rho ----------
  window.S3_SELFTEST = function () {
    var f = [];
    function ok(n, c) { if (!c) f.push(n); }
    var M61 = (1n << 61n) - 1n;
    [2n, 3n, 97n, 7919n, 1000003n, 1000000007n, 2147483647n, M61, 18446744073709551557n].forEach(function (p) { var t = isPrime(p); ok("prime " + p, t.prime && (p < 1000000n || t.method === "deterministic")); });
    ok("2^61-1 deterministic", isPrime(M61).method === "deterministic");
    [0n, 1n, 4n, 561n, 1105n, 1729n, 2465n, 2821n, 6601n, 8911n, 3215031751n, 3825123056546413051n, TWO64 - 1n, 1000000007n * 1000000009n].forEach(function (c) { ok("composite " + c, !isPrime(c).prime); });
    var M89 = (1n << 89n) - 1n, t89 = isPrime(M89); ok("2^89-1 probable", t89.prime && t89.method === "probabilistic");
    ok("2^67-1 composite", !isPrime((1n << 67n) - 1n).prime); // = 193707721 × 761838257287
    var d = rho(600851475143n); ok("rho 600851475143", d !== null && d > 1n && d < 600851475143n && 600851475143n % d === 0n);
    ok("factor 600851475143", factorText(factor(600851475143n), true) === "71 * 839 * 1471 * 6857");
    var semi = factor(1000000007n * 998244353n); ok("rho semiprime", factorText(semi, true) === "998244353 * 1000000007");
    var m67 = factor((1n << 67n) - 1n); ok("factor 2^67-1", factorText(m67, true) === "193707721 * 761838257287");
    var big = factor(3825123056546413051n); ok("factor spsp", factorText(big, true) === "149491 * 747451 * 34233211");
    ok("factor 360", factorText(factor(360n), true) === "2^3 * 3^2 * 5");
    var i360 = divisorInfo(factor(360n), 360n); ok("divisors 360", i360.count === 24n && i360.list.length === 24 && i360.sigma === 1170n && i360.phi === 96n);
    ok("perfect 28", divisorInfo(factor(28n), 28n).sigma === 56n && divisorInfo(factor(8128n), 8128n).sigma === 16256n);
    ok("square cofactor", factorText(factor(1000003n * 1000003n), true) === "1000003^2");
    ok("next/prev", nextPrime(13n) === 17n && prevPrime(13n) === 11n && prevPrime(2n) === null && nextPrime(1n) === 2n && prevPrime(3n) === 2n && nextPrime(M61 - 2n) === M61);
    var g = gcdLcm([12n, 18n, 30n]); ok("gcd/lcm", g.gcd === 6n && g.lcm === 180n && gcdLcm([0n, 5n]).gcd === 5n && gcdLcm([84n, 126n, 210n]).gcd === 42n);
    ok("euclid lines", euclidSteps(1071n, 462n).lines.join("|") === "1071 = 2 × 462 + 147|462 = 3 × 147 + 21|147 = 7 × 21 + 0");
    ok("sieve 1..100", primesInRange(1, 100).length === 25 && primesInRange(1, 1000000).length === 78498);
    var lo = 1e12, seg = primesInRange(lo, lo + 2000), brute = [];
    for (var k = lo; k <= lo + 2000; k++) if (isPrime(BigInt(k)).prime) brute.push(k);
    ok("segmented sieve = Miller-Rabin", seg.length > 0 && seg.join() === brute.join());
    ok("parse", parseBig("2^61-1") === M61 && parseBig("1,000,003") === 1000003n && parseBig("1000003*1000033") === 1000003n * 1000033n && parseBig("5!") === 120n && parseBig("(2+3)^2") === 25n);
    var bad = false; try { parseBig("2^x"); } catch (e) { bad = true; } ok("parse rejects", bad);
    return f.length ? f : true;
  };
})();
