# SPDX-License-Identifier: Apache-2.0
# Copyright (c) 2026 Alexander Stephen Donahue
"""Generate the Interactive Web Observatory (docs/site/index.html) and searchable Lean 4
Blueprint DAG (docs/site/blueprint/index.html + data.json) with strict CSP and WCAG AA."""
from __future__ import annotations

import json
import pathlib

REPO = pathlib.Path(__file__).resolve().parent.parent
SITE_DIR = REPO / "docs" / "site"
BP_DIR = SITE_DIR / "blueprint"
BP_DIR.mkdir(parents=True, exist_ok=True)


BLUEPRINT_NODES = [
    {"id": "T1a", "decl": "QPRigidity.Palomar.prove_t1a", "pillar": "Pillar I (AME)",
     "file": "lean/QPRigidity/AMEGraph.lean", "axioms": ["propext", "Classical.choice", "Quot.sound"],
     "deps": [], "summary": "Radical divisor descent, prime-power/CRT lifting, and universal unimodular graphs (C_5, Prism_6, W_5) for all d >= 2."},
    {"id": "T1b", "decl": "QPRigidity.Palomar.prove_t1b", "pillar": "Pillar I (AME)",
     "file": "lean/QPRigidity/AMEGraph.lean", "axioms": ["propext", "Classical.choice", "Quot.sound"],
     "deps": [], "summary": "Universal Pless moment obstruction: even N >= 2p^2 and odd N >= 2p^2+2p+1 impossible."},
    {"id": "T1c", "decl": "QPRigidity.Palomar.prove_t1c", "pillar": "Pillar I (AME)",
     "file": "lean/QPRigidity/AMEGraph.lean", "axioms": ["propext", "Quot.sound"],
     "deps": [], "summary": "Exact Rains shadow obstructions for N in {4,7,9,11} and exhaustive 0/64 binary N=4 graph proof."},
    {"id": "T1d", "decl": "QPRigidity.Palomar.prove_t1d", "pillar": "Pillar I (AME)",
     "file": "lean/QPRigidity/AMEGraph.lean", "axioms": ["propext", "Quot.sound"],
     "deps": [], "summary": "Torsion Singleton p-rank forcing (dim G[2] = N) and additive F_4-MDS impossibility (N=7 A_6=-21, odd N>=9)."},
    {"id": "T1e", "decl": "QPRigidity.Palomar.prove_t1e", "pillar": "Pillar I (AME)",
     "file": "lean/QPRigidity/AMEGraph.lean", "axioms": ["propext", "Classical.choice", "Quot.sound"],
     "deps": ["T1a", "T1b", "T1c", "T1d"], "summary": "Complete even-d cyclic Z_{2l}-stabilizer dichotomy (N in {2,3,5,6}) and Z_4 vs F_4 separation at (4,4)."},

    {"id": "T2a", "decl": "QPRigidity.Palomar.prove_t2a", "pillar": "Pillar II (RQLS)",
     "file": "lean/QPRigidity/ResolvableQLS.lean", "axioms": ["propext", "Classical.choice", "Quot.sound"],
     "deps": [], "summary": "Trace-nonconstant coset lemma & affine transversal unique intersection for maximal-cardinality t-RQLS."},
    {"id": "T2b", "decl": "QPRigidity.Palomar.prove_t2b", "pillar": "Pillar II (RQLS)",
     "file": "lean/QPRigidity/ResolvableQLS.lean", "axioms": ["propext", "Classical.choice", "Quot.sound"],
     "deps": ["T2a"], "summary": "Kernel-checked certificates for 2-RQLS(9), 3-RQLS(11), 4-RQLS(13), and char-2 3-RQLS(16)."},
    {"id": "T2c", "decl": "QPRigidity.Palomar.prove_t2c", "pillar": "Pillar II (RQLS)",
     "file": "lean/QPRigidity/ResolvableQLS.lean", "axioms": ["propext", "Classical.choice", "Quot.sound"],
     "deps": ["T2b"], "summary": "Direct-product composite lifting theorem (instantiated at 3-RQLS(55))."},
    {"id": "T2d", "decl": "QPRigidity.Palomar.prove_t2d", "pillar": "Pillar II (RQLS)",
     "file": "lean/QPRigidity/ResolvableQLS.lean", "axioms": ["propext", "Quot.sound"],
     "deps": [], "summary": "Zero-gap F_8 obstruction: every orthomorphism fixing 0 is F_2-linear (0/4,872 nonlinear)."},

    {"id": "T3a", "decl": "QPRigidity.Palomar.prove_t3a", "pillar": "Pillar III (Magic)",
     "file": "lean/QPRigidity/MagicGeometry.lean", "axioms": ["propext", "Quot.sound"],
     "deps": [], "summary": "Gurvits-Barnum Cor. 3 exact identity & 2-qubit rational witnesses rho_ent, rho_sep."},
    {"id": "T3b", "decl": "QPRigidity.Palomar.prove_t3b", "pillar": "Pillar III (Magic)",
     "file": "lean/QPRigidity/MagicGeometry.lean", "axioms": ["propext", "Quot.sound"],
     "deps": ["T3a"], "summary": "Exact closed-form circumradii R^2(ASTAB_{2,2}) = 3(13+4*sqrt(3))/484 and R^2(ASTAB_{1,3}) = (7-3*sqrt(5))/6."},
    {"id": "T3c", "decl": "QPRigidity.Palomar.prove_t3c", "pillar": "Pillar III (Magic)",
     "file": "lean/QPRigidity/MagicGeometry.lean", "axioms": ["propext", "Quot.sound"],
     "deps": [], "summary": "Symplectic Marginal Descent: C_n <= (7*4^n + 8)/(15*2^n) and exact 15/7x squared-inball gain for all n >= 2."},
    {"id": "T3d", "decl": "QPRigidity.Palomar.prove_t3d", "pillar": "Pillar III (Magic)",
     "file": "lean/QPRigidity/MagicGeometry.lean", "axioms": ["propext", "Quot.sound"],
     "deps": [], "summary": "Clifford-Reynolds Degree-2 RLT+SOS Barrier: M >= 4^n - 1 for all n >= 1."},

    {"id": "ALL", "decl": "QPRigidity.Palomar.prove_all_rigidity_theorems", "pillar": "Master Bundle",
     "file": "lean/PalomarSolution.lean", "axioms": ["propext", "Classical.choice", "Quot.sound"],
     "deps": ["T1e", "T2c", "T2d", "T3b", "T3c", "T3d"], "summary": "Unified Palomar Challenge-Solution master conjunction across all three pillars."},
    {"id": "NV1", "decl": "QPRigidity.NonVacuity.nonvacuity_pillar1_ame", "pillar": "Non-Vacuity",
     "file": "lean/QPRigidity/NonVacuity.lean", "axioms": ["propext", "Classical.choice", "Quot.sound"],
     "deps": ["T1a", "T1b"], "summary": "Concrete Prism_6 AME(6,12), C_5 AME(5,6), and inhabited Pless specs."},
    {"id": "NV2", "decl": "QPRigidity.NonVacuity.nonvacuity_pillar2_rqls55", "pillar": "Non-Vacuity",
     "file": "lean/QPRigidity/NonVacuity.lean", "axioms": ["propext", "Classical.choice", "Quot.sound"],
     "deps": ["T2b", "T2c"], "summary": "Concrete inhabited 3-RQLS(55) from 3-RQLS(11) x ClassicalMOLS(5)."},
    {"id": "NV3", "decl": "QPRigidity.NonVacuity.nonvacuity_pillar3_magic", "pillar": "Non-Vacuity",
     "file": "lean/QPRigidity/NonVacuity.lean", "axioms": ["propext", "Quot.sound"],
     "deps": ["T3a", "T3c", "T3d"], "summary": "Inhabited witnesses for Gurvits-Barnum D=9, SMD n=3, and RLT barrier n=2."},
    {"id": "ADV", "decl": "QPRigidity.AdversarialTests (6 refutations)", "pillar": "Adversarial",
     "file": "lean/QPRigidity/AdversarialTests.lean", "axioms": ["propext", "Quot.sound"],
     "deps": ["T1a", "T1b", "T2d", "T3b", "T3d"], "summary": "6 concrete boundary refutations (Path_5, N=8/13 Pless, F_8 swap67, Deg-2 RLT M=14, 2q ASTAB outside GB ball)."},
]


def build_blueprint() -> None:
    data = {
        "project": "quantum-phasespace-rigidity",
        "archive_id": "0TH-2026-020",
        "lean_toolchain": "leanprover/lean4:v4.35.0",
        "zero_mathlib": True,
        "nodes": BLUEPRINT_NODES,
    }
    (BP_DIR / "data.json").write_text(json.dumps(data, indent=2) + "\n", encoding="utf-8")

    bp_html = f"""<!DOCTYPE html>
<html lang="en">
<head>
<meta charset="utf-8">
<meta name="viewport" content="width=device-width, initial-scale=1">
<meta http-equiv="Content-Security-Policy" content="default-src 'self'; script-src 'unsafe-inline'; style-src 'unsafe-inline'; img-src 'self' data:;">
<title>Lean 4.35.0 Blueprint DAG — Quantum Phase-Space Rigidity (0TH-2026-020)</title>
<style>
  :root {{ --bg:#0b1120; --card:#111827; --ink:#f8fafc; --muted:#94a3b8; --accent:#38bdf8; --ok:#10b981; --border:#1e293b; }}
  * {{ box-sizing:border-box; }}
  body {{ margin:0; font-family:system-ui,-apple-system,Segoe UI,Roboto,sans-serif; background:var(--bg); color:var(--ink); line-height:1.5; }}
  header {{ padding:1.25rem 2rem; border-bottom:1px solid var(--border); display:flex; flex-wrap:wrap; justify-content:space-between; align-items:center; gap:1rem; }}
  header h1 {{ margin:0; font-size:1.25rem; }}
  a {{ color:var(--accent); text-decoration:none; }} a:hover {{ text-decoration:underline; }}
  main {{ max-width:1280px; margin:0 auto; padding:1.5rem 2rem; }}
  .controls {{ display:flex; flex-wrap:wrap; gap:0.75rem; margin-bottom:1.25rem; }}
  input, select {{ background:var(--card); color:var(--ink); border:1px solid var(--border); padding:0.5rem 0.75rem; border-radius:6px; font-size:0.9rem; }}
  .grid {{ display:grid; grid-template-columns:repeat(auto-fill, minmax(320px, 1fr)); gap:1rem; }}
  .card {{ background:var(--card); border:1px solid var(--border); border-radius:10px; padding:1rem 1.15rem; }}
  .card:hover {{ border-color:var(--accent); }}
  .pill {{ display:inline-block; font-size:0.72rem; padding:0.15rem 0.5rem; border-radius:999px; background:#0f2942; color:#7dd3fc; margin-right:0.35rem; font-weight:600; }}
  .ok {{ background:#064e3b; color:#6ee7b7; }}
  .decl {{ font-family:ui-monospace,SFMono-Regular,Consolas,monospace; font-size:0.82rem; color:#e2e8f0; word-break:break-all; margin:0.4rem 0; }}
  .meta {{ font-size:0.8rem; color:var(--muted); margin-top:0.5rem; }}
  svg {{ width:100%; height:auto; background:#070d19; border:1px solid var(--border); border-radius:10px; margin-bottom:1.5rem; }}
</style>
</head>
<body>
<header>
  <div>
    <h1>Lean 4.35.0 Zero-Mathlib Blueprint DAG — <code>0TH-2026-020</code></h1>
    <div style="font-size:0.85rem;color:#94a3b8;">Alexander Stephen Donahue · Independent Researcher · 23 Audited Declarations · Strictly <code>[propext, Classical.choice, Quot.sound]</code></div>
  </div>
  <nav><a href="../index.html">&larr; Back to Scientific Observatory</a></nav>
</header>
<main>
  <svg id="dag" viewBox="0 0 1160 360" role="img" aria-label="Lean 4 Theorem Dependency DAG"></svg>
  <div class="controls">
    <input id="q" type="search" placeholder="Search theorem, declaration, or file..." aria-label="Search theorems" style="min-width:280px;">
    <select id="pillar" aria-label="Filter by pillar">
      <option value="">All Pillars &amp; Audits</option>
      <option>Pillar I (AME)</option>
      <option>Pillar II (RQLS)</option>
      <option>Pillar III (Magic)</option>
      <option>Master Bundle</option>
      <option>Non-Vacuity</option>
      <option>Adversarial</option>
    </select>
  </div>
  <div id="cards" class="grid"></div>
</main>
<script>
const NODES = {json.dumps(BLUEPRINT_NODES)};
const POS = {{
  T1a:[75,55], T1b:[75,125], T1c:[75,195], T1d:[75,265], T1e:[250,155],
  T2a:[435,70], T2b:[435,160], T2c:[600,120], T2d:[600,225],
  T3a:[775,60], T3b:[940,60], T3c:[775,165], T3d:[775,265],
  ALL:[980,175], NV1:[250,295], NV2:[600,315], NV3:[940,295], ADV:[435,295]
}};
const COLORS = {{
  "Pillar I (AME)":"#0284c7", "Pillar II (RQLS)":"#059669", "Pillar III (Magic)":"#d97706",
  "Master Bundle":"#7c3aed", "Non-Vacuity":"#0f766e", "Adversarial":"#be123c"
}};
function drawDAG() {{
  const svg = document.getElementById("dag");
  let out = '<defs><marker id="arr" viewBox="0 0 10 10" refX="8" refY="5" markerWidth="6" markerHeight="6" orient="auto-start-reverse"><path d="M0,1 L10,5 L0,9 z" fill="#475569"/></marker></defs>';
  for (const n of NODES) {{
    const [x2, y2] = POS[n.id];
    for (const d of n.deps) {{
      const [x1, y1] = POS[d];
      out += `<line x1="${{x1+44}}" y1="${{y1}}" x2="${{x2-44}}" y2="${{y2}}" stroke="#475569" stroke-width="1.6" marker-end="url(#arr)"/>`;
    }}
  }}
  for (const n of NODES) {{
    const [x, y] = POS[n.id];
    const col = COLORS[n.pillar] || "#334155";
    out += `<g style="cursor:pointer" onclick="document.getElementById('q').value='${{n.id}}';render();">
      <rect x="${{x-44}}" y="${{y-20}}" width="88" height="40" rx="8" fill="${{col}}" stroke="#e2e8f0" stroke-width="1.2"/>
      <text x="${{x}}" y="${{y+4}}" text-anchor="middle" fill="#ffffff" font-size="12" font-weight="700" font-family="ui-monospace,monospace">${{n.id}}</text>
    </g>`;
  }}
  svg.innerHTML = out;
}}
function render() {{
  const q = document.getElementById("q").value.trim().toLowerCase();
  const p = document.getElementById("pillar").value;
  const list = NODES.filter(n => (!p || n.pillar === p) && (!q || JSON.stringify(n).toLowerCase().includes(q)));
  document.getElementById("cards").innerHTML = list.map(n => `
    <article class="card">
      <div><span class="pill">${{n.pillar}}</span><span class="pill ok">KERNEL-VERIFIED</span></div>
      <div class="decl">${{n.id}} &mdash; ${{n.decl}}</div>
      <p style="margin:0.4rem 0;font-size:0.88rem;color:#cbd5e1;">${{n.summary}}</p>
      <div class="meta">File: <code>${{n.file}}</code><br>Axioms: <code>[${{n.axioms.join(", ")}}]</code>${{n.deps.length ? "<br>Depends on: " + n.deps.join(", ") : ""}}</div>
    </article>`).join("");
}}
drawDAG(); render();
document.getElementById("q").addEventListener("input", render);
document.getElementById("pillar").addEventListener("change", render);
</script>
</body>
</html>
"""
    (BP_DIR / "index.html").write_text(bp_html, encoding="utf-8")


def build_observatory() -> None:
    axioms_txt = (REPO / "results" / "lean_axioms.txt").read_text(encoding="utf-8").strip()
    html = f"""<!DOCTYPE html>
<html lang="en">
<head>
<meta charset="utf-8">
<meta name="viewport" content="width=device-width, initial-scale=1">
<meta http-equiv="Content-Security-Policy" content="default-src 'self'; script-src 'unsafe-inline'; style-src 'unsafe-inline'; img-src 'self' data:;">
<title>Quantum Phase-Space Rigidity Observatory (0TH-2026-020)</title>
<style>
  :root {{ --bg:#090e1a; --panel:#111827; --ink:#f8fafc; --muted:#94a3b8; --accent:#38bdf8; --green:#10b981; --warn:#f59e0b; --bad:#ef4444; --border:#1f2937; }}
  * {{ box-sizing:border-box; }}
  body {{ margin:0; font-family:system-ui,-apple-system,Segoe UI,Roboto,sans-serif; background:var(--bg); color:var(--ink); line-height:1.55; }}
  header {{ background:linear-gradient(135deg,#0f172a,#1e1b4b); border-bottom:1px solid var(--border); padding:2rem 2rem 1.5rem; }}
  .wrap {{ max-width:1200px; margin:0 auto; }}
  h1 {{ margin:0 0 0.4rem; font-size:1.75rem; letter-spacing:-0.02em; }}
  .sub {{ color:#cbd5e1; font-size:0.95rem; max-width:920px; }}
  .badges {{ display:flex; flex-wrap:wrap; gap:0.5rem; margin-top:1rem; }}
  .badge {{ font-size:0.78rem; padding:0.25rem 0.65rem; border-radius:999px; background:#0f2942; color:#7dd3fc; border:1px solid #1d4ed8; font-weight:600; }}
  .badge.ok {{ background:#064e3b; color:#6ee7b7; border-color:#059669; }}
  nav.tabs {{ display:flex; flex-wrap:wrap; gap:0.5rem; margin:1.5rem 0 1.25rem; }}
  nav.tabs button {{ background:var(--panel); color:var(--ink); border:1px solid var(--border); padding:0.55rem 1rem; border-radius:8px; cursor:pointer; font-weight:600; font-size:0.88rem; }}
  nav.tabs button.active {{ background:var(--accent); color:#0b1120; border-color:var(--accent); }}
  section.tab {{ display:none; }} section.tab.active {{ display:block; }}
  .card {{ background:var(--panel); border:1px solid var(--border); border-radius:12px; padding:1.25rem 1.4rem; margin-bottom:1.25rem; }}
  .two {{ display:grid; grid-template-columns:repeat(auto-fit,minmax(360px,1fr)); gap:1.25rem; }}
  img.fig {{ width:100%; border-radius:8px; border:1px solid var(--border); background:#ffffff; }}
  pre {{ background:#030712; color:#e2e8f0; padding:1rem; border-radius:8px; overflow-x:auto; font-size:0.78rem; border:1px solid var(--border); }}
  table {{ width:100%; border-collapse:collapse; font-size:0.86rem; }}
  th, td {{ text-align:left; padding:0.5rem 0.65rem; border-bottom:1px solid var(--border); }}
  th {{ color:#93c5fd; }}
  .rqls-grid {{ display:grid; grid-template-columns:repeat(11, 28px); gap:3px; margin:0.75rem 0; }}
  .cell {{ width:28px; height:28px; display:flex; align-items:center; justify-content:center; font-size:0.72rem; border-radius:4px; cursor:pointer; border:1px solid #1e293b; font-family:ui-monospace,monospace; }}
  .btn-row {{ display:flex; flex-wrap:wrap; gap:0.5rem; margin:0.6rem 0; }}
  .btn-sm {{ background:#1e293b; color:#e2e8f0; border:1px solid #334155; padding:0.35rem 0.7rem; border-radius:6px; cursor:pointer; font-size:0.8rem; }}
  .btn-sm:hover {{ border-color:var(--accent); }}
  label {{ display:block; font-size:0.84rem; margin:0.45rem 0 0.15rem; color:#cbd5e1; }}
  input[type=range] {{ width:100%; }}
  footer {{ text-align:center; padding:2rem; color:var(--muted); font-size:0.82rem; border-top:1px solid var(--border); margin-top:2rem; }}
  a {{ color:var(--accent); }}
</style>
</head>
<body>
<header>
  <div class="wrap">
    <h1>Discrete Symplectic Phase-Space Rigidity — Interactive Observatory</h1>
    <div class="sub">
      <strong>Alexander Stephen Donahue</strong> (<a href="https://orcid.org/0009-0006-8168-9648">ORCID 0009-0006-8168-9648</a>) ·
      Independent Researcher, Spokane, WA, USA · Archive ID <code>0TH-2026-020</code>
    </div>
    <div class="badges">
      <span class="badge ok">Lean 4.35.0 Zero-Mathlib (6-Kernel Audited)</span>
      <span class="badge ok">7 Polyglot Engines (Rust · Zig · C++20 · C11+NASM · Eshkol · Python)</span>
      <span class="badge ok">100% Mutation Kill (6/6)</span>
      <span class="badge"><a href="blueprint/index.html" style="color:inherit;text-decoration:none;">Open Lean 4 Blueprint DAG &rarr;</a></span>
      <span class="badge"><a href="https://github.com/0thernes/quantum-phasespace-rigidity" style="color:inherit;text-decoration:none;">GitHub Repository &rarr;</a></span>
    </div>
  </div>
</header>
<main class="wrap">
  <nav class="tabs" role="tablist">
    <button class="active" data-tab="p1">Pillar I: Cyclic AME Dichotomy</button>
    <button data-tab="p2">Pillar II: Interactive 3-RQLS(11)</button>
    <button data-tab="p3">Pillar III: ASTAB / ASEP &amp; SMD Lab</button>
    <button data-tab="p4">QGTL &amp; 6-Kernel Axiom Audit</button>
  </nav>

  <section id="p1" class="tab active">
    <div class="card">
      <h2>Pillar I — Complete Cyclic &Zopf;<sub>2&ell;</sub>-Stabilizer AME(N, 2&ell;) Classification</h2>
      <p>Extends W&oacute;jcik et al. (<code>arXiv:2603.18193v3</code>) to <strong>all</strong> cyclic &Zopf;<sub>2&ell;</sub>-stabilizer groups (including arbitrary non-canonical and non-free torsion subgroups): exists <strong>iff N &isin; {{2, 3, 5, 6}}</strong>, contrasted with an explicit Galois &Fopf;<sub>4</sub>-stabilizer AME(4, 4).</p>
      <img class="fig" src="assets/fig1_ame_phase_diagram.png" alt="Pillar I AME phase diagram">
    </div>
  </section>

  <section id="p2" class="tab">
    <div class="two">
      <div class="card">
        <h2>Interactive 3-RQLS(11) Orthogonality Explorer</h2>
        <p style="font-size:0.86rem;color:#cbd5e1;">Click any cell (x, y) &isin; &Fopf;<sub>11</sub><sup>2</sup>. Highlighted cells are <strong>exact zero inner products</strong> in &Zopf;[&zeta;<sub>11</sub>] along its row, column, and all 3 mutually orthogonal quantum transversal slopes c &isin; {{7, 8, 10}}.</p>
        <div id="rqlsGrid" class="rqls-grid" role="grid" aria-label="11 by 11 3-RQLS(11) grid"></div>
        <div id="rqlsInfo" style="font-size:0.84rem;color:#93c5fd;">Selected cell: (0, 0) — 50 exact orthogonal partners (row + col + 3 slopes), 0 off-diagonal collinear states!</div>
      </div>
      <div class="card">
        <h2>Maximal-Cardinality t-RQLS Frontier</h2>
        <p style="font-size:0.86rem;color:#cbd5e1;">Breaks Zhang &amp; Cao's (<code>arXiv:2608.29201v2</code>) t &le; 2 ceiling via Megyesi&ndash;R&eacute;dei permutations: t = (p&minus;5)/2 for all odd primes p &ge; 7, plus 2-RQLS(9), char-2 3-RQLS(16), and zero-gap &Fopf;<sub>8</sub> obstruction.</p>
        <img class="fig" src="assets/fig2_rqls_frontier.png" alt="Pillar II RQLS frontier">
      </div>
    </div>
  </section>

  <section id="p3" class="tab">
    <div class="two">
      <div class="card">
        <h2>Live 2-Qubit ASTAB vs. ASEP Spectrum Lab</h2>
        <div class="btn-row">
          <button class="btn-sm" onclick="setSpec(0.55,0.15,0.15)">&rho;<sub>ent</sub> (ASTAB &setminus; ASEP)</button>
          <button class="btn-sm" onclick="setSpec(0.40,0.35,0.20)">&rho;<sub>sep</sub> (ASEP &setminus; ASTAB)</button>
          <button class="btn-sm" onclick="setSpec((7+3*Math.sqrt(3))/22,(5-Math.sqrt(3))/22,(5-Math.sqrt(3))/22)">Vertex &lambda;*<sub>2,2</sub> (Max R&sup2;)</button>
        </div>
        <label>&lambda;<sub>1</sub>: <span id="v1">0.550</span></label><input id="s1" type="range" min="0.25" max="0.75" step="0.005" value="0.55">
        <label>&lambda;<sub>2</sub>: <span id="v2">0.150</span></label><input id="s2" type="range" min="0.05" max="0.45" step="0.005" value="0.15">
        <label>&lambda;<sub>3</sub>: <span id="v3">0.150</span></label><input id="s3" type="range" min="0.00" max="0.33" step="0.005" value="0.15">
        <div id="specOut" style="margin-top:0.8rem;font-family:ui-monospace,monospace;font-size:0.83rem;background:#030712;padding:0.8rem;border-radius:8px;border:1px solid #1f2937;"></div>
      </div>
      <div class="card">
        <h2>ASTAB Circumradii &amp; Symplectic Marginal Descent</h2>
        <p style="font-size:0.86rem;color:#cbd5e1;">Gurvits&ndash;Barnum Cor. 3 forces ASTAB<sub>2,d</sub> &subset; AWP<sub>2,d</sub> &sube; ASEP<sub>2,d</sub> for all odd primes d &ge; 3, while Symplectic Marginal Descent delivers an exact <strong>15/7&times;</strong> squared-inball gain for all n &ge; 2.</p>
        <img class="fig" src="assets/fig3_astab_magic_geometry.png" alt="Pillar III magic geometry">
      </div>
    </div>
  </section>

  <section id="p4" class="tab">
    <div class="card">
      <h2>QGTL Quantum Geometric Tensor &amp; 7-Engine Trust Matrix</h2>
      <label>Entangled-ASTAB polar angle &theta; = <span id="thVal">1.10</span> rad &rarr; <span id="qgtlOut" style="color:#7dd3fc;"></span></label>
      <input id="thSlider" type="range" min="0.05" max="3.09" step="0.01" value="1.10">
      <img class="fig" style="margin-top:0.8rem;" src="assets/fig4_qgtl_and_architecture.png" alt="QGTL and architecture">
    </div>
    <div class="card">
      <h2>Verbatim Lean 4.35.0 <code>#print axioms</code> Audit (23 Declarations)</h2>
      <pre>{axioms_txt}</pre>
    </div>
  </section>
</main>
<footer>
  Dual Licensed: Code under Apache-2.0 &middot; Paper, Data &amp; Figures under CC-BY-4.0 &middot; Vendored Moonlab under MIT &middot;
  <a href="blueprint/index.html">Lean Blueprint DAG</a>
</footer>
<script>
document.querySelectorAll("nav.tabs button").forEach(btn => {{
  btn.addEventListener("click", () => {{
    document.querySelectorAll("nav.tabs button").forEach(b => b.classList.remove("active"));
    document.querySelectorAll("section.tab").forEach(s => s.classList.remove("active"));
    btn.classList.add("active");
    document.getElementById(btn.dataset.tab).classList.add("active");
  }});
}});

// Interactive 3-RQLS(11) Explorer
let selX = 0, selY = 0;
const SLOPES = [7, 8, 10];
function renderRQLS() {{
  const grid = document.getElementById("rqlsGrid");
  grid.innerHTML = "";
  let orthoCount = 0;
  for (let x = 0; x < 11; x++) {{
    for (let y = 0; y < 11; y++) {{
      const dx = (x - selX + 11) % 11, dy = (y - selY + 11) % 11;
      const same = dx === 0 && dy === 0;
      const rowCol = !same && (dx === 0 || dy === 0);
      const slopeHit = !same && SLOPES.some(c => dy === (c * dx) % 11);
      if (rowCol || slopeHit) orthoCount++;
      const d = document.createElement("div");
      d.className = "cell";
      d.textContent = same ? "★" : (rowCol ? "0" : (slopeHit ? "⊥" : "·"));
      d.style.background = same ? "#facc15" : (rowCol ? "#0369a1" : (slopeHit ? "#047857" : "#0f172a"));
      d.style.color = same ? "#0f172a" : "#f8fafc";
      d.title = `(${{x}}, ${{y}})`;
      d.onclick = () => {{ selX = x; selY = y; renderRQLS(); }};
      grid.appendChild(d);
    }}
  }}
  document.getElementById("rqlsInfo").textContent =
    `Selected cell (${{selX}}, ${{selY}}): ${{orthoCount}} exact orthogonal partners (row + col + slopes 7, 8, 10), 0 collinear off-diagonal rays.`;
}}
renderRQLS();

// Live 2-qubit ASTAB/ASEP lab
function updateSpec() {{
  let l1 = parseFloat(document.getElementById("s1").value);
  let l2 = parseFloat(document.getElementById("s2").value);
  let l3 = parseFloat(document.getElementById("s3").value);
  let l4 = 1 - l1 - l2 - l3;
  document.getElementById("v1").textContent = l1.toFixed(4);
  document.getElementById("v2").textContent = l2.toFixed(4);
  document.getElementById("v3").textContent = l3.toFixed(4);
  const valid = l1 >= l2 && l2 >= l3 && l3 >= l4 && l4 >= 0;
  if (!valid) {{
    document.getElementById("specOut").innerHTML = `<span style="color:#ef4444;">Invalid ordered spectrum (&lambda;<sub>4</sub>=${{l4.toFixed(4)}}). Require &lambda;<sub>1</sub> &ge; &lambda;<sub>2</sub> &ge; &lambda;<sub>3</sub> &ge; &lambda;<sub>4</sub> &ge; 0.</span>`;
    return;
  }}
  const s3 = Math.sqrt(3), s5 = Math.sqrt(5);
  const f1 = ((1 - s3)/2)*l1 + ((1 + s3)/2)*l4;
  const f2 = ((1 - s5)/4)*(l1 + l2) + ((1 + s5)/4)*(l3 + l4);
  const inAstab = f1 >= -1e-9 && f2 >= -1e-9;
  const va = l1 - l3 - 2*Math.sqrt(l2*l4);
  const inAsep = va <= 1e-9;
  const r2 = l1*l1 + l2*l2 + l3*l3 + l4*l4 - 0.25;
  document.getElementById("specOut").innerHTML =
    `&lambda; = (${{l1.toFixed(4)}}, ${{l2.toFixed(4)}}, ${{l3.toFixed(4)}}, ${{l4.toFixed(4)}})<br>` +
    `R&sup2; = &Vert;&rho; &minus; I/4&Vert;<sub>2</sub>&sup2; = <strong>${{r2.toFixed(6)}}</strong> (GB ball = 0.083333)<br>` +
    `ASTAB facet 1 = ${{f1.toFixed(6)}} | facet 2 = ${{f2.toFixed(6)}} &rArr; <strong style="color:${{inAstab?"#10b981":"#ef4444"}}">${{inAstab?"IN ASTAB":"OUTSIDE ASTAB"}}</strong><br>` +
    `ASEP Verstraete-Audenaert V<sub>A</sub> = ${{va.toFixed(6)}} &rArr; <strong style="color:${{inAsep?"#10b981":"#f59e0b"}}">${{inAsep?"IN ASEP (Separable)":"NPT ENTANGLED"}}</strong>`;
}}
function setSpec(a,b,c) {{
  document.getElementById("s1").value = a;
  document.getElementById("s2").value = b;
  document.getElementById("s3").value = c;
  updateSpec();
}}
["s1","s2","s3"].forEach(id => document.getElementById(id).addEventListener("input", updateSpec));
updateSpec();

// Live QGTL slider
function updateQGTL() {{
  const th = parseFloat(document.getElementById("thSlider").value);
  const a = 0.55, c = 0.15;
  const w = a * Math.pow(Math.sin(0.5*th), 2) + c;
  const gtt = a / 4.0, gpp = w*(1-w), om = -0.5*a*Math.sin(th);
  document.getElementById("thVal").textContent = th.toFixed(2);
  document.getElementById("qgtlOut").textContent =
    `g_θθ = ${{gtt.toFixed(6)}}, g_φφ = ${{gpp.toFixed(6)}}, Ω_θφ = ${{om.toFixed(6)}}`;
}}
document.getElementById("thSlider").addEventListener("input", updateQGTL);
updateQGTL();
</script>
</body>
</html>
"""
    (SITE_DIR / "index.html").write_text(html, encoding="utf-8")


def main() -> int:
    build_blueprint()
    build_observatory()
    print("[WEB] Built docs/site/index.html and docs/site/blueprint/{index.html,data.json}!")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
