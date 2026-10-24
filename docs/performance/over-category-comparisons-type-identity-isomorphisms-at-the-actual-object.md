> [Case index](README.md) · [Methods](../PERFORMANCE.md#conversion-boundaries).
> Commands and status describe the recorded source; [current practice](../PERFORMANCE.md#repair-workflow) remains with the operating guides.

## Over-category comparisons: type identity isomorphisms at the actual object

Measured on 2026-10-24 at Lean 4.34.1, Mathlib `d13f23b`, Aglib base `090956ca`, remote profile
`aglib-picard-endpoint` (8 frontends × 4 threads), in `Picard/Tangent/FieldExtension` and the leaf
that landed as `Picard/Tangent/StructureCohomology`. The measured sources called that leaf
`Picard/Tangent/Endpoint`; at landing only declaration names, the visibility of two lemmas (made
private), one selective `open`, docstrings and line breaks changed.
The matched evidence for the repaired sources is the final unprofiled build
`remote-717b4c731630405ea93470f7a26e8b8b` (source snapshot `058f0165…`): `FieldExtension` 10 s,
`Endpoint` 62 s.

1. `Over.isoMk (Iso.refl _) hw : specOver k k ≅ Over.mk (𝟙 (Spec k))`, where
   `specOver k k = Over.mk (Spec.map (ofHom (algebraMap k k)))`: the `_` elaborates to
   `(specOver k k).left`.
   - Run `remote-5649dc34b6144529a2b7a17e64653b67` (profiled, threshold 500 ms): 89.4 s and
     44.1 s of kernel type checking for the definition, 43 s for a square proved by `rw`; module
     181 s. The run exited 1 on lint of the temporary profiler options, after compiling the
     declarations.
   - Probe `remote-765bd4ba10d34fa7b5a51ee3e445c6f1` (threshold 100 ms): the same definition
     98.4 s + 53.9 s, and with `hw` given as a cheap term 127 s + 59.4 s; the `rfl` facts
     `specOver k k[ε] = Over.mk (dualMap k)`, `(specOverMap fstHom).left = closedPoint k`,
     `ofHom (algebraMap k k) = 𝟙` and `Spec.map (ofHom (algebraMap k k)) = 𝟙` (by `congrArg` and
     `Spec.map_id`) each below 0.1 s.
   - Repair: `Over.isoMk (Iso.refl (Spec (.of k))) ((Category.comp_id _).trans h.symm)` with
     `h : Spec.map (ofHom (algebraMap k k)) = 𝟙`, and squares by `Over.OverMorphism.ext` with
     `Category.id_comp`/`comp_id` terms. Run `remote-92b4010f987b4b49beaf387a00245e3a`: module
     7.4 s, 0.66 s type checking in total; it exited 1 on lint (two long lines) after compiling
     the declarations.
   - Candidate mechanism, not measured: the kernel checks `Iso.refl (specOver k k).left` against
     `(specOver k k).left ≅ (Over.mk (𝟙 _)).left`, compares the two `Over` objects under
     `Comma.left` before reducing the projections, and unfolds `Spec.map` far trying
     `Spec (algebraMap k k) ≡ 𝟙`.
2. `rfl` lemmas equating `Subtype.val` of an element of `tangentKernel F k` with `Subtype.val` of
   an element of `ker F(closedPointOver k)`, for the concrete `F = Pic_{X/k,(fppf)}`.
   - Run `remote-c7f13da6a6ba46778af7cee288da8a16`: `(kernel) excessive memory consumption
     detected` at both lemmas (`Endpoint.lean:194:8` and `:304:8` of that source). The failed run
     also reported two application type mismatches and a parse error, so its 542 s module time is
     not attributed to these lemmas alone.
   - Repair: no `rfl` across the two subtypes. The comparison goes through
     `AddEquiv.addSubgroupCongr` and Mathlib's `addSubgroupCongr_apply`, and the whole `k`- and
     `K`-linear assembly is proved with `F` (and `G`) variables in `Tangent/FieldExtension`, then
     instantiated (`remote-cc8c184928524e7fa660f4dcc0afc396`: `Endpoint` 121 s, exit 0).
   - Candidate mechanism, not measured: the kernel compares the two membership predicates first
     (same head `Subtype.val`), that is `F(specOverMap fst)` with `F(closedPointOver k)`, and
     unfolds the sheafification.
3. Instantiating the generic `K`-side assembly with the Picard data.
   - Probes `remote-4c146b47a6294692ba713cfba980f764` and
     `remote-da373b94e90349d59249baf3551931ea` show about 20 s of kernel checking for the
     instantiating definition itself, independent of a type ascription, of `sorry` for the proof
     arguments and of the presentation of `G` (`fieldBaseChange` or `pullback.snd`), plus about
     10 s for the abstracted proof of the linearity hypothesis of `v_K` and about 2 s for that of
     the base-change compatibility.
   - Repair: one generic constructor `linearEquivTangentKernelOfFieldExtension` instead of three
     concrete declarations (map, bijectivity, equivalence). `Endpoint` 121 s → 62 s
     (`remote-cc8c1849` → `remote-717b4c731630405ea93470f7a26e8b8b`). This is a single change:
     the `Endpoint` input of `remote-cc8c1849` (`fc593050…`) is the WIP commit `4e30622d`, whose
     diff to the final file is only this merge of the `K`-side declarations.
   - Profiled 60 s in `remote-0f92d0be0b82426c9139a03d8caa0da0`: the definition
     1.9 + 10.0 + 1.9 + 20.3 s, the `k`-side definitions 5.2, 2.7 + 5.2 and 5.1 s.
4. Profile reading. In `remote-aeb0ae094dd646faaee42519c771db2a`,
   `remote-16e8ca80517d4ebb8d34a43437531e58` and `remote-0f92d0be…` (profiler thresholds not
   retained; the smallest reported entries are 2.05 s, 0.65 s and 1.88 s), "tactic execution of
   refine" of 32–75 s for theorems right after a heavy definition, and "linting" of 54–90 s at the
   end of the module, were not accounted for by their own traced work.
   - The trace of `remote-59e968f8972442e5b7e53933aa5c58fb` put 32.9 s on one `inferInstanceAs`
     elaboration step whose traced children took 0.16 s (`build.log:1757`, 32.853782 s, children
     0.150683 s and 0.010106 s).
   - In that run each `refine` time matches the kernel checks of the declarations before it
     (32.8 s against 1.85 + 10.2 + 21.4 = 33.5 s; 78.5 s against 75.0 s), and the closing
     `linting` time matches the module's total type checking (94.7 s against 91.8 s). In
     `remote-0f92d0be0b82426c9139a03d8caa0da0` the figures are 41.4 s against 41.7 s, and 54.1 s
     against 55.1 s.
   - Candidate, not measured: these phases wait for the asynchronous kernel checks of the
     preceding declarations.
   - The scratch probe `remote-10c60913b1824b57a20f3911dbe872ef` is no evidence here: it failed to
     synthesize the base-change instances at those `inferInstanceAs` lines.

Rules:

- Type an `Over.isoMk`, and any identity morphism between `left`s, at the actual object, not at the
  `left` of either `Over` object, whenever the two structure maps are not definitionally equal.
- Compare kernels of a concrete presheaf only through generic equivalences (`addSubgroupCongr`) and
  generic lemmas proved with the presheaf a variable.
- Instantiate a heavy generic construction once.
- When a profile shows a large `refine` or closing `linting` time after heavy definitions, compare
  it with the kernel checks of the preceding declarations before attributing it to that tactic.
