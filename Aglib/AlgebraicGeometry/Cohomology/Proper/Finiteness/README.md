# Unconditional proper finiteness over a Noetherian affine base

[Finiteness](../Finiteness.lean) proves the following for an arbitrary
commutative Noetherian ring `R`, an actual proper morphism
`f : X ⟶ Spec R`, and an actual coherent coefficient:

- `proper_closed_derivedSingle_coherent R f j M hM k` gives coherence of
  every native homology sheaf of the installed `R(j ≫ f)` on the native
  integer single `M[k]`, for every actual closed immersion `j : W ⟶ X`.
- `proper_derivedSingle_coherent R f M hM k` is the original proper
  direct-image specialization, in every integer single placement.
- `proper_higherDirectImage_coherent R f M hM q` gives coherence of the
  unchanged native `((Modules.pushforward f).rightDerived q).obj M`.
- `moduleCohomology_finite_of_proper R f M hM q` proves finiteness of the
  unchanged `Sheaf.H.{u + 1}` with its original structural `R`-action
  through `f.appTop` and `ΓSpecIso`. It uses the original affine
  higher-image/section-cohomology comparison.

The proof has no Chow, proper-finiteness, support-induction or cohomology
theorem family as a premise. It internally performs well-founded induction
on closed subsets `Z` of the fixed Noetherian ambient `X`. Its strengthened
predicate quantifies every actual closed `j : W ⟶ X` with range in `Z`,
every coherent coefficient on `W`, and every integer single placement.
For nonempty `W`, the proved coefficient-independent Chow modification
supplies one dense open `U`, an isomorphism over it, and both bounded
coherent modification images. The image `j(Uᶜ)` is closed and strictly
smaller than `Z`: a point in dense `U` maps into `Z` but is excluded from
the boundary image by injectivity of `j`. The induction hypothesis thus
applies to every actual closed thickening of that boundary in `W`.

The [support step](../SupportInduction/README.md) uses the original
ordinary modification map and actual distinguished triangle, retaining
the possible cone degree `-1`. Each supported coherent homology sheaf
descends directly to a positive ideal-power thickening. The sole native
finite Postnikov argument controls the derived cone image, and the
original `derivedPushforwardPlusCompIso` identifies the middle image.
Empty sources are handled by zero stalks. No nonempty-source,
nonempty-base, nontrivial-ring, relative-flatness, reducedness or
integrality premise is imposed. No prime filtration, Leray spectral
sequence or separate derived cohomology model is introduced.

The exact final source passed with receipt `1792122455291704000-46222`
in 3.2 seconds at the default budget. The independent arbitrary-universe
`ProperFinitenessConsumer.lean` passed with receipt
`1792122531862399000-47043`; all four inspected declarations use only
`propext`, `Classical.choice`, and `Quot.sound`. Source line-length checks
also passed. Only the named leaf and the independent consumer were built.

This is the affine-base Noetherian coherent finiteness tier. General
locally Noetherian targets follow through original open restriction and
quasicoherent locality in a separate consumer. Relative flatness and a
bounded finite-projective replacement are further inputs to a perfect
direct-image model and arbitrary ordinary-coefficient base change;
those conclusions are not inferred from coherent finiteness alone.
