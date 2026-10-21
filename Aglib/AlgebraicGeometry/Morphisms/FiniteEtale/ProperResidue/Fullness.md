# Fullness over a proper flat Henselian DVR model

[Fullness.lean](Fullness.lean) constructs lifts of actual morphisms between
finite étale covers under the literal functor

```lean
Scheme.FiniteEtale.baseChange
  (pullback.fst π (Scheme.LocalRing.residueSpecMap R))
```

The endpoint `closedFiber_baseChange_full_of_henselianDVR` has assumptions
`CommRing R`, `IsDomain R`, `IsDiscreteValuationRing R`,
`HenselianLocalRing R`, `IsProper π` and `Flat π`. It applies in any relative
dimension, including proper flat models with nodal closed fibre. No
smoothness, geometric integrality, connectedness, completeness or excellence
assumption is present. DVR hypotheses supply Noetherianity and an actual
nonzero generator of the maximal ideal.

The more general theorem `closedFiber_baseChange_full_of_principal` retains
Noetherianity, Henselianity, a local domain, and an explicit nonzero generator
of the maximal ideal. All structural maps and products use the original
schemes and their native categorical pullbacks.

Combined with [ProperResidue](../ProperResidue.lean), these results give full
faithfulness. They do not give essential surjectivity or an equivalence of
cover categories. Algebraizing an arbitrary finite étale cover of the closed
fibre remains separate. In particular, `ProperHenselianComparison R` is not
inhabited by this result.

## From the graph to a clopen lift

For a residue morphism between two covers, construct its graph inside the
residue base change of their actual product cover. The graph is a
monomorphism of finite étale covers, hence an open immersion with closed
image. Lift this clopen image to the product before restriction.

The categorical base change uses the two-step fibre
`P ×_Y (Y ×_R k)`. The clopen-lifting theorem uses `P ×_R k`. The proof relates
them only through the native `pullbackRightPullbackFstIso` and its literal
first-projection equation. The public functor remains the original two-step
pullback throughout.

The lifted clopen cover has a first projection to the original source cover.
Its residue base change is an isomorphism. The proved
`closedFiber_baseChange_reflectsIsomorphisms` therefore makes that original
projection an isomorphism. Its inverse followed by the second projection
produces a lift of the prescribed morphism; the native graph projection
equations prove exact equality after base change.

## The actual clopen construction

Let `X` be proper and flat over the chosen base, and let `t` be the global
function supplied by a generator of the maximal ideal. A clopen partition of
the closed fibre gives opens `U,V` covering `X`: remove the opposite closed
part in each case. Their overlap avoids the closed fibre, so `t` is invertible
there.

For each `n`, use the actual module-sheaf cokernel of multiplication by
`t^(n+1)` on `O_X`. The image of one on `U` and zero on `V` glue, because the
cokernel vanishes on the overlap. Sheaf uniqueness proves compatibility of
these sections under the native cokernel maps. No compatible section family
is assumed.

Flatness supplies monicity of all the scalar powers. Proper coherent
cohomology finiteness supplies finite original `H¹`. Naturality of the actual
connecting maps gives

```text
δ₀(y₀) = t^n δₙ(yₙ),       t^(n+1) δₙ(yₙ) = 0.
```

Noetherian stabilization of power torsion forces `δ₀(y₀)=0`. Exact degree-zero
cohomology lifts the patch to a global function `a`. Its local classes are
zero or one, so the class of `a²-a` vanishes in the first scalar cokernel.
Evaluation preserves the kernel sequence on every open; consequently this
vanishing is actual divisibility by `t`, including on global sections.
Thus `a` determines an idempotent modulo the maximal ideal in the finite
algebra `Γ(X,O_X)`.

[`FiniteAlgebraIdempotents`](../../../../RingTheory/Henselian/FiniteAlgebraIdempotents.lean)
lifts that prescribed idempotent to a global idempotent `e`. The construction
uses the actual finite global-section algebra and the original quotient map.
The local divisibility equations show that `e` evaluates to one on the chosen
closed-fibre part and zero on its complement. Its actual basic open is the
required clopen lift.

The proof uses finite original `H⁰` and `H¹`, exact scalar cokernels, and
Henselian idempotent lifting. It does not assume an isomorphism or surjectivity
of `Γ(X)/mΓ(X) → Γ(X_k)`, formal functions, a proper section-lifting family,
or the desired fullness or cover equivalence.
