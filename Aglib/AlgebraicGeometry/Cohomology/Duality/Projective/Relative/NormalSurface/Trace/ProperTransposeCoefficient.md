# Coefficient normalization of the original proper Serre transpose

`ProperTransposeCoefficient.lean` proves one general bridge. It creates no new
transpose, canonical module, canonical trace, derived unit or global-sections
comparison.

## Complete inputs

The original base is a regular local domain `R : Type u`. Both schemes are
integral, have normal stalks and topological dimension at most two, and carry
actual closed embeddings into projective spaces over R. Both structural maps
are dominant. Their original triangle with `b : Y → X` is retained. The
coordinate equivalences to `Fin (nX+1)` and `Fin (nY+1)` and both original
`genericImageBaseMap` finiteness hypotheses are explicit. The morphism b is
proper, as required by the existing ordinary canonical trace.

The module inputs are `MX LX : X.Modules` and `LY : Y.Modules`. Only MX and LY
are required to be quasicoherent and affine-locally finite type. No coherence
hypothesis is imposed on LX. The maps are

```text
C : MX → b_* LY
φ : MX → LX
Ψ : Rb_*(LY[0]) → LX[0]
ΦX : LX → ωX.
```

The complete general input equation is

```text
single(C) ≫ b_*.rightDerivedSingleUnit LY ≫ Ψ = single(φ).
```

This is an input to the general bridge, not an assumed geometric trace square.
An actual one-point consumer must discharge it using its proved derived
coefficient theorem. No such specialization is introduced here.

## Conclusion and original maps

Let ΦY be the existing `normalSurfaceProperSerreTranspose` applied to Ψ and ΦX,
and let τ be the existing `normalSurfaceProperCanonicalTrace`. The theorem
`normalSurfaceProperSerreTranspose_coefficient` concludes

```text
C ≫ b_*.map ΦY ≫ τ = φ ≫ ΦX.
```

The source is exactly MX. In particular, a later raw-form application need not
replace it by its bidual. The proof uses the existing canonical-trace source
functional, native single-unit naturality, naturality of the original
proper-global-sections composition, and the defining Serre-transpose equation.
It closes with the proved bijectivity (hence injectivity) of that same original
coherent-source Serre map on MX, without simplifying an equivalence wrapper.
Only the composition isomorphism is canceled against its inverse. No general
derived unit, raw evaluation or global-sections functor is treated as invertible
or faithful.

The same standard derived-category realizations of the imported Serre and trace
owners are retained, including `HasDerivedCategory.{u+1}` for base modules. No
settings, auxiliary backend or new global instance is installed.

## Scope and status

The original target reached its first normal check in `reupload-own-290` after
61 required supplier successes. Its 9-second target check reported three ordinary
proof-elaboration errors (lines 110, 120 and 127), not an aggregate guard failure.
The repaired owner reached `reupload-own-302` in 7 seconds and reported only
an unused `Category.assoc` simp argument at line 125. This successor removes
that redundant simp argument only; it is not yet natively checked. No prefix
of the earlier failed owner is claimed accepted. It uses explicitly typed
whole-equation transport for the original unit/comparison maps, the associativity
equation followed by the original derived coefficient hypothesis, and injectivity
of the original Serre map. It does not unfold or reconstruct the transpose,
right-derived functor, canonical trace or Serre equivalence producer. No compiler
settings or resource limits are changed, and no resource-cure claim is made.

It does not establish
existence of projective embeddings for arbitrary proper models, a canonical
initial coefficient, a one-point geometric specialization, chain composition,
a uniform scalar or H1 vanishing. In a differential-form application, genuine
global finite-type/coherence suppliers must still be supplied; no local-finite-
type assertion about a stalk map follows from this theorem.

The focused imports are the existing `Cohomology.ProperTranspose` and
`Trace.Proper` owners. The recorded source closure excludes the held affine-form
localization, finite-cover trace, nonflat-composition and optional bidual-
restriction branches. Textual closure evidence is not native readiness.
