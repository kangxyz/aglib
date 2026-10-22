# The literal global functions of projective space

`Aglib.AlgebraicGeometry.ProjectiveSpace.GlobalFunctions` computes the actual
structural coefficient map for a commutative ring `R` and finite nonempty
coordinate type `I` in the native geometric universe:

```text
(toSpec R I).appTop.hom.comp (Scheme.ΓSpecIso (.of R)).inv.hom
  : R →+* Γ(ProjectiveSpace R I, ⊤).
```

`globalFunctionsCoefficient_bijective R I` proves this exact map bijective.
`globalFunctionsRingEquiv R I` is an actual ring equivalence with that literal
forward map; `globalFunctionsRingEquiv_toRingHom` is reflexive. The two inverse
cancellation formulas recover both the original coefficient and the original
global function under this same structural map.

The required projective-line case is obtained directly with
`I := ULift.{u} (Fin 2)`. The proof has no field, reducedness, nontriviality,
normality or Noetherian premise. Nonemptiness concerns the coordinate index;
no point of the projective scheme is chosen. The zero-ring case, where the
projective scheme is empty, remains included.

The proof uses the native degree-zero homogeneous polynomial ring comparison,
the original homogeneous-section equivalence, and the actual zero-twist/unit
module isomorphism. On every original coordinate chart, the image of `C r`
under these maps equals the restriction of the original structural constant,
by `constant_restriction`. This identifies the composite section bijection
with the literal structural ring map. `RingEquiv.ofBijective` then retains
its original additive and multiplicative structure and forward coefficient
square. No global-functions equality is assumed as a premise.
