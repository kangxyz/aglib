# Affine nilpotent object lifts

[Existence.lean](Existence.lean) proves essential surjectivity of the literal
functor

```lean
Scheme.FiniteEtale.baseChange
  (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I)))
```

for any commutative ring `R` and nilpotent ideal `I : Ideal R`. The theorem is
`Scheme.FiniteEtale.Nilpotent.quotient_baseChange_essSurj`. It does not require
locality, Henselianity, Noetherianity or completeness.

Given an actual finite étale cover `Y` of `Spec (R ⧸ I)`, its source is affine.
The original global-section algebra is finite and étale over `R ⧸ I`.
[`Algebra.Etale.exists_finite_nilpotent_lift`](../../../../RingTheory/Etale/NilpotentLift.lean)
constructs an actual finite étale `R`-algebra `A` and a tensor reduction
isomorphism. Taking spectra and transporting along the original source's
`isoSpec` gives the pullback square in `exists_spec_quotient_pullback`:

```text
Y.obj.left  →  Spec A
    ↓            ↓
Spec(R/I)  →   Spec R.
```

The left edge is literally `Y.obj.hom`. The lower edge is the original
quotient ring map under `Spec.map`. `exists_quotient_baseChange_iso` packages
the square as an isomorphism over the same quotient spectrum. The forward
object is the native `pullback.snd`, and `quotient_baseChange_map_fst` records
the original first-projection equation for morphisms.

This is the affine object-existence step used by the [global nilpotent
equivalence](../Nilpotent.md), which constructs the scheme cover and its
finite étale structure by gluing. A compatible tower over all powers of
the maximal ideal still needs proper algebraization. The file proves
neither essential surjectivity for a general proper closed fibre nor a
proper-Henselian equivalence. The separate [Fullness](Fullness.lean) theorem
remains fully faithful over its stated proper-flat Henselian-DVR scope.
