# Henselian residue sections

[HenselianResidue](HenselianResidue.lean) lifts an actual residue-field point
of a finite etale scheme over a Henselian local ring to a unique section of
that same scheme. The namespace is `Scheme.FiniteEtale.HenselianResidue`.

For `p : X ⟶ Spec R`, with `IsFinite p` and `Etale p`, the input is the
specified morphism `t : Spec (IsLocalRing.ResidueField R) ⟶ X` and its
triangle `t ≫ p = Scheme.LocalRing.residueSpecMap R`. The theorem
`existsUnique_section_lift` produces a unique `s : Spec R ⟶ X` satisfying
both original equations:

```text
s ≫ p = 𝟙 (Spec R)
Scheme.LocalRing.residueSpecMap R ≫ s = t.
```

`liftResiduePoint` chooses this section. Its `over`, `restrict`, and `unique`
lemmas retain these exact equations. The residue map is the native
[residue-spectrum map](../../Spec/ResidueFiber.lean), induced by
`IsLocalRing.residue R`; a replacement residue embedding is not supplied.

The only ring assumptions are `CommRing R` and `HenselianLocalRing R`.
In particular, the original Henselian Noetherian DVR setting is a
specialization. The result adds no completeness, excellence, characteristic,
or proper-comparison assumption.

The lower [Henselian etale algebra API](../../../RingTheory/Henselian/Etale.lean)
proves bijectivity of the literal map
`f ↦ (Algebra.ofId R (IsLocalRing.ResidueField R)).comp f` from
`A →ₐ[R] R` to `A →ₐ[R] IsLocalRing.ResidueField R` for every etale
`R`-algebra `A`. It chooses the native standard-etale chart at the kernel of
the given residue point, lifts its simple root by the native Hensel theorem,
and proves uniqueness through the same localization. The scheme proof uses
the given cover's actual affine coordinates and the canonical
[`isoSpec_inv_over` triangle](../../AffineScheme/BaseChangeCoordinates.lean).

The [focused client](../../../../AglibTest/HenselianResidue.lean) includes the
original Noetherian DVR specialization, the literal residue triangle, and
the identity cover's section.

The equivalence of the full finite-etale categories under residue base
change remains a separate endpoint. Lifting maps into every finite etale
target algebra requires more than this target-`R` section result. This API
does not construct `ProperHenselianComparison R`, a comparison for arbitrary
proper schemes, or a purity or Picard/Hilbert representability supplier.
