# Formal etaleness of actual ring maps

[FormalProperties](FormalProperties.lean), imported as `Aglib.RingTheory.Etale.FormalProperties`, extends `RingHom.FormallyEtale` for actual homomorphisms of commutative rings in the same universe. `iff_formallyUnramified_and_formallySmooth` identifies the formal property with those two algebra-level conditions.

`RingHom.FormallyEtale.stableUnderComposition`, `respectsIso`, `isStableUnderBaseChange` and `holdsForLocalization` supply the corresponding ring-property interfaces. `RingHom.FormallyEtale.localRingHom` preserves formal etaleness for the canonical map between prime localizations, with the actual prime ideals, their prime instances and the equality relating their comap. `RingHom.Etale.formallyEtale` forgets the finite-presentation part of etaleness.

The prime-localization statement concludes formal etaleness. It does not assert finite presentation or etaleness of that localized map. [Scheme stalk etale base change](../../AlgebraicGeometry/Morphisms/Etale/README.md) consumes these generic ring-map operations; their source's scheme application is provenance rather than their mathematical owner. [Regular-local etale comparison](../RegularLocalRing/README.md) separately retains local Noetherian, flat and essentially-finite-type hypotheses for dimension and regularity.

[Polynomial](Polynomial.lean), imported as `Aglib.RingTheory.Etale.Polynomial`, gives `RingHom.Etale.isMaximal_comap_polynomial`. For an actual etale map `g : MvPolynomial (Fin n) K →+* B`, where `K` is any field and `B` any commutative ring in the original common universe, the comap of a maximal ideal is maximal. The argument uses the existing finite-type field-algebra residue result; it imposes no separability or scheme hypothesis. [Etale polynomial stalks](../../AlgebraicGeometry/Stalk/EtalePolynomial.lean) consume this lower algebraic result.

[MilnorPatching](MilnorPatching.lean) defines the original universal proposition
`RingHom.Etale.MilnorPatching.EtalePatching`, using the actual fibre-product map
and compatible tensor boundary isomorphisms. Its
[FinitePresentation](MilnorPatching/FinitePresentation.lean) leaf proves
`etale_fiberMap` and supplies `etalePatching : EtalePatching` for the full
original seven-map family in one universe: the boundary map `f` is surjective,
the two component maps are etale, and the supplied tensor equivalences retain
their original boundary formulas. There is no finite-module, Noetherian,
flatness-of-`g`, output-flatness, output-finite-presentation or input-patching
premise.

The [clutching guide](MilnorPatching/README.md) records the general component
reconstruction, flatness and finite-presentation route. The finite-free
split-power theorem remains a separate concrete result with an explicit stable
retraction, both canonical tensor comparisons and an endpoint-dependent cyclic
client.

[Nilpotent lifting](NilpotentLift.md) lifts an actual étale algebra across any
nilpotent ideal of a commutative ring. A finite input algebra has a finite lift,
with the original tensor and quotient comparisons. No Noetherian, Henselian
or completeness hypothesis is required.

[PolynomialSystemChart](PolynomialSystemChart.lean) constructs the quotient of a finite square polynomial
system localized at its native Jacobian. It proves this chart is etale rather
than assuming etaleness. The native variable-row, equation-column matrix is
the transpose of the usual Jacobian. Explicit points preserve the original
coefficient map and coordinates. This is a nonsingular chart, not Artin
approximation or general desingularization.

## Points with local targets

[LocalPoints](LocalPoints.lean), imported as
`Aglib.RingTheory.Etale.LocalPoints`, proves
`Algebra.Etale.residue_comp_injective`. For an etale `R`-algebra `B` and any
local commutative `R`-algebra `T`, two maps `B →ₐ[R] T` agree if their composites
with the actual residue map of `T` agree. The base, source, and target have
independent universes. Neither the base nor the target is assumed Henselian;
no Noetherianity, finite-module, or nilpotent-maximal-ideal assumption is used.

The proof passes to a native standard-etale chart at the residue point and
uses simple-root uniqueness in the local target. It proves injectivity only,
not existence of a lift. [Henselian quotient lifting](../Henselian/EtaleQuotientLifting.lean)
uses this uniqueness to preserve a point modulo an arbitrary proper ideal.

## Detection from adic reductions

[Adic/LocalCriterion](Adic/LocalCriterion.lean) proves
`Algebra.etale_of_etale_quotient_pow`: a finite commutative algebra over a
Noetherian local ring is etale when every positive reduction modulo powers
of a proper ideal is etale over its quotient ring. The ideal need not be
maximal, and completeness is not required. [Adic/BaseChange](Adic/BaseChange.lean)
retains the native tensor cancellation maps and applies this criterion after
scalar extension to a Noetherian local target where the extended ideal is
proper. The finite-etale construction uses it to detect etaleness of the
actual finite algebra on its good opens.

## Finite-étale descent to coefficients and filtered stages

[FiniteDescent](FiniteDescent.lean), imported as
`Aglib.RingTheory.Etale.FiniteDescent`, proves
`Algebra.Etale.exists_subalgebra_fg_of_finite`. Given commutative rings
`R : Type w`, `A : Type u`, `B : Type v`, an `R`-algebra structure on `A`,
and a finite étale `A`-algebra `B`, it constructs a finitely generated
`R`-subalgebra `A₀` of `A` and a finite étale `A₀`-algebra `B₀ : Type u` with

```lean
Nonempty (B ≃ₐ[A] A ⊗[A₀] B₀)
```

The three input universes are independent. The construction retains a finite
étale presentation and the integral equations of its generators. It does not
assume that `A` is Noetherian or finitely generated over `R`.

[Filtered-colimit descent](../../Algebra/Category/Ring/Descent/FiniteEtale.lean),
imported as `Aglib.Algebra.Category.Ring.Descent.FiniteEtale`, proves
`Algebra.Etale.exists_finite_model_of_isColimit` and its `_above` variant.
For an actual filtered `F : I ⥤ CommRingCat.{u}`, specified colimit cocone `c`,
and finite étale `c.pt`-algebra `B : Type v`, the conclusion is a finite étale
`Bᵢ : Type u` at an original stage and an algebra equivalence
`c.pt ⊗[F.obj i] Bᵢ ≃ₐ[c.pt] B`, using the algebra structure induced by
`c.ι.app i`. The index and hom universe are `u`. The `_above` form also returns
an arrow from any prescribed initial stage. No flatness or injectivity of
the transition maps is imposed. The
[scheme-limit object descent](../../AlgebraicGeometry/Morphisms/FiniteEtale/Descent/LimitObjects.lean)
uses these lower algebraic constructions.
