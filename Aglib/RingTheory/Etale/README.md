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
