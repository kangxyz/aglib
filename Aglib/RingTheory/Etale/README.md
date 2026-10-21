# Formal etaleness of actual ring maps

[FormalProperties](FormalProperties.lean), imported as `Aglib.RingTheory.Etale.FormalProperties`, extends `RingHom.FormallyEtale` for actual homomorphisms of commutative rings in the same universe. `iff_formallyUnramified_and_formallySmooth` identifies the formal property with those two algebra-level conditions.

`RingHom.FormallyEtale.stableUnderComposition`, `respectsIso`, `isStableUnderBaseChange` and `holdsForLocalization` supply the corresponding ring-property interfaces. `RingHom.FormallyEtale.localRingHom` preserves formal etaleness for the canonical map between prime localizations, with the actual prime ideals, their prime instances and the equality relating their comap. `RingHom.Etale.formallyEtale` forgets the finite-presentation part of etaleness.

The prime-localization statement concludes formal etaleness. It does not assert finite presentation or etaleness of that localized map. [Scheme stalk etale base change](../../AlgebraicGeometry/Morphisms/Etale/README.md) consumes these generic ring-map operations; their source's scheme application is provenance rather than their mathematical owner. [Regular-local etale comparison](../RegularLocalRing/README.md) separately retains local Noetherian, flat and essentially-finite-type hypotheses for dimension and regularity.

[Polynomial](Polynomial.lean), imported as `Aglib.RingTheory.Etale.Polynomial`, gives `RingHom.Etale.isMaximal_comap_polynomial`. For an actual etale map `g : MvPolynomial (Fin n) K →+* B`, where `K` is any field and `B` any commutative ring in the original common universe, the comap of a maximal ideal is maximal. The argument uses the existing finite-type field-algebra residue result; it imposes no separability or scheme hypothesis. [Etale polynomial stalks](../../AlgebraicGeometry/Stalk/EtalePolynomial.lean) consume this lower algebraic result.

[MilnorPatching](MilnorPatching.lean) defines
`RingHom.Etale.MilnorPatching.EtalePatching` as an explicit universal input,
using the actual fibre-product map and compatible tensor boundary isomorphisms.
This leaf defines the proposition and does not supply a proof of it.

The [finite-free clutching guide](MilnorPatching/README.md) gives a proved
finite-etale split-power case on the actual fibre map, with an explicit stable
retraction, both canonical tensor comparisons and an endpoint-dependent cyclic
client. Projectivity gives finite presentation over an arbitrary fibre base;
joint tensor conservativity proves formal unramifiedness. The universal
arbitrary-component family remains separate.

[Nilpotent lifting](NilpotentLift.md) lifts an actual étale algebra across any
nilpotent ideal of a commutative ring. A finite input algebra has a finite lift,
with the original tensor and quotient comparisons. No Noetherian, Henselian
or completeness hypothesis is required.
