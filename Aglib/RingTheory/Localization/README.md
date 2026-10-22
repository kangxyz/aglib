# Module length under localization

[LengthSurjective](LengthSurjective.lean) exports `Localization.localMap_surjective` and `Module.length_localization_of_surjective`. A surjective map of commutative scalar rings remains surjective at corresponding prime localizations. For a module with compatible source/target actions and scalar tower, the actual localized modules have equal extended-natural lengths. No finite-length assumption is required.

[IteratedModuleLength](IteratedModuleLength.lean) gives `Module.iterated_localized_length`, comparing a second prime localization with localization at its contracted prime, again without a finite-length premise. Its support criteria identify the actual contracted support. [LengthFlatBaseChange](LengthFlatBaseChange.lean) gives `Module.localized_length_flat_baseChange`, retaining flatness and the specified contracted prime for the flat-local length formula.

The three length-comparison imports are `Aglib.RingTheory.Localization.LengthSurjective`, `.IteratedModuleLength` and `.LengthFlatBaseChange`. Principal scalar-homology transport and prime-filtration/local multiplicity calculations are concrete consumers. Equality of extended-natural lengths must not be replaced by an unstated finite-length conclusion.

[ModulePresentation](ModulePresentation.lean), imported as `Aglib.RingTheory.Localization.ModulePresentation`, transports actual linear equivalences and cyclic presentations to principal neighbourhoods and identifies the literal localized principal ideal. It retains the source module-finiteness premise where used.

[PrincipalQuotientLength](PrincipalQuotientLength.lean) owns the generic
prime-quotient factor comparison in namespace `Module`. The source ideal may be
arbitrary where stated, while the target ideal is prime. See also the focused
[away-localization guide](Away/README.md).

[HomEvaluation](HomEvaluation.lean) supplies
`IsLocalizedModule.of_homEvaluation`. For a finitely presented source module,
evaluation-compatible linear equivalences transfer the native Hom-localization
theorem to the specified original modules and map. The target need not be
finite, and no Noetherian hypothesis is imposed. Its current consumer is
coherence of the actual scheme internal Hom.

[FractionBase](FractionBase.lean), in namespace `FractionBaseLocalization`,
localizes a commutative `R`-algebra `B` at the images of the nonzero elements
of a domain `R`. Its `BaseLocalized R B` carries the native `FractionRing R`
action, with independent ring universes. For compatible coefficient maps
`k → R → B`, the images of any original `k`-algebra generators generate the
localized algebra over `FractionRing R`; finite type over `k` suffices.
For a prime `q` with zero contraction to `R`, `selectedPrime` is its actual
extension, `selectedPrime_comap` recovers `q`, and `localEquiv` identifies the
selected prime localization with `Localization.AtPrime q` as a `B`-algebra.
`quotientMap` and `quotientMap_comp_algebraMap` retain the original quotient
classes and coefficient square. The
[geometric-local finite-origin construction](../Henselian/GeometricLocalFiniteOriginModel.lean)
uses these maps after choosing residue transcendence parameters.

[SeparatingParameters](SeparatingParameters.lean) localizes a residual source
subalgebra at the nonzero polynomials in a supplied algebraically independent
parameter family. Algebraicity over the actual parameter field makes its
canonical point into the given fraction field bijective.
[SeparatingParameterField](SeparatingParameterField.lean) transports finite
separability through the specified coefficient equivalence and proves its
fraction-map triangle. [ProjectedResidue](ProjectedResidue.lean) identifies
the extended original residue kernel and its quotient, retaining the explicit
denominator-image equality. The
[projected DVR centre](../DiscreteValuationRing/ParameterProjectedResidue.lean)
supplies that equality from its original coefficient and residue maps.
