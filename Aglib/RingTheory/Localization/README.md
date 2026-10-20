# Module length under localization

[LengthSurjective](LengthSurjective.lean) exports `Localization.localMap_surjective` and `Module.length_localization_of_surjective`. A surjective map of commutative scalar rings remains surjective at corresponding prime localizations. For a module with compatible source/target actions and scalar tower, the actual localized modules have equal extended-natural lengths. No finite-length assumption is required.

[IteratedModuleLength](IteratedModuleLength.lean) gives `Module.iterated_localized_length`, comparing a second prime localization with localization at its contracted prime, again without a finite-length premise. Its support criteria identify the actual contracted support. [LengthFlatBaseChange](LengthFlatBaseChange.lean) gives `Module.localized_length_flat_baseChange`, retaining flatness and the specified contracted prime for the flat-local length formula.

The three length-comparison imports are `Aglib.RingTheory.Localization.LengthSurjective`, `.IteratedModuleLength` and `.LengthFlatBaseChange`. Principal scalar-homology transport and prime-filtration/local multiplicity calculations are concrete consumers. Equality of extended-natural lengths must not be replaced by an unstated finite-length conclusion.

[ModulePresentation](ModulePresentation.lean), imported as `Aglib.RingTheory.Localization.ModulePresentation`, transports actual linear equivalences and cyclic presentations to principal neighbourhoods and identifies the literal localized principal ideal. It retains the source module-finiteness premise where used.

[PrincipalQuotientLength](PrincipalQuotientLength.lean) owns the generic
prime-quotient factor comparison in namespace `Module`. The source ideal may be
arbitrary where stated, while the target ideal is prime. See also the focused
[away-localization guide](Away/README.md).
