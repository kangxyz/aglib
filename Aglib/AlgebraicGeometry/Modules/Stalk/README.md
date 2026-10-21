# Actual module stalks and detection

[Basic](Basic.lean), imported as `Aglib.AlgebraicGeometry.Modules.Stalk.Basic`, constructs `Scheme.Modules.moduleStalk X x : X.Modules ⥤ ModuleCat (X.presheaf.stalk x)`. It uses the actual abelian-group stalk with its structure-sheaf stalk action; `moduleStalkMap` is the actual induced linear map. `moduleStalkForgetIso` identifies its underlying abelian-group functor with the established stalk functor. No quasicoherence or Noetherian premise is used.

The actual module skyscraper is `Scheme.Modules.moduleSkyscraper X x`. `moduleStalkSkyscraperHomEquiv` identifies stalk-module maps with sheaf maps to this skyscraper, and `moduleStalkSkyscraperAdjunction` supplies their adjunction. Finite-limit preservation and that left-adjoint structure give `moduleStalkExactFunctor` for the actual sheaf and module abelian exact structures. `mono_of_moduleStalk` detects monomorphisms from all module stalks.

[Reflection](Reflection.lean) gives `Scheme.Modules.epi_of_moduleStalk` and `isIso_of_moduleStalk`, together with zero-object and quasi-isomorphism detection on the original stalk maps. [Exactness](Exactness.lean) gives `exact_of_moduleStalk` and `shortExact_of_moduleStalk` for an actual short complex with the stated stalkwise exactness, mono and epi hypotheses. These detection results apply to arbitrary scheme module sheaves.

The [tensor stalk comparisons](../Tensor/Stalk/README.md), [projection formula](../ProjectionFormula/README.md), [Godement construction](../../Cohomology/Godement/README.md) and [open-cover quasi-isomorphism detection](../../Cohomology/Locality/README.md) consume these interfaces. Stalkwise properties remain inputs to detection.

[LocalSpectrum](LocalSpectrum.lean) identifies global sections on the spectrum
of a local ring with the actual closed-point stalk. Its forward map is the
original germ, with scalar restriction along the native closed-point ring
isomorphism. It is natural in the coefficient and requires no quasicoherence.
