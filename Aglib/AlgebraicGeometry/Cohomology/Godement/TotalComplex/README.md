# Godement total exactness and bounded augmentation

[Basic](Basic.lean), imported as `Aglib.AlgebraicGeometry.Cohomology.Godement.TotalComplex.Basic`, constructs `Scheme.Modules.Godement.godementResolutionInt`, `godementTotal` on ordinary integer complexes and `godementTotalPlus` on actual bounded-below objects.

[Exactness](Exactness.lean) gives `godementResolutionInt_shortExact`, `godementTotal_shortExact` and degreewise-monomorphism preservation. The last two statements concern categorical exactness in the ordinary complex category, including unbounded objects. They do not assert that every unbounded total augmentation is a quasi-isomorphism.

[QuasiIso](QuasiIso.lean) gives `godementTotalUnit_quasiIso_of_isStrictlyGE` for an explicit `[K.IsStrictlyGE a]`. `godementTotalPlusUnit` and the Plus quasi-isomorphism map results retain actual bounded-below membership. Their stalk homotopy uses the original total differential and sign normalization.

[Naturality](Naturality.lean), [PushforwardQuasiIso](PushforwardQuasiIso.lean) and [NatTransQuasiIso](NatTransQuasiIso.lean) propagate the original bounded-below quasi-isomorphism/unit and componentwise-QI data through the actual total-image/reassociation maps. They do not grant arbitrary ordinary pushforward preservation of every quasi-isomorphism.

Consumers are [D+ calculation](../DerivedPushforward/README.md), section spans, tensor/derived projection and flat-base-change unit diagrams. Exactness, lower-bound augmentation and unit-isomorphism premises remain separate.

[Carrier](Carrier.lean), imported as `Aglib.AlgebraicGeometry.Cohomology.Godement.TotalComplex.Carrier`, supplies `Scheme.Modules.Godement.totalPlusCompιIso` for the actual bounded-below totalization and its ordinary-cochain inclusion. `compTotalPlusCarrierIso`, `resolvedContractionCompιIso` and `precompResolvedContractionCompιIso` keep the original total and composed-functor carrier comparisons. The resolved comparisons allow arbitrary additive module-sheaf functors and coefficients, and retain any supplied carrier isomorphism for precomposition. These are actual underlying-object comparisons; they supply no contraction isomorphism or finite-local-freeness assertion.
