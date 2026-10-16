# Actual finite presentations and transport

[Basic](Basic.lean), imported as `Aglib.AlgebraicGeometry.Modules.FinitePresentation.Basic`, defines `Scheme.Modules.finitePresentation` and `FinitePresentation` from genuine finite local generators and relations. `finitePresentation_of_presentation` turns an actual finite presentation into the local property; a finite local basis gives one with no relations.

The arbitrary-site `SheafOfModules.finitePresentation_map_isFinite` lives in [generic presentations](../../../Algebra/Category/ModuleCat/Sheaf/Presentation.lean). It transports an actual presentation through a colimit-preserving module-sheaf functor with a supplied unit comparison, keeping both finite index types. [Generic pushforward](../../../Algebra/Category/ModuleCat/Sheaf/Quasicoherent/Pushforward.lean) supplies the compatible slice/site transport. [AffineTransport](AffineTransport.lean) moves an actual affine presentation to the corresponding open slice.

[Locality](Locality.lean) gives restriction, over/restriction and actual open-cover finite-presentation results, without a locally Noetherian coherent-category dependency. The open immersion/cover and finite presentation data remain explicit.

[Noetherian](Noetherian.lean) supplies `Scheme.Modules.exists_finite_presentation_tilde` and `finitePresentation_tilde` for a finite module over a Noetherian commutative ring. `Scheme.Modules.QuasiCoherent.affineFiniteSheaf_exists_presentation` constructs an actual finite presentation from the affine finite-sheaf predicate over such a ring. `affineLocallyFiniteType_finitePresentation` extends this to the actual affine-open cover of a locally Noetherian scheme. These constructions require no coherent category, flatness or nontrivial-ring premise.

Focused scheme imports are the four named leaves; arbitrary-site presentation transport is imported from its lower owner. Quasicoherent finite-type detection, arbitrary pullback, [finite local freeness](../LocallyFree/README.md) and the later [coherent specialization](../Coherent/README.md) consume these lower constructions. Finite presentation and finite type are not identified by their names alone.
