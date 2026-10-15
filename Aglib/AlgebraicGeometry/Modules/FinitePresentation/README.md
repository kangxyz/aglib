# Actual finite presentations and transport

[Basic](Basic.lean), imported as `Aglib.AlgebraicGeometry.Modules.FinitePresentation.Basic`, defines `Scheme.Modules.finitePresentation` and `FinitePresentation` from genuine finite local generators and relations. `finitePresentation_of_presentation` turns an actual finite presentation into the local property; a finite local basis gives one with no relations.

`finitePresentation_map_isFinite` transports an actual presentation through a colimit-preserving module-sheaf functor with a supplied unit comparison. Generator/relation index sets are unchanged; coefficient sheafification and universe assumptions remain those in the source. [Transport](Transport.lean) supplies the general slice/site transport, and [AffineTransport](AffineTransport.lean) moves an actual affine presentation to the corresponding open slice.

[Locality](Locality.lean) gives restriction, over/restriction and actual open-cover finite-presentation results, without a locally Noetherian coherent-category dependency. The open immersion/cover and finite presentation data remain explicit.

[Noetherian](Noetherian.lean) supplies `Scheme.Modules.exists_finite_presentation_tilde` and `finitePresentation_tilde` for a finite module over a Noetherian commutative ring. `Scheme.Modules.QuasiCoherent.affineFiniteSheaf_exists_presentation` constructs an actual finite presentation from the affine finite-sheaf predicate over such a ring. `affineLocallyFiniteType_finitePresentation` extends this to the actual affine-open cover of a locally Noetherian scheme. These constructions require no coherent category, flatness or nontrivial-ring premise.

Focused imports are these five leaves. Quasicoherent finite-type detection, arbitrary pullback, [finite local freeness](../LocallyFree/README.md) and the later [coherent specialization](../Coherent/README.md) consume these lower constructions. Finite presentation and finite type are not identified by their names alone.
