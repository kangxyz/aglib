# Noetherian affine coherent exactness

The lower actual affine finite-type quasicoherent category and finite-module equivalence are in [QuasiCoherent/Affine](../../QuasiCoherent/Affine/README.md). Here the commutative affine ring is Noetherian for the coherent abelian/exact and finite-relation results.

[Basic](Basic.lean) constructs `Scheme.Modules.Coherent.affineCoherentExactStructure`. [Comparison](Comparison.lean) gives `coherentToAffineExact` and `affineToCoherentExact`; [Exact](Exact.lean) gives the actual inclusion and sheaf exactness comparison; [GlobalSections](GlobalSections.lean) separately owns `Scheme.Modules.Coherent.globalSectionsExact R` for a Noetherian ring, independently of any ideal. The selected exact structure agrees with ambient module-sheaf exactness, rather than merely with an abstract transported category.

[FinitePresentation](FinitePresentation.lean) produces actual finite presentations of tilde sheaves from finite modules over a Noetherian ring. [RestrictionExact](RestrictionExact.lean) gives `affinePrincipalRestrictionExact` and identifies its kernel with actual supported-away objects. [Support](Support.lean) supplies the supported coherent exact structure; the lower closed-support theorem itself has no Noetherian hypothesis. [Property](Property.lean) provides the source interface into the general finite-type property.

Focused imports are these `Aglib.AlgebraicGeometry.Modules.Coherent.Affine` leaves. Consumers are global coherent exactness, finite/closed direct image and the actual support categories. Object-preserving affine comparisons are not strengthened to unconditional coherent abelian structures by dropping the source hypotheses.
