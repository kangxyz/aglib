# Abelian object properties and resolutions

[Subcategory](Subcategory/README.md) constructs an abelian full subcategory from containing-zero, subobject, quotient and finite-product closure. [SerreClass](SerreClass/README.md) separately derives finite-product closure from a genuine Serre class. The former result does not acquire an extension-closure premise from the latter.

[Injective](Injective/README.md) gives actual kernel short exact sequences of supplied resolutions and comparison of exact-functor Ext maps with actual mapped resolution cycles. These generic statements feed finite-module/coherent structures and scheme Cech/cohomology comparison. Focused imports follow their subfamily source paths.

[Ext1](Ext1/README.md) realizes every degree-one Ext class by a short exact extension with fixed endpoints, and turns equality of classes into an endpoint-preserving isomorphism of extensions. The category is arbitrary abelian, with the stated independent `HasExt` and derived-category universes; no enough-injective or enough-projective premise is added.

[FiniteCoproductFunctor](FiniteCoproductFunctor.lean) supplies finite-limit and finite-colimit preservation for the actual finite coproduct functor in the stated abelian setting. This lower categorical result is used by finite-free sheaf tensor exactness.
