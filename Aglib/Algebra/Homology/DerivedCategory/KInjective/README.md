# K-injective targets in native derived categories

These leaves extend Mathlib's actual `CochainComplex`, `HomotopyCategory` and
`DerivedCategory` objects. Their maps use the original `DerivedCategory.Q`,
`DerivedCategory.Qh` and `quotientCompQhIso`; no localization or complex carrier
is reimplemented. Declarations belong to `CochainComplex` or
`CategoryTheory.Adjunction`.

- [Representatives](Representatives.lean) gives an actual chain representative
  of every derived arrow into a supplied K-injective target, a chain homotopy
  for a supplied equality of such arrows, and a chain factorization up to
  homotopy retaining the specified derived arrow. Every additive functor
  preserves quasi-isomorphisms between K-injective complexes. The lower-bounded
  termwise-injective consequence retains the two separately supplied term
  bounds. Neither exactness of the functor nor an upper bound is assumed.
- [Hom](Hom.lean) defines the endpoint-normalized homotopy-to-derived Hom map
  and its additive equivalence when the target is K-injective. Its forward and
  inverse equations retain each actual chain-map image.
- [Map](Map.lean) transports an actual derived arrow into a K-injective target
  through an additive functor. The image need not be K-injective and the functor
  need not be exact. Composition retains K-injectivity of the middle and final
  original targets; the isomorphism result retains it for both endpoints.
- [Adjunction](Adjunction.lean) compares actual derived Hom types through an
  additive adjunction when both the original target `I` and the actual complex
  obtained by applying the right adjoint to `I` are K-injective. It preserves
  both original chain-adjoint equations. This is a target-sensitive Hom
  statement, not an adjunction of globally defined derived functors.

The ordinary degreewise adjunction is lower at
[HomologicalComplex/Adjunction](../../HomologicalComplex/Adjunction.lean).
The actual cochain homotopy adjunction and quotient unit/counit equations are at
[HomotopyCategory/Adjunction](../../HomotopyCategory/Adjunction.lean).
`Hom` uses only Mathlib's K-injective localization theorem and Hom congruence;
`Map` also imports `Representatives`; `Adjunction` imports `Hom` and the lower
homotopy adjunction. Object, morphism and derived-model universes remain the
independent universes of the original interfaces. No global
`HasDerivedCategory` instance is added.

The present consumers are the existing general section/direct-image model and
open-restriction injective-comparison code being migrated from Quillen. Source
identity and selected ranges are recorded in the leaves. This wave extracts
`Quillen/Algebra/Homology/{KInjectiveRepresentatives,KInjectiveHom,KInjectiveMap,Adjunction}.lean`
from frozen dirty Quillen `6db56ddd3fdb898ef5de29d5fe51a0c61f9ba116`, with
native namespace and dependency changes only.
