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

[ExactResolution](ExactResolution.lean) constructs an actual chain comparison
from the exact additive image of a supplied native injective resolution to a
supplied injective resolution of the image coefficient.
`InjectiveResolution.mapCochainComparison_Q_map` retains the inverse image of
the actual mapped source augmentation followed by the original target
augmentation. The map is a quasi-isomorphism, and its original augmentation
square has an actual chain homotopy. The source needs no derived category;
neither category needs enough injectives when both resolutions are supplied.
Preservation of injective objects is not assumed. A subsequent nonexact functor
must still be compared through its original derived unit; the source of this
comparison need not be K-injective.

[ExactResolution/Unit](ExactResolution/Unit.lean) retains these actual maps in
bounded-below complexes. Its literal Q-equation is the same original
augmentation comparison. `mapCochainComparison_rightDerivedUnit` identifies
the image comparison under any subsequent additive functor with the installed
right-derived map through its original unit and inverse mapped augmentation.
Only that subsequent functor's source needs enough injectives; the original
source category still needs neither enough injectives nor a derived category.
No exactness of the subsequent functor or quasi-isomorphism of its mapped
comparison is assumed. Canonical geometric base-change normalization consumes
this unit equation.

[ExactResolution/Ext](ExactResolution/Ext.lean) computes the original
`Ext.mapExactFunctor` on every original cocycle in the supplied resolution.
`mapCochainComparisonCocycle_extClass` identifies it with the target
resolution class obtained by mapping that cocycle and following the actual
comparison. `mapCochainComparisonCocycle_fromSingleEquiv` records the
literal mapped single coordinate and original comparison component. The
native `extEquivCohomologyClass_symm_mk_precomp` also preserves the actual
source morphism as its original single-complex precomposition. The
source and target Ext sizes and the target derived-model universe remain
independent. The source still needs neither a derived category nor enough
injectives; no image term is assumed injective. The geometric resolution
section-tensor comparison consumes these exact class and component formulas.

[Adjunction/InjectiveComplex](Adjunction/InjectiveComplex.lean) proves the
actual right-adjoint image K-injective for every bounded-below complex of
injectives when the left adjoint preserves monomorphisms. The derived Hom
equivalence consequently needs neither K-injectivity as an extra input;
both original chain-adjoint maps are preserved. The pure K-injectivity
supplier uses no derived category or enough-injectives assumption.
