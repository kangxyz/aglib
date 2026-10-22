# Proper henselian local comparison

Import `Aglib.AlgebraicGeometry.Morphisms.FiniteEtale.ProperHenselian.General`
for the comparison between finite-étale covers of a proper scheme over a
henselian local ring and covers of its closed fibre. All declarations below
belong to `AlgebraicGeometry.Scheme.FiniteEtale`.

Let `R : Type u` be a commutative henselian local ring and let
`f : X ⟶ Spec (.of R)` be proper, with `X : Scheme.{u}`. Write

```lean
baseChange (pullback.fst f (LocalRing.residueSpecMap R))
```

for the original closed-fibre restriction functor.

| Declaration in [General.lean](General.lean) | Result |
|---|---|
| `properHenselian_baseChange_essSurj f` | Every closed-fibre cover lifts to an actual finite-étale cover of `X`. |
| `properHenselian_baseChange_isEquivalence f` | The displayed restriction functor is an equivalence. |
| `properHenselianEquivalence f` | An explicit equivalence with the displayed functor as its forward functor. |
| `properHenselianEquivalence_functor f` | The forward-functor equality, proved by `rfl`. |
| `properHenselianComparison` | The existing `ProperHenselianComparison R` proposition. |

These statements require no Noetherian, finite-presentation, completeness,
flatness, excellence, domain, or projectivity hypothesis beyond the stated
properness and henselian locality. They concern local rings and their residue
fields; a general nonlocal henselian-pair statement is a separate interface.

[Noetherian.lean](Noetherian.lean) provides the named
`properNoetherianHenselian_baseChange_essSurj`,
`properNoetherianHenselian_baseChange_isEquivalence`, and
`properNoetherianHenselianEquivalence` specializations. Its lower theorem
`properHenselian_baseChange_essSurj_of_finitePresentation` works over an arbitrary
henselian local ring with the explicit hypothesis
`[LocallyOfFinitePresentation f]`. The Noetherian specialization obtains that
hypothesis from properness.

The construction uses an actual
[proper finite-presentation approximation](../../../Approximation/Proper/FiniteType.lean)
over the unchanged base. The native system has the original scheme as its
limit, with closed transition maps and projections. Finite-étale object
[descent](../Descent/LimitObjects.lean) lifts a closed-fibre cover through one
stage, and the finite-presentation theorem lifts the stage cover.
[Approximation.lean](Approximation.lean) and
[ApproximationSystem.lean](ApproximationSystem.lean) expose these conditional
consumers of a specified limit or approximation system.

The finite-presentation theorem descends the proper scheme to a finite-type
arithmetic model and the prescribed residue-field cover to a selected geometric
local henselization. The
[geometric-local comparison](../ProperGeometricLocal.lean) covers finite-type
algebras over an arbitrary field or a characteristic-zero DVR, at any prime.
The coefficient algebra may have zero divisors and need not be flat. The
[base-change lifting theorem](../ProperGeometricBaseChange.lean) retains the
original coefficient map into the henselian local target.

Finally, [universal essential surjectivity](../ProperResidue/EssentialSurjectivity.lean)
lifts a closed-fibre graph over the product of two covers. Closed-fibre
reflection of isomorphisms makes its first projection invertible, giving
fullness. This argument requires essential surjectivity for every proper
scheme over the same base, rather than for only the chosen scheme.
