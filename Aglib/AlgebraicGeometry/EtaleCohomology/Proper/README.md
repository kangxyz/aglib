# Proper base change

This family owns proper base change for the original higher and bounded-below
derived exchange maps, in namespace
`AlgebraicGeometry.Scheme.EtaleCohomology.Proper`. Its formal and geometric
reducers retain the lower `Proper.Reduction` namespace.
Scheme coefficients use `AbelianSheaf.{u,u+1}`; the derived statements use
the actual bounded-below category `DerivedCategory.Plus`.

## Original proper exchange on locally torsion coefficients

For proper `f : X ⟶ S`, arbitrary `g : S' ⟶ S` and an actual Cartesian square
with maps `f'` and `g'`, [BaseChange](BaseChange.lean) supplies:

- `properHigherBaseChange_isIso`: every original higher exchange component
  is invertible in every natural degree for an internally locally torsion F.
- `properDerivedBaseChange_single_isIso`: the same original derived exchange
  is invertible on the original degree-zero single of F.
- `properDerivedBaseChange_isIso_of_torsion_homology`: the same exchange is
  invertible on every D+ object whose homology sheaves are internally locally
  torsion.

The four supplied derived-category data records and their universes remain
independent. The base, base change and locally torsion coefficient are
arbitrary: the final statements add no uniform annihilator, Noetherian,
constructibility, finite-presentation or coefficient-order-invertibility
condition. The D+ statement retains bounded-below scope and imposes no common
annihilator on its homology sheaves or terms.

[Bounded](Bounded.lean) gives the intermediate original exchange on every
coefficient killed by a supplied positive integer. The actual universal-P1
input is constructed in [Universal/ProjectiveLine](Universal/ProjectiveLine.lean)
from original local and geometric-stalk comparisons. The original factorial
kernel cocone and sheaf-valued sequential higher-image continuity give local
torsion; the native finite Postnikov windows give D+.

## Formal and geometric reduction inputs

| Source | Supplied interface |
| --- | --- |
| [Composition](Reduction/Composition.lean) | Vertical composition and cancellation of invertibility for the original derived mate, and extraction of original higher-exchange components through native transport. |
| [Retracts](Reduction/Retracts.lean) | Invertibility of original derived and higher exchange passes to an actual coefficient retract, retaining its original arrows under both functors. |
| [InjectiveRetract](Reduction/InjectiveRetract.lean) | A faithful left adjoint and enough injectives in its target give a retract presentation for an actual injective source object. Natural-transformation invertibility transfers along that retract. |
| [SurjectivePullback](Reduction/SurjectivePullback.lean) | Original abelian inverse image along an arbitrary surjective scheme morphism is faithful and reflects monomorphisms at value universe `u+1`. |
| [ChowGeometry](Reduction/ChowGeometry.lean) | Every proper scheme over an arbitrary affine base has an actual proper surjection from a scheme closed in standard projective space over that same base, with the original structural equation. |

## Original exchange, composition and retracts

For `f : X ⟶ S`, `f' : X' ⟶ S'`, `g : S' ⟶ S`,
`g' : X' ⟶ X` and `h : f' ≫ g = g' ≫ f`, the map
`derivedBaseChangeMap f f' g g' h` has direction

```lean
derivedDirectImage f ⋙ derivedInverseImage g ⟶
  derivedInverseImage g' ⋙ derivedDirectImage f'
```

For vertically composable squares with `k : Y ⟶ X` and
`k' : Y' ⟶ X'`, let `K` be a bounded-below coefficient on `Y`.
`derivedBaseChangeMap_isIso_vComp` assumes invertibility of the outer
exchange at `(derivedDirectImage k).obj K` and the inner exchange at
`K`, and concludes invertibility for the composite `k ≫ f` at `K`.
`derivedBaseChangeMap_isIso_of_vComp` cancels in the other stated
direction: inner and composite invertibility at `K` give outer
invertibility at that actual derived direct image.
The whole-natural-transformation composition theorem retains the same original
mate. These are formal implications for the specified commuting squares,
without a properness or cartesian hypothesis. The six
`HasDerivedCategory` universes for `S,X,Y,S',X',Y'` remain independent.

`higherBaseChangeMap_isIso_app_of_derived` assumes derived-exchange
invertibility at the original degree-zero single of a coefficient `F` and
concludes invertibility of its original higher-exchange component in every
natural degree. It uses the native source/target and homology transports.
Whole derived-exchange invertibility likewise implies invertibility of the
whole original higher exchange.

The retract theorems apply to a specified `Retract K L` in the actual
bounded-below coefficient category, or `Retract F G` for original abelian
coefficients. Naturality gives an arrow retract of the same exchange:
both functors apply to the original inclusion and retraction. Invertibility at
the larger coefficient then gives invertibility at its retract. These
statements retain the four displayed source/target derived-category universes.

## Injectives and faithful inverse image

The generic `exists_injective_rightAdjoint_retract` assumes an actual
adjunction `L : C ⥤ D`, `R : D ⥤ C`, `L ⊣ R`, with
`L.Faithful` and `EnoughInjectives D`. For an actual injective
`I : C`, it constructs an injective `J : D` and
`Retract I (R.obj J)`.
For a natural transformation on `C`,
`isIso_app_injective_of_rightAdjoint_injectives` transfers invertibility
on right images of all target injectives to invertibility on source injectives.
Injectivity is a hypothesis in the stated source or target category; no
injectivity after scalar forgetting is asserted.

For an arbitrary surjective `f : X ⟶ S`,
`inverseImage_faithful_of_surjective` makes the original functor
`inverseImage f : AbelianSheaf.{u,u+1} S ⥤ AbelianSheaf.{u,u+1} X`
faithful. Its companion `inverseImage_mono_iff_of_surjective` gives,
for every original coefficient arrow `a`,

```lean
Mono ((inverseImage f).map a) ↔ Mono a
```

The proof uses the actual conservative family of image geometric points and
the existing original stalk-unit and point-universe comparisons. There is no
finite-presentation, Noetherian or Ext premise.

## Projective geometry over the original affine base

Let `R : Type u` be a commutative ring and
`f : X ⟶ Spec (.of R)` be proper.
`exists_projective_modification` supplies `Y`, a proper surjection
`p : Y ⟶ X`, a natural number `m`, and an actual closed immersion

```lean
j : Y ⟶ ProjectiveSpace R (ULift.{u} (Fin (m + 1)))
```

with the original equation

```lean
j ≫ ProjectiveSpace.toSpec R (ULift.{u} (Fin (m + 1))) = p ≫ f
```

The intermediate `exists_projective_modification_of_finitePresentation`
retains `LocallyOfFinitePresentation f`; the final theorem removes that
premise using the published proper-approximation system. Neither `R` nor
`f` is required to be Noetherian, reduced or flat, and the final theorem
requires no finite-presentation hypothesis. Finite presentation of `Y`
and dense-open isomorphism data are outside the exported packet.

## Original all-coefficient reductions

[HigherReduction](Reduction/HigherReduction.lean) proves composition and
surjective descent for the original all-degree higher exchange on every actual
coefficient satisfying `n • 𝟙 F = 0`, for any natural `n`, including zero.
Its hypotheses quantify all coefficients on the declared source schemes.
All six original derived-category universes remain independent.

[AllModuleCoefficients](Reduction/AllModuleCoefficients.lean) extends original
exchange tests on genuine injective `ZMod n` sheaves to every n-killed abelian
coefficient. The auxiliary module-derived model is supplied internally; it does
not constrain the four displayed abelian-derived universes. The exact genuine
module images and actual injective retract use
[ZModImages](Reduction/ZModImages.lean) and [ZModRetract](Reduction/ZModRetract.lean).
[HigherImageAcyclic](Reduction/HigherImageAcyclic.lean),
[ZModAcyclic](Reduction/ZModAcyclic.lean) and
[ZModDerivedImage](Reduction/ZModDerivedImage.lean) identify the original
relative acyclicity and actual derived image of the underlying injective.
Scalar forgetting and geometric pullback are never assumed to preserve injectives.

The native
[injective-single criterion](../../../Algebra/Homology/DerivedCategory/Plus/InjectiveComparison.lean)
uses triangulated functors, installed shifts, nonnegative source-single images
and tests on actual injectives. Its finite-degree induction derives degree zero;
it adds no H0 comparison, convergence or unbounded-resolution premise.
[ExchangeShift](Reduction/ExchangeShift.lean) proves shift compatibility for
the original canonical mate.
[SingleHigher](Reduction/SingleHigher.lean) identifies original derived-single
invertibility with invertibility of all original natural-degree higher maps.
[InjectiveExchange](Reduction/InjectiveExchange.lean) and
[BoundedCoefficients](Reduction/BoundedCoefficients.lean) retain the actual
source coefficients and maps in the composition/descent arguments.

## Conditional projective-line reduction

[GeometryCriterion](Reduction/GeometryCriterion.lean) reduces an explicitly
supplied morphism property to the native projective line over an arbitrary
spectrum. Composition stability, arbitrary base-change stability, membership
of finite maps and the proper-surjective descent rule remain hypotheses.
The proof uses the production finite binary-form covers and the actual Chow
packet above; it leaves no Noetherian or finite-presentation premise on the
original affine base or proper morphism.

The constructed
[universal bounded exchange property](Universal/Basic.lean) tests every
coefficient killed by `n` on every pulled-back source. Actual finite exchange,
composition and surjective descent supply its closure rules. Thus universal
exchange for the native projective line implies the same property for every
proper morphism over the same arbitrary spectrum. The initial original-source
predicate alone is not asserted stable under base change.

[ModelTransport](Universal/ModelTransport.lean) transfers this standard-model
property to the original higher exchange in four independently supplied
derived-category models and universes. It uses the actual ordinary mate in
degree zero and the original higher-image zero objects on genuine module
injectives in positive degrees. [AffineReduction](Universal/AffineReduction.lean)
exports the original higher-exchange and derived-single conclusions directly.
Every natural modulus, including zero, is retained. No injectivity after scalar
forgetting is asserted.

The actual universal projective-line input is constructed in
[Universal/ProjectiveLine](Universal/ProjectiveLine.lean).
[TargetLocality](Universal/TargetLocality.lean) supplies the arbitrary-target
bounded conclusion, and [BaseChange](BaseChange.lean) assembles the original
locally torsion higher and D+ endpoints. The reductions retain their explicit
inputs as reusable interfaces.

## Original strictly local test coefficients

[FiniteTests](Local/FiniteTests.lean) transports original cohomology pullback
surjectivity and injectivity to an actual finite direct-image coefficient,
through the original finite cohomology exchange square. All four Ext
universes remain independent, and no torsion assumption is required.

[ProjectiveLineTests](Local/ProjectiveLineTests.lean) applies the completed
curve comparison to finite constant direct images on the literal projective-line
residue fibre. It proves all-degree surjectivity over any henselian local ring
with separably closed residue field and degree-zero injectivity over any
henselian local ring. Neither conclusion adds Noetherianity or an order
condition; higher injectivity for general coefficients remains a devissage.

[ModuleCogenerators](Local/ModuleCogenerators.lean) factors a given original
abelian monomorphism through the actual native annihilator of its target,
yielding a monomorphism of the original genuine `ZMod n` sheaves. Its proved
factorization recovers the original arrow. The annihilator of a constant
direct image is the same direct image of the actual constant value kernel;
finite values remain finite. Every modulus is permitted. This constructs the
module adapter from a supplied embedding; it does not produce general finite
cogenerators or complete the remaining coefficient presentations.

[AnnihilatorProducts](Local/AnnihilatorProducts.lean) identifies the original
whole-product annihilator with the product of its actual coordinate
annihilators, including empty products and all moduli. The constant direct-image
specialization retains the original finite sources and value kernels. Applying
the same genuine-module lift to the whole original abelian product therefore
supplies the product target adapter for a given finite cogenerator embedding.

The [local cohomology criteria](Local/README.md) reduce the original
`cohomologyPullback` to explicit finite-embedding and finite-annihilator tests.
The projective-line specialization retains `n ≠ 0`, its henselian and
residue-field hypotheses, and `hfinite`. The selected PBC route constructs
that finite-embedding input; the local criterion retains it explicitly for
independent applications.

## Scope boundaries

The formal composition and retract theorems retain their displayed
exchange-invertibility inputs for general commuting squares. The proper
endpoints above supply those inputs in their stated torsion range.
Unbounded proper exchange and the remaining six-operation formalism have
separate homological and coherence obligations.

The [finite family](../Finite/README.md) supplies actual finite exchange.
The [torsion family](../Torsion/README.md) retains its geometric presentation,
local surjectivity inputs and conditional original-map test interfaces. Proper
base change constructs the actual geometric and comparison inputs needed by its
selected route; unrelated applications retain their own premises.
