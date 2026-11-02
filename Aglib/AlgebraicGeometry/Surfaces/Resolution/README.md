# Surface principalization and resolution prerequisites

[Principalization](Principalization.md), in `Scheme.Blowup`, supplies
`exists_regular_pointBlowup_principalization` for a locally Noetherian integral
scheme `X` whose actual stalks are regular local rings of Krull dimension at
most two. The input is a nonzero native ideal sheaf `J` with an actual
Artinian quotient subscheme `J.subscheme`.

The result is a finite `PointBlowupChain` with actual composite `f : Y ⟶ X`.
It retains properness, dominance and `BirationalOver f (𝟙 X)`, integrality and
regularity of `Y`, and the same local dimension bound. Its conclusion
`cartierPullback J f` concerns local rank one of the actual ideal module of
`J.comap f`: the original total inverse-image ideal is Cartier.
`exists_regular_pointBlowup_principalization_of_dimension_le_two` accepts
`topologicalKrullDim X ≤ 2` and derives the required original stalk bounds.

[WeakTransform](WeakTransform.md) defines the weak ideal on an actual universal
blowup `B` as

```lean
(J.comap B.map).colon ((I.comap B.map) ^ r)
```

Here `I` is its actual centre ideal. Under `J ≤ I ^ r`, the exact equality
`(I.comap B.map) ^ r * B.weakTransform J r = J.comap B.map` retains the whole
inverse-image ideal. Its affine and stalk comparisons use the original
[ideal-sheaf colon](../../IdealSheaf/Colon.md) and the literal
[saturated-chart weak transform](../../../RingTheory/Blowup/WeakTransform.md).
The actual local-spectrum blowup comparison preserves this weak ideal and
the original local order.

The construction chooses closed points with two-dimensional local rings.
[Local colength](../../../RingTheory/Blowup/Colength.md) strictly decreases at
every new nonfree ideal stalk over the chosen centre. The finite multiset
`nonfreeIdealColengths` records those actual local lengths with multiplicity;
its well-founded decrease replaces the selected entry by finitely many smaller
entries and retains the entries away from the centre. It does not require a
decreasing unweighted sum. The principalization proof derives finite support and finite
local lengths from the actual Artinian quotient. Conversely, the
[actual-stalk Artinian bridges](../../IdealSheaf/Artinian.md) assemble finite
support and finite original stalk-quotient lengths into an Artinian weak
quotient along the chain.

At the terminal stage, every actual ideal stalk has a singleton basis. The
Cartier exceptional-power and product equations recover the original total
inverse-image ideal through the later dominant integral chain maps. This uses
the canonical ideal maps and Cartier avoidance; pullback of an abstract
invertible module alone is not substituted for the embedded ideal comparison.

## Supplied chains and their generic maps

[PointBlowupChain](PointBlowupChain.md), in `Scheme.Blowup.PointBlowupChain`,
concatenates supplied chains over their literal composite. For integral
original `X`, `functionFieldMap_isIso` and `functionFieldEquiv` identify
the original canonical function-field map of a supplied chain with an
isomorphism. This needs no additional regularity, Noetherianity,
properness or global dimension hypothesis.

[Trait](Trait.md) treats a supplied chain `f : Y ⟶ X` and an actual proper
`p : X ⟶ Spec R` over a DVR with specified fraction field `F`.
`PointBlowupChain.genericBaseChange_isIso` proves invertibility of the
literal `Over.pullback (baseMap R F)` image of `f`.
`PointBlowupChain.genericIso` has exactly that forward map, with the
original projection and base triangles. Regularity, integrality and
flatness of `X` are unnecessary for this preservation theorem. The separate
[proper section theorem](../../Morphisms/Proper/TraitSections.md) lifts
original sections through a proper map with such an invertible generic map.

Principalization starts with an already regular source and an Artinian
ideal quotient. The
[original rational-coordinate ideals](../../RationalMap/BaseIdeal.md)
supply such an ideal to
[projective extension](../../RationalMap/ProjectiveExtension.md), which in
turn serves [regular-source common domination](../Birational/CommonDomination.md).
Removing a divisorial part of an arbitrary ideal and resolving an initially
singular scheme remain separate obligations.

## Splitting and punctured cohomology from the original normal graph

[ExtensionGraph](ExtensionGraph.md), in
`Scheme.ProjectiveBundle.RankTwoExtension`, proves
`splitting_of_finite_normal_graph` for an actual rank-two extension on an
integral normal scheme proper and birational over a normal Noetherian
local domain of dimension two. A supplied finite map from an integral
normal scheme to its actual projective bundle has birational projection,
avoids the quotient section generically, and meets that section only over
the original closed base point. The original Cartier ideal, conormal
comparison and open complement then split the extension.

[Construction](ExtensionGraph/Construction.md) constructs this finite
normal graph as the literal normalization of the punctured
complementary-section image. Its actual injective finite-type algebraic
chart maps satisfy the
[surface Nagata stability theorem](../../../RingTheory/Nagata/FiniteTypeSurface.md).
It proves injectivity of the original punctured structure-H1 restriction
over a normal Noetherian Nagata local domain of dimension two. The
complete-base corollary derives Nagata on the original base. The
[residue-field calculation](../../Cohomology/Proper/ResidueVanishing.md)
uses this injection to obtain the original degree-one residue-Hom
vanishing.

## Regular-local vanishing and necessary conditions

[Regular](../RationalSingularities/Regular.md), in
`Scheme.RationalSingularities`, proves universal original structure-H1
vanishing for every supplied integral normal proper dominant model over
a regular local ring of dimension two whose original function-field map
is invertible. It constructs a dominating regular point chain from the
already regular base and applies the original H1 injection. The supplied
normal model need not be projective, and no resolution of it is an input.
This universal predicate does not assert Nagata or construct a resolution
of an initially singular surface.

[Necessity](Necessity.md) starts with a supplied proper dominant birational
regular integral model of an integral Noetherian scheme of dimension at
most two. It proves finiteness of the literal generic normalization,
finiteness of that normalization's singular set, and normal domain
completions at every actual normalization point. The localized structural
section bijections are derived from the original normal-birational map.
These are necessary conditions for resolution, not an existence theorem.

## Normalized chains, domination and completion

[NormalizedPointBlowupChain](NormalizedPointBlowupChain.md) records a finite
sequence of literal ordinary blowups at closed nongeneric points, each
followed by normalization in its original function field. It is indexed by
the composite arrow. Its native laws derive integrality, normality,
dominance and the original function-field isomorphism without a Nagata or
Noetherian premise. Properness additionally requires finite normalization.

[Normalized-point domination](../Birational/NormalizedPointDomination/AffineBase.md)
constructs such a chain dominating any supplied integral proper birational
model over a commutative normal Nagata domain of dimension at most two.
Its terminal is normal; it need not be regular.

[CompletionDescent](CompletionDescent.md) takes a commutative Noetherian
local domain `A` of dimension two whose literal completion `H` is a normal
domain. A supplied normalized-point chain over `Spec H` descends to one over
`Spec A` of exactly the same length, with proper dominant original map,
integral terminal and invertible original function-field map.
The explicit terminal isomorphism to the completion pullback retains both
projections. Supplied regularity of the upper terminal descends as well.
The upper chain is an input; it is not constructed by descent.

[Rationality under completion](../RationalSingularities/Completion.md)
combines domination and arbitrary-terminal chain descent with the original
flat cohomology comparison and proper-birational H1 injection.
It proves `NormalModificationH1Vanishing A → NormalModificationH1Vanishing H`
under the same dimension and normal-domain completion assumptions, without
Nagata on `A` or algebraization of an arbitrary model over `H`.

## Conditional resolution from initial full cones

[FiniteResolution](RationalDoublePoint/FiniteResolution.md) starts with a
commutative Noetherian Nagata local domain `R` of dimension two satisfying
`NormalModificationH1Vanishing R`, and an integral normal model
`f : X ⟶ Spec R` which is proper and dominant with invertible original
function-field map. Its intermediate theorem serializes empty levels of
the original singular prefixes into an ordinary finite point-blowup chain.
It proves normality of all chain stages, regularity of the terminal and an
isomorphism over every original open whose stalks are regular.

The geometric endpoint takes two additional inputs. At each original
singular stalk, `hcones` supplies a generating triple `(t,g₀,g₁)` and a
nonzero homogeneous quadratic `q` over its original residue field with
`RingHom.ker (CaseOne.canonicalConeMap t g) = Ideal.span {q}`.
A commutative local domain `A` is complete for its maximal ideal and has
dimension two, with an actual local injective `a : A →+* R` and finite
original residue-field map. This earlier `A` has no additional Noetherian
hypothesis; neither `R` nor later stalks are assumed complete.

[OriginalPathCones](RationalDoublePoint/OriginalPathCones.md) constructs the
later full cones from the supplied initial cone.
[OriginalMixedPath](RationalDoublePoint/OriginalMixedPath.md) constructs a
marked tail, distinguishing the ratio parameter in second entry from the
previous exceptional denominator. The
[original marked-path theorem](../../Blowup/Arc/MarkedPath.md) then gives
a regular point using the earlier complete base and the original composed
local and residue maps.
[FinitePrefixGeometry](RationalDoublePoint/FinitePrefixGeometry.md) proves
finite branching before choosing any infinite continuation;
[FiniteHeight](RationalDoublePoint/FiniteHeight.md) applies native König
to obtain an empty level.
[PointHeight](RationalDoublePoint/PointHeight.md) and
[HeightMultiset](RationalDoublePoint/HeightMultiset.md) give the strict
decrease used in finite serialization.

[NormalizedResolution](RationalDoublePoint/NormalizedResolution.md) converts
that ordinary chain to a literal normalized-point chain using its proved
normal stages and an explicit terminal isomorphism. It retains the proper
dominant birational original map, integral regular terminal and isomorphism
over every original regular open. It uses the same `hcones` and earlier
complete-base map.

The [monic-quadratic kernel theorem](../../../RingTheory/GradedAlgebra/MonicQuadratic.md)
requires an actual relation and `finrank k (H n) = 2*n+1` in every degree.
The [first-power exceptional theorem](RationalDoublePoint/ExceptionalHilbert/FirstPower.md)
derives this Hilbert function on a normal Nagata rational local surface
from cotangent rank three. Singular child three-generation supplies that
rank in the path construction. Initial-cone recognition from arbitrary
rational or rational-Gorenstein input remains separate.

## Remaining input boundary

The full singular-surface resolution criterion RES and its quasi-excellent
corollary RES-QE remain open. The conditional endpoint above does not derive
`hcones` from arbitrary rational or rational-Gorenstein data.
The selected completion-descent theorem does not supply complete-local
resolving-chain existence. [Supported surface-chain spreading](../../Descent/LocalModification/SurfaceChain.md)
already extends a supplied proper normalized chain at a closed nongeneric
point of an integral normal Noetherian surface of dimension at most two.
It preserves the length, original stalk Cartesian square and complement;
regularity follows from a supplied regular local terminal and regular
unchanged complement. Complete-local existence and the remaining global
criterion assembly must still be supplied before these interfaces prove RES.

## Additional prerequisites and their consumers


[Finite domination](../Birational/FiniteDomination.md) constructs the actual
normal finite diagram used by the
[finite separable H1 transfer](../../Cohomology/Proper/FiniteExtension.md).
The latter retains a genuine lower uniform bound, Nagata normal local
surface bases and original function-field separability. The
[maximal-model construction](../../Cohomology/Proper/MaximalModel.md) consumes
such a uniform bound; its
[complete-local R1 consequence](../../Cohomology/Proper/MaximalModel/R1.md)
uses the original higher direct image. Neither supplies a resolving chain.

[Chosen-embedding GR](../../Cohomology/Proper/GrauertRiemenschneider.md)
retains a finite injective local map from a regular local surface base, a
compatible actual closed embedding, a complete normal local surface target
and a supplied normal proper birational model of dimension at most two.
[Unit-coefficient curve Serre](../../Cohomology/Duality/Projective/Relative/CohenMacaulayCurve/Serre.md)
retains the closed-stalk regular-primary parameter condition and `1 ≤ n`.
[Coefficient-valued Serre](../../Cohomology/Duality/Projective/Relative/CohenMacaulayCurve/Coefficients/Serre.md)
keeps an actual finite one-dimensional coefficient module, the curve's
regular-primary/CM hypotheses and coherent-source conditions. Its maps,
trace and naturality are normalized against the original structural maps;
the coefficient line is not silently identified with the ground field.
The [Cartier restriction](../../Cohomology/Duality/Projective/Relative/NormalSurface/CartierRestriction.md)
and finite canonical comparison interfaces retain their actual embedding,
regularity and scalar-map conditions.

[Ordinary rational blowups](../RationalSingularities/README.md#ordinary-rational-blowups-and-the-full-exceptional-fibre)
and [conditional quadratic charts](../../../RingTheory/Blowup/README.md#conditional-quadratic-charts-and-differential-images)
provide original-map, ideal-power and local marked-successor primitives.
Their rationality, full-kernel, Hilbert-function and marking premises remain
explicit. The conditional initial-cone endpoint above constructs a resolving chain
under its stated inputs. These prerequisites alone do not supply those
inputs or the full RES and RES-QE construction.
