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

## Open resolution construction

The full singular-surface resolution criterion RES and its quasi-excellent
corollary RES-QE remain open. The normal-graph, vanishing and necessity
results above do not supply the converse construction.

The remaining argument includes global canonical-module and integral-trace
comparisons, full coefficient-valued curve Serre duality, canonical
restriction, rational/Gorenstein reduction, geometric production of the
genuine child tangent-cone hypotheses, persistent marking and full RDP
termination, complete-local degree induction, and descent and globalization
of the prescribed normalized chain. The completed interfaces below supply
parts of this argument under their stated hypotheses; they do not supply
the converse resolution construction.

The [monic-quadratic kernel theorem](../../../RingTheory/GradedAlgebra/MonicQuadratic.md)
assumes both an actual relation and the genuine Hilbert function
`finrank k (H n) = 2*n+1` in every nonnegative degree. Deriving those
inputs from the rational/Gorenstein geometry remains open; changing
cotangent coordinates only preserves a presentation already supplied.

[MarkedPath](../../Blowup/Arc/MarkedPath.md) constructs a formal arc on a
given marked ordinary point-blowup path and obtains regularity at an
original selected point under its actual completion or complete-base
hypotheses. The marking and the original finite-prefix residue-finiteness
conditions remain inputs. Its local termination conclusion does not
construct the required marking or an arbitrary global resolving chain.

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
The intrinsic-line coefficient concentration and generic affine coefficient
model do not themselves supply full coefficient-valued Serre duality.

[Ordinary rational blowups](../RationalSingularities/README.md#ordinary-rational-blowups-and-the-full-exceptional-fibre)
and [conditional quadratic charts](../../../RingTheory/Blowup/README.md#conditional-quadratic-charts-and-differential-images)
provide original-map, ideal-power and local marked-successor primitives.
Their rationality, full-kernel, Hilbert-function and marking premises remain
explicit. A supplied normalized chain, its cohomological consequences and
its pointwise comparisons are distinct from existence and termination of a
resolving chain. RES and RES-QE remain open.

[NormalizedPointBlowupChain](NormalizedPointBlowupChain.md) records a supplied
finite sequence of literal ordinary blowups at closed nongeneric points,
each followed by normalization in its original function field. Its index
is the actual composite arrow. Integrality, normality, dominance and the
original function-field isomorphism are derived without Noetherian or Nagata
hypotheses. Finiteness of normalization, hence chain properness, needs its
own hypotheses and is not automatic. The
[completion point comparison](../../Descent/CompletionPointBlowup.md) supplies
the one-step consumer interface under its actual domain-completion and
normal-upper-model assumptions. The full finite-chain descent capstone and
existence of a resolving chain remain open; this chain type supplies neither.
