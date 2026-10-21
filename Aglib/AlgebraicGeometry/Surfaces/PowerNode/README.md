# Power-node blowups and resolution

The coefficient algebra is the existing `PlaneNode.Ring c`, with literal
relation `U * V = c`. `PowerNode.Rees.node π n` is the same algebra at `c = π ^ n`.
The ring calculations use the existing saturated localization subalgebras;
no unsaturated quotient replaces a chart.

[Blowup/NodeAtlas](Blowup/NodeAtlas.lean) constructs the three actual open charts
of a supplied ordinary blowup and affine atlas, in the order U, π, V. The rings
are `PlaneNode.Ring π`, `PlaneNode.Ring (π ^ m)`, and `PlaneNode.Ring π` for
exponent `m + 2`. Coverage, overlaps, ratio formulas and blowdown triangles are
proved for those maps. [Blowup/StructuralFlatness](Blowup/StructuralFlatness.lean)
derives flatness of the structural composite to the original DVR from these
three charts.

[Resolution/Recursion](Resolution/Recursion.lean) constructs the resolution by
replacing the middle chart with the resolution at exponent `m` and taking the
actual open pushout with the two unchanged outer charts. Exponents zero and one
are distinct identity base cases. The data records properties of that actual
map; its constructors prove those properties. The recursive constructor retains
three explicit inputs:

- `Scheme.Blowup.NoetherianBlowupExistence`;
- `Scheme.Blowup.NoetherianBlowupProper`;
- `Scheme.Blowup.BlowupAffineAtlas`.

[Resolution/SourceGeometry](Resolution/SourceGeometry.lean) proves flatness,
reducedness, integrality and surjectivity of the same recursively constructed
source. The generic-fibre comparison is the canonical map between the literal
fibre products over the supplied fraction field. The coefficient ring remains
a domain DVR and `π` remains irreducible throughout these geometric statements.
The pure Laurent comparison and uniformizer-node regularity live below schemes
in `Aglib.RingTheory.PlaneNode.Regularity`.

[PointedEtale/Charts](PointedEtale/Charts.lean) treats an arbitrary actual scheme
and a specified point over the original residue field. Each chart retains two
full scheme-theoretic centre squares. Its successor uses the actual middle
chart and the existing full-fibre shrinking construction.
[PointedEtale/Runs](PointedEtale/Runs.lean) iterates those constructed steps with
a decreasing exponent. The additional input
`Scheme.Blowup.BlowupFlatBaseChange` stays explicit. Regularity descent for an
arbitrary pointed global source remains a separate condition.

[PointedEtale/Unchanged](PointedEtale/Unchanged.lean) specializes the relative
unchanged-open theorem to the original map. Its section lift uses that actual
restriction isomorphism. The Weierstrass adapters keep the original equation,
residue point, common chart and unit-power equation throughout the finite run.

The comparison leaves use the shared `Scheme.LocalRing.ResidueFiber` objects
and maps. `Scheme.PowerNode.specializationIso` is the existing canonical node
base-change isomorphism followed by the literal pullback symmetry, so its first
projection is the node projection. Reciprocal coordinate maps target the fixed
homogeneous `Scheme.ProjectiveLine.projectiveP1`; their general gluing and
descent proofs extend the existing projective-line family in
`Aglib.AlgebraicGeometry.Curves.ProjectiveLine.Reciprocal`.

The critical-neighborhood leaves retain an actual étale faithfully flat
coefficient algebra, its original-residue-field point, critical translation and
coordinate displacements. That coefficient algebra is not assigned a local-ring
or DVR structure. The field-valued tangent-point construction permits an
arbitrary field algebra over its coefficient ring.

The strict-transform leaves construct the image of the integral punctured open
in the same final residue fibre. They prove its closure support, the actual
strict-plus-exceptional cover and the retained first-chart comparisons. The
Weierstrass specializations reuse the proved coefficient-base-change and
residue-fibre integrality suppliers. A component inventory is obtained from
the actual maps and their noncontainment proofs; it is not an input count.

Positive-thickness strict-normalization recognition uses actual étale curve
charts and the proved `RegularityDescent.Etale.regular_at_image` on their original
stalk maps. Smooth-field regularity and the required dimension statements are
supplied by the native curve-chart theorems. Its parametric lower interface retains
the proper-birational DVR-locus and normal/proper curve-extension inputs. The normalization arrow and its
function-field map are the actual maps constructed from the same equation.
The downstream `SplitRationalComponents` record is not copied; the comparison
provides the individual P¹ maps, their ranges and their closed immersions.

The regularity of the independently constructed local node resolution does
not discharge regularity descent for an arbitrary pointed global scheme.
The actual strict-curve applications use étale descent and no longer require
`FlatLocalRegularityDescent`. Their pointwise applications use the original
stalk maps, field maps and charts. The retained parametric families have actual native suppliers
`normalProperCurveGenericExtension`, `smoothFieldRegularity`,
`smoothClosedPointDimension`, `smoothFieldDimension`, and
`properBirationalDVRIsomorphismLocus`. The concrete cyclic-fibre adapters apply
the relevant suppliers internally. General `FlatLocalRegularityDescent` remains
a separate unproved predicate; the étale theorem does not supply that full family.

Relative minimality has a further boundary in
[Components/Minimality](../../Curves/Models/Components/Minimality.lean).
`Scheme.LocalRing.ResidueFiber.noMinusOne_isIso` takes
`VerticalContractionExceptionalComponent` explicitly. It also requires the
original regular Noetherian integral surfaces of dimension two, proper flat
structural maps over the DVR, the proper dominant comparison over that DVR,
and isomorphisms on its actual function fields and generic fibres. Its component
data are closed integral components with exhaustive ranges and isomorphisms to
P¹ over the residue field. The proper-curve product formula and the exclusion
of normal degree −1 for every locally rank-one component ideal remain inputs.
The component maps and intersection squares in this family supply geometric
data for such a criterion; they supply no surface-contraction theorem.

The alternative common-blowup initial adapter from the original `NextCenter`
source is not used by this route. Its raw models have not been identified with
the chosen `initialChart` and generic successor states, so that adapter remains
downstream.

These interfaces preserve the original Cartier, centre, localization and base
maps. Their parametric lower interfaces retain the four blowup families; the
native `Blowup` construction, properness, affine-atlas and flat-base-change
providers supply those exact families in the concrete adapters. Final R5 model-cover,
marked or arithmetic assemblies remain downstream. Picard/Hilbert
representability remain outside this family. Purity is handled by a separate
theorem owner; it is not used here to remove any displayed input.

The source basis is frozen R5 revision
`f8a3314ddecffcada2ec721d26d56a937bed9690`. The primary selection is the five
`PointedResolution.Blowup` modules, the six `PointedResolution.Resolution`
modules, and the fifteen selected `CyclicModelComparison` component, closure,
recognition and intersection modules. Partial extractions are routed as follows;
line numbers refer to that revision, not to the native files.

| Source cut | Native owner and purpose |
| --- | --- |
| `Resolution.NextCenter:19–95` | [NextCenter](Resolution/NextCenter.lean): residue origin, centre and blowdown triangles; later alternative initial adapters stay downstream. |
| `PointedEtale.Runs:14–228,230–291` | [Runs](PointedEtale/Runs.lean) and [Weierstrass](PointedEtale/Weierstrass.lean): generic finite runs and the actual original-equation initial state. |
| `ResolutionGeometry:136–185,239–303,602–678` | [Unchanged](PointedEtale/Unchanged.lean), [Weierstrass](PointedEtale/Weierstrass.lean), [WeierstrassSections](PointedEtale/WeierstrassSections.lean) and [FullMiddleCenters](PointedEtale/FullMiddleCenters.lean): restrictions, section lifts and four full-centre squares. |
| `EtaleNode.CriticalNeighborhood:33–437`; `CommonChart:115–619` | [CriticalNeighborhood](../../EllipticCurve/Weierstrass/CriticalNeighborhood/Basic.lean) and its [common chart](../../EllipticCurve/Weierstrass/CriticalNeighborhood/CommonChart.lean): actual coefficient algebras, translation, residue point and centre maps. |
| `Weierstrass.DVRNode:72–96,190–245,253–304` | [ResidueNode](../../EllipticCurve/Weierstrass/ResidueNode.lean) and [ResidueNodeInfinity](../../EllipticCurve/Weierstrass/ResidueNodeInfinity.lean): original residue evaluation, projective point and infinity complement. |
| `ProjectiveComponents:12–337,928–1001` | [Reciprocal](../../Curves/ProjectiveLine/Reciprocal.lean): general reciprocal chart gluing on the fixed homogeneous P¹; the node consumers stay in [ProjectiveComponents](Comparison/ProjectiveComponents.lean). |
| `StrictTransformClosure:20–192,198–536,539–810` | [StrictTransformClosure](Comparison/StrictTransformClosure.lean) and its [Weierstrass specialization](Comparison/WeierstrassStrictTransformClosure.lean): the actual punctured-open image and closure. |
| `StrictTransformCover:12–237,240–635,638–1077,1080–1205,1208–1310,1313–1394` | [StrictTransformCover](Comparison/StrictTransformCover.lean) and its [Weierstrass specialization](Comparison/WeierstrassStrictTransformCover.lean): generic retained charts and original-equation fibre coverage. |
| `BranchComparison:16–117,118–298,378–483`; `SingularCubic:586–750` | [Birational](../../Curves/ProjectiveLine/Birational.lean) and `CriticalCubic.{TargetNormalization,SingularNormalization,SingularTranslation}`: actual field-compatible maps and normalization, with the original extension input. |
| `NativeStrictIntersections:260–386`; `StrictTransformRecognition:12–1011` | [NativeStrictIntersections](Comparison/NativeStrictIntersections.lean) and [StrictTransformRecognition](Comparison/StrictTransformRecognition.lean): actual comparison squares and recognition; later component-record adapters stay downstream. |
| `FunctionField.AffineCharts:165–273`; `MorphismExt:26–59` | [AffineCompatibility](../../FunctionField/AffineCompatibility.lean) and [MorphismExt](../../FunctionField/MorphismExt.lean): canonical generic/coordinate triangles, structural constants and separated uniqueness. |

The supporting regularity, plane-node residue and scheme-theoretic image
lemmas retain their own source locators in their module headers. The extra
critical-cubic affine leaf selects the nineteen finite, localization,
fraction-field and section declarations from `CriticalCubic.Affine`; it reuses
the existing `coordinateMap` and `affineNormalization`. Its projective leaf
keeps the same normalization arrow and the original curve-extension input.
The two discriminant-thickness constructors in `Blowup.Comparison`, the
alternative initial-state adapters and the terminal component/model records
are retained downstream. Module headers preserve exact source hashes.
Compilation evidence is separate from these source selections and from
mathematical adoption.
