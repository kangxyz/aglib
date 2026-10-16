# Native mathematical interfaces

`Aglib` is an import root. Mathematical declarations extend native owners: `Module` and `Algebra` for algebraic objects/maps, `CategoryTheory` for categorical structure, `TopCat.Sheaf` for topological sheaves, and `AlgebraicGeometry.Scheme`/`Scheme.Modules`/`Scheme.Cohomology` for scheme-specialized objects. A declaration namespace need not be its source module path.

The selected exact-category structure lives in `CategoryTheory.ExactCategory`. Its `ExactFunctor` preserves chosen conflations and is distinct from other native exact-functor notions. Its [pushout interface](../Aglib/CategoryTheory/ExactCategory/README.md) retains the admissibility of the first input map of the displayed pushout square. Site Cech declarations use `CategoryTheory.Cech`; small-model declarations use the actual `CategoryTheory.SmallModel` interface. [namespace-map.json](namespace-map.json) records correspondence and [module-map.json](module-map.json) records path changes. Original names are provenance; downstream adapters belong in the original packages.

## Object properties and categorical structures

Ambient module sheaves are Mathlib's actual `X.Modules`. Quasicoherence, finite type, finite presentation and finite local freeness are distinct properties of these sheaves. The locally Noetherian coherent category is an abelian/exact specialization; those categorical structures must not impose local Noetherianity on lower finite-type or finite-presentation constructions that do not need it.

Affine comparison relates actual finite-type quasicoherent sheaves to finite modules. Arbitrary pullback preserves finite presentations and coherent objects under the source interfaces' hypotheses; flatness supplies the exact coherent-pullback interface. Finite and closed-immersion pushforward keeps its actual affine scalar-restriction/quotient comparison. Vector bundles use finite local bases and arbitrary exact pullback through local splitting.

Small-model construction retains the supplied `EssentiallySmall.{w}` witness and chosen universe `w`. Supplied injective-resolution kernel sequences do not assert existence of resolutions in arbitrary categories. Ext and total-complex comparisons retain their object, morphism and coefficient universes.

The [structural perfect-complex family](../Aglib/AlgebraicGeometry/Modules/PerfectComplexes/README.md) extends `Scheme.Modules.Complex` on arbitrary schemes. `StrictPerfect X` is the chain category of complexes with globally bounded terms that are finite locally free; `Perfect X` is the full chain category defined by local derived isomorphisms to strict models under the actual `DerivedCategory.Q`. The latter is not itself the derived localization. Open restriction, inherited strict exactness and strict shift/cone closure retain these objects. Local perfectness gives quasicoherent homology and local homology bounds without termwise quasicoherence or a global strict model. Only the single global homology interval requires `CompactSpace X`; it does not provide a global term bound or strictification. The [ordinary-complex](../Aglib/AlgebraicGeometry/Modules/Complex/README.md) and [quasicoherent](../Aglib/AlgebraicGeometry/Modules/QuasiCoherent/README.md) guides own the lower homology comparisons and termwise-quasicoherent result.

The [finite-etale family](../Aglib/AlgebraicGeometry/Morphisms/FiniteEtale/README.md) uses the actual full subcategory `Scheme.FiniteEtale X` of `Over X`, with finite etale structural maps; empty covers are allowed. Its field-valued fibre functor and base-change comparisons keep the actual maps. The lower [finite-morphism point-lift interface](../Aglib/AlgebraicGeometry/Morphisms/Finite/README.md) gives finite Hom sets of lifts through a finite morphism over an arbitrary field. A finite lift set may be empty; the separate geometric-point existence theorem retains surjectivity and an algebraically closed field.

The [algebraic rigidity interface](../Aglib/RingTheory/Unramified/README.md) gives `Algebra.FormallyUnramified.eq_of_comp_mkQ_eq`: an essentially finite-type formally unramified commutative `R`-algebra has equal maps to a domain `R`-algebra when their reductions at a supplied prime ideal agree. The [section-rigidity interface](../Aglib/AlgebraicGeometry/Morphisms/FormallyUnramified/README.md) gives `Scheme.Hom.eq_of_comp_eq_of_section` for a separated, formally unramified, locally finite-type `p : X ⟶ Y`, a geometrically connected `q : Z ⟶ T` with a specified section, and maps `f g : Z ⟶ X` with equal composites through `p` and equal restrictions to that section. These are equality statements about the actual maps; their family guides retain the complete equations and hypotheses.

## Canonical maps and cohomology objects

The module-base-change map is the actual pullback/pushforward counit mate, with source `g* f_* M` and target the direct image of the pulled-back module on the fibre product. Relative evaluation is the original adjunction counit. The invertibility theorem must concern that constructed map.

Structure and module cohomology are actual additive `Sheaf.H`. For schemes/fields in universe `u`, these Ext-defined types are in `Type (u+1)`. Structural constants induce the field action. The H0 comparison, coefficient maps, connecting maps, geometric pullback and field-tensor map preserve these objects and actions. A resolution/Cech computation becomes a statement about `Sheaf.H` through its proved canonical comparison.

## Explicit theorem-family inputs

Some proposition-valued interfaces remain as explicit data. The affine base-change and proper-constants interfaces below now have actual theorem suppliers; their predicate definitions are retained. Proper module-cohomology finiteness and relative locally free base change remain unsupplied inputs.

| Native input owner | Conditions and conclusion |
| --- | --- |
| `AlgebraicGeometry.Scheme.Modules.AffineModuleBaseChange` | The retained predicate has a proved supplier for affine `f`, quasicoherent coefficients and arbitrary `g`; the actual canonical mate is invertible without flatness of `g`. |
| `AlgebraicGeometry.Scheme.Cohomology.ProperModuleCohomologyFinite` | Proper field scheme, finitely presented module sheaf, nonnegative degree: the actual structural-field cohomology is finite-dimensional. |
| `AlgebraicGeometry.Scheme.ProperStructureCohomologyFinite` | Structure-sheaf specialization of proper field-scheme finiteness; the module family supplies it through the actual scalar-compatible comparison. |
| `AlgebraicGeometry.Scheme.ProperGeometricallyIntegralConstants` | The predicate file is unchanged. `Scheme.constants_bijective_of_proper_geometricallyIntegral` supplies bijectivity of the actual constants map for proper geometrically integral field schemes. |
| `AlgebraicGeometry.Scheme.Cohomology.LocalFreeCohomologyBaseChange` | Proper, locally finitely presented, flat `f`; locally free/finitely presented coefficients; geometric fibre cohomology concentrated in degree zero of rank `r`: direct image has rank `r`, and its actual mate is invertible after every change of base. |

Predicate definitions and theorem suppliers are separate interfaces. Supplier modules in the current source provide smooth regularity/normality/dimension, normal-component openness, etale differential pullback, Noetherian Zariski dimension vanishing and quasi-compact separated field base change. The local guides name these results and retain their exact conditions. Current elaboration/audit coverage remains in [WORK_PLAN.md](WORK_PLAN.md).

## Latest tensor and derived boundaries

`SheafOfModulesOfCommRing.tensorLeftFunctor`/`tensorFunctor` is the single site tensor. `Scheme.Modules.moduleTensorLeftFunctor`, its right counterpart and invertible wrappers specialize that construction. Finite-locally-free left/right tensor `PreservesHomology` lives in the locally free exactness tier; generic symmetry depends on neither projection formula nor invertible sheaves.

The module projection-formula map is constructed for arbitrary coefficients. Its arbitrary-morphism isomorphism requires finite local freeness of the target coefficient; its closed-immersion module isomorphism does not. The D+ interface retains finite local freeness and its installed derived-unit equation.

`Scheme.Modules.Godement.godementTotal_shortExact` concerns the ordinary integer-complex category and has no boundedness premise. `godementTotalUnit_quasiIso_of_isStrictlyGE`, total homotopy and Plus/derived calculations retain actual lower bounds. Derived direct-image unit invertibility requires termwise flasqueness or the stated jointly covering target opens with flasque pullback restrictions. Flat-base-change unit comparison keeps the actual cartesian square and `Flat j`/`Flat a`; constructing it is not an unconditional base-change isomorphism.

Generic D+ term comparison keeps both lower and upper zero-term bounds. `exactDerivedContractionIso` needs additive `F,G`, homology preservation by `G` and a supplied `F ⋙ G ≅ Id` in the stated abelian/enough-injective/derived setting; only the one-sided derived isomorphism and original unit equation are supplied.

The tensor and derived constructions do not supply `ProperModuleCohomologyFinite` or `LocalFreeCohomologyBaseChange`. The pointwise fibre-dimension, smooth-rank and etale-differential results now have separate proved interfaces; those three obsolete global family requirements are retired. Downstream bridge retargeting is a separate acceptance question.

The ordinary module-complex layer constructs restriction and pullback on actual integer-indexed complexes. Open restriction preserves homology; pullback preservation retains flatness of the morphism. Left/right coefficient tensor preserves homology when the coefficient is finite locally free. Separately, an actual short exact sequence with finite locally free quotient remains short exact after tensor with an arbitrary coefficient sheaf, by local splitting. Acyclicity on an open means restriction to that displayed open is acyclic; flat pullback uses its actual inverse-image open. These statements need neither a term bound nor a perfect-complex predicate.

The bounded-below geometric pullback/direct-image unit is constructed for arbitrary morphisms. The Godement resolved composite inserts the actual totalization between these functors. Comparison with `derivedFlatPullbackPlus p ⋙ derivedPushforwardPlus p` retains `Flat p` and the canonical derived-category choices. Quasi-isomorphism of the displayed resolved unit and invertibility of the displayed derived unit are the respective inputs to the two transfer theorems; no universal unit-invertibility premise is inferred. Derived open-cover reflection separately assumes each actual local restriction/pullback is invertible, or each local object is zero.

Godement open-unit descent uses an actual cartesian square `IsPullback a b f j` with open immersions `a,j` and a bounded-below target complex. Its final restricted-unit quasi-isomorphism assumes that the displayed local resolved unit for `b` is a quasi-isomorphism. The total-image span uses bounded-below flasque terms; flatness of `f,b` is not a premise of this open descent theorem. This route is distinct from the flat derived-unit transfer.

## Mapping cones and sequential colimits

`CochainComplex.mappingCone.map_add` in `Aglib.Algebra.Homology.MappingCone.Map` gives additivity in the two maps of a commutative square of integer-indexed cochain complexes. It assumes only a preadditive category with binary biproducts, with independent object and morphism universes. The [mapping-cone guide](../Aglib/Algebra/Homology/MappingCone/README.md) distinguishes this general map interface from the identity-cone functor's abelian setting.

In an abelian coefficient category, the same [cone family](../Aglib/Algebra/Homology/MappingCone/README.md) supplies quasi-isomorphism of the literal cone map from quasi-isomorphisms of both endpoints. Its short-exactness theorem for a natural-transformation cone functor retains a preadditive source, additive endpoint functors and short exactness of both actual endpoint image sequences. These results require no term bounds. The [sequential-system family](../Aglib/CategoryTheory/Limits/Shapes/SequentialSystem/README.md) compares finite tails and, given the diagram's colimit, makes the original inclusion at a stage invertible when all successors from that stage are invertible. Its alternating-sign construction turns anti-commuting successor squares into natural transformations in a preadditive category; invertibility of the stage maps is required only for its isomorphism version. Exact imports, signs and colimit hypotheses are recorded in the family guides.

## Pointwise suppliers and canonical comparisons

[Finite local bases](../Aglib/AlgebraicGeometry/Modules/LocallyFree/README.md) give
`Scheme.Modules.moduleFibre_finite_and_finrank_eq_card` on the actual field fibre.
[Differentials](../Aglib/AlgebraicGeometry/Modules/Differentials/README.md) use
`Scheme.Modules.Differentials.differentialSheaf_hasRank_of_smooth` and the actual
etale `differentialPullbackMap`. Their rank and isomorphism constructors no longer
accept `LocalBasisFibreDimension`, `SmoothDifferentialRank` or
`EtaleDifferentialPullback`. `Modules/Differentials/Properties.lean` is retired;
its actual successor interfaces are in `SmoothRank.lean` and `EtalePullback.lean`.

[Affine base change](../Aglib/AlgebraicGeometry/Modules/BaseChange/Affine/README.md)
concerns the literal `moduleBaseChangeMap`, not an isomorphism of unrelated objects.
The fifteen old R5 Spec comparison interfaces remain unretired. Nineteen actual
map-equality witnesses pass native checks and independent PartB correspondence
review. Four R5 caller transports remain pending; no old producer/caller interface
is removed here. The accepted unit/counit/hom-equivalence equations are separate
from the finite-flat local-freeness property. Proper constants do not imply proper module-cohomology finiteness.

## Coherent quotient and Cartier boundaries

For an open immersion between locally Noetherian schemes, coherent restriction
has the coherent sheaves supported in the closed complement as kernel. The
proved quotient equivalence with coherent sheaves on the open assumes
`IsNoetherian X`. [Coherent extension](../Aglib/AlgebraicGeometry/Modules/Coherent/Extension/README.md)
means an extension with an isomorphism after restriction; it is distinct from
extension by zero, which generally does not preserve quasicoherence.

[Cartier ideal criteria](../Aglib/AlgebraicGeometry/EffectiveCartierDivisor/Smooth/README.md)
retain smooth relative dimension one, a closed immersion and the separately
stated finite, flat and locally finitely presented composite at their finite-flat
root. Their bases can be nonreduced and non-Noetherian. The lower ideal-kernel
comparisons keep their quotient-flatness and actual scalar-square conditions.
