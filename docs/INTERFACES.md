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

The affine module-base-change theorem now has the unconditional supplier
`Scheme.Modules.affineModuleBaseChange` in
`Aglib.AlgebraicGeometry.Modules.BaseChange.Affine`.
`moduleBaseChangeMap_isIso` concerns the original counit mate for affine `f`,
quasicoherent coefficients and arbitrary `g`; it has no flatness, finiteness or
Noetherian premise. The retained `AffineModuleBaseChange` proposition and older
parameterized consumers remain available, with this proof as their input.

An arbitrary structural ring map `α : R →+* Γ(X, ⊤)` acts on the unchanged
`Sheaf.H` through `moduleCohomologyModuleOfHom`. This action is explicit in `α`
to distinguish different structural maps. The general Cech linear computation
and geometric module-coefficient maps preserve that action and the original
degree-zero comparison. Their construction does not assume flatness or finite
generation. For a quasi-compact separated `f : X ⟶ Spec A`, a flat ring map
`A → B` and any quasicoherent module coefficient, the
[general module base-change supplier](../Aglib/AlgebraicGeometry/Cohomology/BaseChange/Modules/Separated.lean)
now proves invertibility of the original `moduleCohomologyBaseChangeMap` in
every nonnegative degree. Its unit-pure-tensor formula is the actual geometric
cohomology pullback. The [qcqs supplier](../Aglib/AlgebraicGeometry/Cohomology/BaseChange/Modules/Qcqs.lean)
extends this to quasi-compact quasi-separated `f` in every degree, and to
an arbitrary supplied Cartesian square over the same ring map, with the
original unit and tensor mate. `BaseChange/Derived/Locality` now proves
invertibility of that installed derived comparison over arbitrary bases,
for a Cartesian square with flat base-change morphism `j`, qcqs original
morphism `f` and QC original homology on D+.
`BaseChange/HigherDirectImage` gives the actual native higher-image map, its
exact homology formula and QC isomorphism theorem.

Original module-linear Ext from the structure module now computes the same
additive cohomology in every degree, linearly for the specified structural
ring map. The forward map is native exact scalar forgetting and the original
integer-generator-one map. Coefficient maps, Yoneda composition and degree-zero
section evaluation are explicit. The native long exact sequence and its
Noetherian finite-generation transfers use the same original objects; the
existing field-linear exactness interfaces specialize this implementation.

On actual polynomial projective space over an arbitrary commutative ring,
every integer twist has finite free cohomology in all degrees. Over a
Noetherian base ring, every coherent coefficient has finite cohomology in
every degree, proved from actual finite negative-twist presentations and
coherent kernels. The same conclusion holds through an actual closed
immersion into that projective space, using the original pushforward
cohomology comparison and displayed structural factorization. The
Noetherian proper theorem is now proved by closed-support induction, and
its coherent higher-image statement descends to every locally Noetherian
target. `Cohomology/Proper/Field` supplies the retained all-field module and
structure-sheaf finiteness families with their original objects and actions.

The lower finite-complex numerical interfaces concern the original native
residue-field scalar-extension complexes: their homology dimensions are
upper semicontinuous for finite projective terms, and their native
homological Euler characteristic is locally constant when those terms are
bounded. The latter only requires finitely presented flat terms. A geometric
consumer must supply an actual comparison with its original fibre
cohomology; these statements alone do not discharge a proper base-change
or local-freeness family.

For an actual closed projective embedding over a Noetherian commutative
base and a coherent relatively flat coefficient, the constructed universal
finite-projective model now supplies that geometric comparison. Every
original ordinary fibre-cohomology dimension is upper semicontinuous, and
their intrinsic alternating sum is locally constant. These public endpoints
construct the model internally and retain the original structural actions.
The original degreewise base-change map is identified with the native
homology mate of the same model by a full linear square. Over a reduced
Noetherian affine base, local constancy of an original fibre dimension
gives finite projective original cohomology and arbitrary original base
change. Over a Noetherian local base, the original residue-field
surjectivity criterion gives arbitrary base change and the adjacent-degree
freeness criterion, without reducedness. The actual sheaf-valued `Rf_*` of
this coherent relatively flat coefficient also has a constructed strict
perfect model, both before and after every ring base change. Its
comparison uses the original injective resolution, actual tilde--Gamma
counit and installed derived unit. The same sole finite-cover model is now
supplied for proper morphisms over
Noetherian affine bases in `Proper/FiniteModel`, including this one-model,
all-ring strict-perfect direct-image statement. Proper upper semicontinuity,
intrinsic Euler local constancy and nonreduced local base-change/freeness
criteria consume this same model and the original maps. Reduced-base
Grauert and the geometric basic-open neighbourhood criterion are proved
on those original maps. The latter gives every composite base-change map
on a neighbourhood from residue-field surjectivity. The intrinsic
point-fibre comparison also gives upper semicontinuity and intrinsic Euler
local constancy over every locally Noetherian target. If that target is reduced and the actual fibre dimension
is locally constant, the original higher direct image is finite locally
free; the target need not be quasi-compact. General nonflat sheaf-valued
base-change comparison remains a separate construction.
Arbitrary perfect-coefficient direct images remain a separate endpoint.

The actual relative differential sheaf for an arbitrary scheme morphism
is owned by `Modules/Differentials/Relative/Basic`. It represents native
relative derivations against every coefficient module sheaf, retains the
original `f.c` differential and its restriction formulas, and has no
quasicoherence, smoothness or base-field premise. The affine-base comparison
to constant-base derivations is proved for every coefficient sheaf. The
actual Spec-map/tilde comparison retains the original principal-open
differentials. Actual open-restriction comparisons and native
standard-smooth charts prove finite local freeness and rank n for every
smooth morphism of fixed relative dimension n over an arbitrary base.
The [global projective Euler and determinant family](../Aglib/AlgebraicGeometry/ProjectiveSpace/Differentials/README.md)
identifies actual top differentials with `O(-n-1) ⊗ π*det(V)` and, after the
displayed ordered degree-one coefficient frame, with `O(-n-1)`. Original
chart maps, wedge formulas and order-change signs are retained.

The [projective Serre duality family](../Aglib/AlgebraicGeometry/Cohomology/Duality/Projective/README.md)
proves full complementary-degree coherent Serre duality on polynomial
projective space over a field, including the original Yoneda/residue
pairing, perfectness, coefficient naturality and dimension zero. The top
Hom/cohomology duality also holds over every Noetherian commutative base
ring. The [derived comparison](../Aglib/AlgebraicGeometry/Cohomology/Duality/Projective/Derived/README.md)
now identifies every nonnegative Ext group of a coherent module into the
original dualizing twist with Hom from its actual RΓ to the shifted
single-term base module, over every Noetherian commutative ring. The
forward map is the original trace after the installed derived functor.
The same affine theorem allows every native base module J, with target
`J[i-n]` and no flatness, finiteness, projectivity or injectivity of J.
There is no source-flatness, perfectness or base-regularity premise;
higher base-ring Ext is retained in dimension zero.

The [relative family](../Aglib/AlgebraicGeometry/Cohomology/Duality/Projective/Relative/README.md)
uses a supplied Cartesian projective-space square. Its derived differential
trace exists over a separated scheme base for every quasicoherent coefficient
N. The same comparison is a structural-scalar linear equivalence in every
natural Ext degree for a coherent source over a Noetherian separated base;
the projective presentation ring need not be Noetherian. Transfer through a
chosen closed embedding retains the actual `Ri!((∧ⁿ Ω_p) ⊗ p*N)`.

[Canonical](../Aglib/AlgebraicGeometry/Cohomology/Duality/Projective/Canonical.lean)
identifies `Ri!(∧ⁿ Ω_p)` with `single_(n-d)(∧ᵈ Ω_(i≫p))` for a closed
immersion i with p smooth of relative dimension n and i≫p smooth of relative
dimension d, over an arbitrary base without separation or Noetherianity.
There is no global `d ≤ n` premise. The chosen smooth-embedding coherent
duality over a Noetherian separated base has target the structure-module
single shifted by `r-d`; its forward map is derived pushforward followed by
one original trace. This is the unit-coefficient specialization. General
coefficients retain the actual right-adjoint value; arbitrary-coefficient
purity, embedding independence, internal RHom/coefficient complexes and
general proper dualizing complexes remain separate.

## Retained theorem-family interfaces

These proposition-valued families quantify over actual objects and
constructed maps. Some legacy consumers retain them as parameters; the
proved suppliers below can now discharge the proper-finiteness inputs.

| Native input owner | Conditions and conclusion |
| --- | --- |
| `AlgebraicGeometry.Scheme.Cohomology.ProperModuleCohomologyFinite` | Supplied by `properModuleCohomologyFinite`: proper field scheme, finitely presented coefficient, every nonnegative degree, original field action. |
| `AlgebraicGeometry.Scheme.ProperStructureCohomologyFinite` | Supplied by `Scheme.Cohomology.properStructureCohomologyFinite` through the original scalar-compatible structure-module comparison. |
| `AlgebraicGeometry.Scheme.ProperGeometricallyIntegralConstants` | Proper geometrically integral field scheme: the actual structural constant map is bijective. |
| `AlgebraicGeometry.Scheme.Cohomology.LocalFreeCohomologyBaseChange` | Proper, locally finitely presented, flat `f`; locally free/finitely presented coefficients; geometric fibre cohomology concentrated in degree zero of rank `r`: direct image has rank `r`, and its actual mate is invertible after every change of base. |

Predicate definitions and theorem suppliers are separate interfaces. Current suppliers include proper coherent finiteness, actual arbitrary-base fixed relative differential rank, smooth regularity/normality/dimension, normal-component openness, etale differential pullback, Noetherian Zariski dimension vanishing, affine module base change and qcqs flat base change over arbitrary bases. The former `SmoothDifferentialRank` input is retired: `differentialSheaf_hasRank_of_smooth` and `relativeDifferentialSheaf_hasRank_of_smooth` prove the actual rank without a supplied family. The empty `Properties` entry is retired; its actual successors are `SmoothRank`, `EtalePullback` and the general relative differential family. The local guides name these results and retain their exact conditions. Current elaboration/audit coverage remains in [WORK_PLAN.md](WORK_PLAN.md) and the focused [cohomology plan](COHOMOLOGY_PLAN.md).

For proper geometrically integral field schemes,
`Scheme.constants_bijective_of_proper_geometricallyIntegral` proves bijectivity
of the original constants map and supplies the retained
`ProperGeometricallyIntegralConstants` predicate. The local-base-dimension
family is retired in favor of the actual pointwise fibre-dimension proof.

## Latest tensor and derived boundaries

The existing [perfect-complex family](../Aglib/AlgebraicGeometry/Modules/PerfectComplexes/README.md)
uses actual integer module-sheaf complexes and actual derived isomorphisms.
`strictPerfect` requires bounds on terms and finite local freeness in every
degree. `locallyPerfect` requires strict derived models on neighborhoods;
`HasStrictModel` instead supplies one model over the whole displayed scheme.
Local perfectness gives quasicoherent homology and local cohomological
bounds; quasi-compactness gives one global cohomological bound. It does not
give a global strict model, and this family alone does not prove that a
proper direct image is perfect.

`SheafOfModulesOfCommRing.tensorLeftFunctor`/`tensorFunctor` is the single site tensor. `Scheme.Modules.moduleTensorLeftFunctor`, its right counterpart and invertible wrappers specialize that construction. Finite-locally-free left/right tensor `PreservesHomology` lives in the locally free exactness tier; generic symmetry depends on neither projection formula nor invertible sheaves.

The module projection-formula map is constructed for arbitrary coefficients. Its arbitrary-morphism isomorphism requires finite local freeness of the target coefficient; its closed-immersion module isomorphism does not. The D+ interface retains finite local freeness and its installed derived-unit equation.

`Scheme.Modules.Godement.godementTotal_shortExact` concerns the ordinary integer-complex category and has no boundedness premise. `godementTotalUnit_quasiIso_of_isStrictlyGE`, total homotopy and Plus/derived calculations retain actual lower bounds. Derived direct-image unit invertibility requires termwise flasqueness or the stated jointly covering target opens with flasque pullback restrictions. Flat-base-change unit comparison keeps the actual cartesian square and `Flat j`/`Flat a`; constructing it is not an unconditional base-change isomorphism.

The older generic D+ term comparison keeps both lower and upper zero-term bounds. The native Postnikov comparison also handles bounded-below objects using single original homology layers and lower-bound preservation, without an output upper bound or termwise-QC premise. `exactDerivedContractionIso` needs additive `F,G`, homology preservation by `G` and a supplied `F ⋙ G ≅ Id` in the stated abelian/enough-injective/derived setting; only the one-sided derived isomorphism and original unit equation are supplied.

The specific geometric proofs supply proper field-scheme finiteness and
smooth differential rank. The pointwise fibre-dimension, smooth-rank and
etale-differential interfaces have proved suppliers, and their obsolete
global packages are retired. The full `LocalFreeCohomologyBaseChange`
family remains an explicit input. Existing downstream parameterized bridges
are a separate retargeting question.

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
`EtaleDifferentialPullback`. `Modules/Differentials/Properties.lean` is retired; its actual successor
interfaces are in `SmoothRank.lean` and `EtalePullback.lean`.

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

## Milnor K-theory

The [Milnor family](../Aglib/KTheory/MilnorK/README.md) owns `MilnorK.K F n`,
the actual integer symbol quotient for every nonnegative degree. Field maps
allow independent universes; concatenation, low-degree comparisons and tame
residues use the same groups and original ordered symbols. The tensor models
are nested under `MilnorK.K2` and `MilnorK.K3`; they are compared explicitly.
Specialization retains a uniformizer, while residue independence has its own
proved normalization/compatibility conditions. General finite-extension norms
and their tower theorem currently require characteristic zero, the actual
algebra structures and finite-dimensional/tower hypotheses. Motivic diagonal,
Quillen and endpoint-cycle comparisons remain downstream.

## Fundamental groups, monodromy and finite-coefficient etale H1

The [selected R5 migration](migration/r5-fundamental-groups.json) uses the
actual native finite-etale category and its specified field-valued fibre
functor. `Scheme.EtaleFundamentalGroups` constructs fibre automorphism groups,
evaluation topologies, scheme-induced maps and section retractions. The field
absolute-Galois identification retains its displayed characteristic-zero
hypothesis; individual forward constructions keep their original assumptions.
The geometric-kernel endpoints retain qcqs, the actual rational section and
its equation, with every additional wrapper hypothesis and named input kept
where displayed. Namespace relocation does not supply a Galois-category,
fibre-functor, descent or exactness premise accepted by another interface.

General connected-scheme Galois dictionaries, finite-etale classification and
marked-kernel/group-scheme monodromy use their actual objects and displayed
conditions. `Scheme.EtaleH1` denotes the actual small-etale Ext H1 surface;
finite-coefficient comparisons retain their `HasSheafify`/`HasExt` universes,
positive globally invertible annihilating level, local trivializations,
markings, point hypotheses and actual forward-map conventions. Generic GC/FF
and theorem-family inputs remain explicit wherever present. Actual Tate
coefficient sheaves and specialized curve, elliptic, arithmetic and K/G/Q/S
applications remain downstream. The post-lint 190-module closure and both
focused public clients compiled. The record separates 56 compiler-local
exceptions from 114 environment-lint entries that preserve original input types,
simp registrations and instance behavior. Actual style and 15 environment linters
passed. Fresh independent replay covered all 190 selected native modules and
5,117 nonvacuous declarations, with no replay reuse; current end-identity guards
passed. The two compiled public examples contain zero stored kernel declarations
and carry no additional replay claim. Standard-foundation audit coverage retains
186 origins under the recorded preservation conditions and freshly checks four.
Publication and separate R5 adoption remain pending. These checks discharge no
theorem-family input and establish no new mathematical status.
