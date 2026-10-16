# Sources and organization references

The maintained interfaces extend Lean 4.34.1 and Mathlib `d13f23b723b8a846827a245b89c10fc7d3f11612`. Module comments and migration records identify the exact original source, selected mathematical statements and canonical maps. Historical source paths are provenance; current family guides and import surfaces give the maintained owners. Source correspondence does not by itself establish compilation or theorem acceptance.

## Initial extraction basis

The initial extraction basis was R5Lab `95a3772b895fbc19a81684be4ffd519d0fdcd6b3` and the then-selected local Quillen release `189a8e779f0c68b2dfc6f8195daebb3e684a5905` at `tmp/output/quillen-library-release/quillen-k-theory`. The initial 133 selected files from Quillen `83629578a3d70787d41ec631f5234af8758716af` are byte-identical in the local release; that is a bounded source comparison, not a claim about every file in the older tree. The package pins Lean 4.34.1 and Mathlib `d13f23b723b8a846827a245b89c10fc7d3f11612`; the local Mathlib checkout's HEAD was checked against that pin. Contributor/license headers and exact source comments remain with the implementation.

[Migration fragments](migration) record original file identities, selected source ranges and declaration correspondence for [ring theory](migration/ring-theory.json), [category/homology](migration/category-homology.json), [scheme operations](migration/scheme-operations.json), [general geometry](migration/general-geometry.json) and [cohomology](migration/cohomology.json). [module-map.json](module-map.json) anchors the initial path refactor; [namespace-map.json](namespace-map.json) records native-owner correspondence. Later substantive source cuts retain their own recorded locators. Original application/implementation snapshots are provenance, not proof claims for their complete source applications.

## Inspected reference crosswalk

The crosswalk below records actual files at the Mathlib pin; [ARCHITECTURE.md](ARCHITECTURE.md) states the overall ownership and extension principles. For example, native `AlgebraicGeometry/Modules/{Presheaf,Sheaf,Tilde}.lean` and `Algebra/Category/ModuleCat/Sheaf/{Quasicoherent,Generators,LocallyFree}.lean` support the module-sheaf hierarchy; `CategoryTheory/Sites/SheafCohomology/{Basic,Cech,ExactSequences}.lean` supplies the generic cohomology layer. The library's focused subfamilies extend these objects and result areas.

The [Stacks Project table of contents](https://stacks.math.columbia.edu/browse) identifies the relevant subjects: Chapter 10, Commutative Algebra; 12, Homological Algebra; 17, Sheaves of Modules; 18, Modules on Sites; 20, Cohomology of Sheaves; 21, Cohomology on Sites; 26, Schemes; 28, Properties of Schemes; 29, Morphisms of Schemes; 30, Cohomology of Schemes; 33, Varieties; and 35, Descent. Their separation guides the commutative-algebra, generic-sheaf/site and scheme-specialized owners. It does not itself attribute a theorem to an uninspected chapter passage.

Robin Hartshorne's [*Algebraic Geometry*](https://link.springer.com/book/10.1007/978-1-4757-3849-0), Graduate Texts in Mathematics 52, has Schemes (pp. 60–200) and Cohomology (pp. 201–292) before Curves and Surfaces in the inspected publisher TOC. That division informs the route from actual scheme modules to their general cohomology, leaving the specialized applications external.

Alexander Grothendieck's [EGA I, *Le langage des schémas*](https://www.numdam.org/item/PMIHES_1960__4__5_0/), Publications Mathématiques de l'IHÉS 4 (1960), pp. 5–228, supplies the scheme-language orientation. The NUMDAM catalog record was inspected; no EGA theorem number or applicability is inferred from that record. [Mathlib naming conventions](https://leanprover-community.github.io/contribute/naming.html) and [source style](https://leanprover-community.github.io/contribute/style.html) guide identifiers and source presentation.


## Pinned subject crosswalk

These concrete paths were inspected at the stated Mathlib revision. The library extends the subjects with occupied local families; it does not assert an identical directory hierarchy.

| Library subject | Actual Mathlib basis | Reference subjects |
| --- | --- | --- |
| Ring algebra, length and regular-local theory | `RingTheory/{Length,FiniteLength}.lean`, `RingTheory/RegularLocalRing/{Defs,Polynomial}.lean`, `RingTheory/KrullDimension/Basic.lean` | Stacks Chapter 10, Commutative Algebra |
| Tensor products and descent | `RingTheory/TensorProduct/Basic.lean`, `RingTheory/{Etale,Finiteness,Flat/FaithfullyFlat}/Descent.lean` | Stacks Chapter 10 and 35, Descent |
| Module categories and site tensors | `Algebra/Category/ModuleCat/{ChangeOfRings,Localization}.lean`, `Presheaf/Monoidal.lean`, `Sheaf/{Colimits,Quasicoherent,Generators,LocallyFree}.lean` | Stacks Chapters 17–18, Sheaves of Modules / Modules on Sites |
| Generic complexes, injectives and D+ | `Algebra/Homology/{TotalComplex,CochainComplexPlus}.lean`, `DerivedCategory/{Plus,ShortExact,RightDerivedFunctorPlus}.lean`, `CategoryTheory/Abelian/Injective/{Resolution,Ext}.lean` | Stacks Chapters 12–13, Homological Algebra / Derived Categories |
| Generic site and topological sheaves | `CategoryTheory/Sites/SheafCohomology/{Basic,Cech,ExactSequences}.lean`, `Topology/Sheaves/{Stalks,Skyscraper,Flasque,MayerVietoris}.lean`, `Topology/{KrullDimension,Sober,NoetherianSpace}.lean` | Stacks Chapters 20–21, Cohomology of Sheaves / Cohomology on Sites |
| Scheme modules and local/morphism properties | `AlgebraicGeometry/Modules/{Presheaf,Sheaf,Tilde}.lean`, `Properties.lean`, `Noetherian.lean`, `Stalk.lean`, `Morphisms/{Finite,Smooth,Etale,ClosedImmersion}.lean` | Stacks Chapters 26, 28–29 and 33; Hartshorne's Schemes; EGA I scheme language |
| Scheme-specialized cohomology and canonical maps | Native site `Sheaf.H`, actual scheme module sheaves and their scalar/functor interfaces | Stacks Chapter 30, Cohomology of Schemes; Hartshorne's Cohomology |


## Theorem-source boundary

Exact proof attributions belong to the implementing module comments, with the stated hypotheses and constructed map. Preserve persistent Stacks tags and locators only for their identified source results. A derived corollary retains its disclosed extra identifications; sharing a tag does not make it the source's literal statement.

Local-basis fibre dimension now has a native pointwise proof. Proper module finiteness and relative locally free base change retain their explicit inputs and original inspected-source boundaries. The relative corollary identifies actual pushforward, the adjunction mate and geometric fibres in addition to its cited derived results. Documentation does not independently establish those external proof chains. Unchecked load-bearing attribution must remain marked rather than acquiring guessed metadata or unconditional status.

## Latest local source selections

[latest-quillen](migration/latest-quillen.json) records the local source-authority comparison. [latest-scheme](migration/latest-scheme.json) records the fixed generic scheme/tensor/Godement selections and their exact cuts. [latest-homology](migration/latest-homology.json) records the twelve generic bounded derived/truncation/comparison leaves. [latest-general-cuts](migration/latest-general-cuts.json) records the four independent affine-induction, zero-section, good-truncation and cartesian-open roots and the eighteen coupled lower destinations. Multi-source leaves have separate rows for their exact original-source selections. These include generic cone/sequence and coefficient primitives, ordinary module-complex operations, locally split tensor, actual Godement carrier/unit/open comparisons and derived locality. Original containing PerfectComplexes/projective-line paths are source locators, not production imports or wholesale admission.

The extended organization crosswalk includes Stacks Chapter 13, Derived Categories, alongside Chapters 12, 17–18 and 20–21 for the generic derived/site tensor layer. At the Mathlib pin, `Algebra/Homology/DerivedCategory/{Plus,ShortExact,RightDerivedFunctorPlus}.lean`, `CategoryTheory/Triangulated/Functor.lean`, `Algebra/Homology/Embedding/CochainComplex.lean`, `Algebra/Category/ModuleCat/Presheaf/Monoidal.lean` and `Sheaf/Colimits.lean` were checked as actual source paths. These are organization/source-interface correspondences, not new external theorem attributions.

The subsequent source-placement review also inspected the Stacks chapter tables
for [Morphisms of Schemes (01QL)](https://stacks.math.columbia.edu/tag/01QL),
[Derived Categories of Schemes (08CU)](https://stacks.math.columbia.edu/tag/08CU),
[Etale Morphisms of Schemes (024J)](https://stacks.math.columbia.edu/tag/024J)
and [Fundamental Groups of Schemes (0BQ6)](https://stacks.math.columbia.edu/tag/0BQ6).
They support the subject distinctions used in the architecture. In particular,
the derived-scheme chapter explicitly names perfect complexes; it does not
justify abbreviating the object to `Perfect` under a module-sheaf parent. These
are classification references, with no theorem-source applicability claim.

[The next group projection](migration/pointwise-cartier-coherent.json) records exact
original/current source identities, the final pointwise names, the fifteen
unretired Spec comparison obligations, and separate native/review states for
pointwise, Cartier and coherent groups. Earlier migration ledgers and their
original source IDs, paths, revisions and hashes remain unchanged.
