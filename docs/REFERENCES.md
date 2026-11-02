# Sources and organization references

The maintained interfaces extend Lean 4.34.1 and Mathlib `d13f23b723b8a846827a245b89c10fc7d3f11612`. Module comments and migration records identify the exact original source, selected mathematical statements and canonical maps. Historical source paths are provenance; current family guides and import surfaces give the maintained owners. Source correspondence does not by itself establish compilation or theorem acceptance.

## Initial extraction basis

The initial extraction basis was R5Lab `95a3772b895fbc19a81684be4ffd519d0fdcd6b3` and the then-selected local Quillen release `189a8e779f0c68b2dfc6f8195daebb3e684a5905` at the historical checkout path `tmp/output/quillen-library-release/quillen-k-theory`.
That temporary path is a provenance locator, not a required live source checkout. The initial 133 selected files from Quillen `83629578a3d70787d41ec631f5234af8758716af` are byte-identical in the local release; that is a bounded source comparison, not a claim about every file in the older tree. The package pins Lean 4.34.1 and Mathlib `d13f23b723b8a846827a245b89c10fc7d3f11612`; the local Mathlib checkout's HEAD was checked against that pin. Contributor/license headers and exact source comments remain with the implementation.

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

## Supplied Motivic Koszul selection

[motivic-koszul](migration/motivic-koszul.json) records the selected eighteen
generic source leaves from the user-supplied archive
`motivic-cohomology-complete-current742-source-m27-20261016T002808.167583Z.tar.gz`.
The user authored this independent library and authorized early reuse of
needed foundations. Original contributor and Apache notices are retained.
The record keeps archive and per-source hashes, current destination hashes,
native owners and focused verification receipts. This is a bounded source
selection, not admission or verification of the complete independent library.
Actual finite Koszul complexes, signed maps and regular-sequence quotient
resolutions now live under `ChainComplex.Koszul`; the elementwise criterion
belongs to `CategoryTheory.ShortComplex`. Geometric purity and determinant
identifications are separate consumers.

[upstream-derived](migration/upstream-derived.json) records six exact generic
adjunction/K-injective leaves selected from local Aglib main `f87a691`, with
unchanged destination bytes and their independent public consumer. This
source is distinct from the fetched remote main. Later root-authored
injective-complex and original unit-comparison leaves have their own native
owners and are not represented as unchanged upstream selections.

[upstream-smooth-differentials](migration/upstream-smooth-differentials.json)
records the minimal four-leaf selection from local Aglib main `40af743`.
It supplies the canonical affine differential comparison, standard-smooth
bases and the actual field-scheme smooth-rank theorem, preserving the
source's earlier R5 provenance in each header. The record includes exact
source/destination hashes and independent public verification. It does not
attribute exterior, determinant or duality identifications to that source.

## Relative Euler sequence and determinant normalization

[Stacks Section 50.11](https://stacks.math.columbia.edu/tag/0FMG), especially
Lemma 50.11.1, gives the standard-chart Euler maps and the top differential
twist calculation over a ring. Its stated range starts at positive projective
dimension; the formal dimension-zero case is checked separately.
[Section 27.21](https://stacks.math.columbia.edu/tag/01OA) fixes the quotient
convention for projective bundles, and [Section 17.26](https://stacks.math.columbia.edu/tag/0B37)
gives the determinant rule for an exact sequence of finite locally free
sheaves. The coordinate-free det(V) factor in the cohomology plan is a
mathematical deduction from these constructions. The actual Euler maps,
exactness, determinant comparison and trace normalization now have native
suppliers in the [projective differential guide](../Aglib/AlgebraicGeometry/ProjectiveSpace/Differentials/README.md)
and [canonical purity theorem](../Aglib/AlgebraicGeometry/Cohomology/Duality/Projective/Canonical.lean).
The [relative-duality guide](../Aglib/AlgebraicGeometry/Cohomology/Duality/Projective/Relative/README.md)
retains the Noetherian separated-base and chosen-embedding conditions; no
external source statement is inserted as a mathematical assumption.

## General Milnor K-theory

[motivic-milnor-k](migration/motivic-milnor-k.json) records the source-preserving
migration from `kangxyz/motivic` revision
`b368f6965228e63643380033ec224335bcd24a2c`. The general symbol, residue and
norm implementations and their necessary algebraic prerequisites have native
Aglib owners. Two endpoint geometry/cycle consumers remain downstream. The
record separates actual moves, native reuse and the small generic polynomial
cut. Original source identities are retained.

## Fundamental groups and finite-coefficient etale H1

The [R5 source correspondence](migration/r5-fundamental-groups.json) records
190 modules from `kangxyz/r5-lab` revision
`c82abf3a72ce1e1cedf4a4f1fe08bea994ad4df5`, selected against Aglib
`64374534558c80c2fec996ee06bf7727b6c7f3e4`. This source revision is a local R5
checkpoint; it is not pushed as part of this Aglib migration. The selection
contains the actual
finite-etale fibre automorphism groups, functorial maps and sections, field
restriction and absolute-Galois comparisons, geometric-kernel exactness,
general Galois-category/monodromy companions and actual finite-coefficient
small-etale H1 comparison endpoints with their required lower dependencies.
Per-source and destination hashes and exact native correspondences retain the
original hypotheses, universes and explicit inputs. Specialized curve,
elliptic, Tate coefficient-sheaf, arithmetic and K/G/Q/S applications remain
downstream; this selection adds no G017 work. The post-lint source record binds the compiled 190-module closure and two
focused public clients, the final native name/kind correspondence, explanatory
API comments and exact declaration-local lint exceptions. Actual style and
15 environment linters and fresh selected 190 kernel replay passed, with 5,117
nonvacuous declarations and zero reused replay modules. Standard-foundation
coverage combines 186 retained origins with four freshly audited origins under
the recorded preservation conditions. R5 adoption is recorded downstream on its
own pin and consumer basis. Earlier source and compiled receipts retain their
own basis.

## Castelnuovo–Mumford regularity and Mumford's bound

Nitin Nitsure's [*Construction of Hilbert and Quot Schemes*](https://arxiv.org/abs/math/0504590v1),
arXiv:math/0504590v1 [math.AG], submitted 29 April 2005, 36 pages; the arXiv abstract page was
inspected and lists no journal reference. Its §2 gives the definition of `m`-regularity (p. 9),
the restriction to a general hyperplane (pp. 9–10), Lemma 2.1 (pp. 10–11), Remark 2.2 and
Theorem 2.3 (p. 11) with its proof (pp. 12–13); `Cohomology/Projective/Regularity` cites these
pages of the v1 PDF. The family README records where the formal route departs from p. 13.
Its §3, Lemmas 3.1 and 3.2 (pp. 13–15) with Theorem 3.7 (pp. 17–18), and §4, Lemma 4.1 to
Theorem 4.3 (pp. 18–23), are cited by `Cohomology/Projective`, `FlatteningStratification`,
`Modules/Flat/Generic` and `Modules/Flat/Relative`, `RingTheory/GenericFreeness`,
`RingTheory/FittingIdeal` and `Topology/NoetherianSpace`; the module documentation of
`LargeTwistBaseChange` records the gap and misprints on p. 14.

David Mumford's
[*Lectures on Curves on an Algebraic Surface*](https://press.princeton.edu/books/paperback/9780691079936/lectures-on-curves-on-an-algebraic-surface),
with a section by G. M. Bergman, Annals of Mathematics Studies 59, Princeton University Press,
1966, xi + 200 pp.; the publisher page and the
[CiNii record](https://ci.nii.ac.jp/ncid/BA0369913X) were inspected. It is Nitsure's source
[M] (p. 36) for Theorem 2.3. No lecture or page of it was inspected, so no statement is
attributed to a particular lecture.


## The Picard scheme

Steven L. Kleiman's [*The Picard scheme*](https://arxiv.org/abs/math/0504020v1),
arXiv:math/0504020v1 [math.AG], submitted 1 April 2005, 83 pages; the arXiv abstract page was
inspected. Its comments describe the paper as expanded notes on the author's lectures at the
ICTP Advanced School in Basic Algebraic Geometry, 7–18 July 2003, and it lists no journal
reference. Page numbers are those of the v1 PDF. The standing conventions (p. 15: locally
Noetherian schemes, a fixed separated map of finite type), 3.1 and Definition 3.3 (p. 22),
Lemma 3.4 with its proof (pp. 22–23), Definition 3.6 with its functoriality remark (p. 23) and the
proof of Theorem 3.7 (p. 24) are cited by `EffectiveCartierDivisor/Relative`. The families
`Picard`, `Picard/Comparison`, `Cohomology/Proper/StructureSheaf` and
`CategoryTheory/Sites/Descent` cite other sections at their own locators.

## Curves, Jacobians and étale duality

These references supply the identified source basis and exact-version locators
for the [Jacobian and curve-cohomology plan](JACOBIAN_PLAN.md). The existing
[Kleiman entry](#the-picard-scheme) remains the Picard bibliography owner.
Inspected passages and source obligations are distinguished in the plan;
bibliographic identity does not establish an imported theorem or proof chain.

### StacksProject

The Stacks Project Authors, *The Stacks Project*, 2026,
[project site](https://stacks.math.columbia.edu). The curve investigations used
chapter PDFs at version `ed88ff78`, compiled 14 July 2026. Persistent tags are
the primary locators: 03RN, 03RQ, 03RR and 0AMB for divisibility, curve
cohomology and degree; 0BA0 for Picard/Jacobian geometry; 0BDP, 0BF0,
0BF2–0BF4 for seesaw/cube suppliers; 0BF7, 0BFA, 0BFG, 0BFH and 0C1Z for
abelian varieties, multiplication and curve torsion. Each use retains the
tagged proof's actual hypotheses, including its base-change requirements.

### Milne2013LecturesEtaleCohomology

James S. Milne, *Lectures on Étale Cohomology*, version 2.21, 22 March 2013,
[author's course notes](https://www.jmilne.org/math/CourseNotes/LEC.pdf).
Locators use the printed pagination of that version: 14.2, 14.5, 14.7 with
Steps 0–7 (pp. 94–96), 14.12, 14.20–14.21 (pp. 101–103), and the Yoneda
pairing on p. 103. The omitted diagram arguments and the references to
*Étale Cohomology* (EC), including p. 177, are not supplied by this entry.
That book was not inspected for this programme (**citation needed**).

### SGA4Tome3

Michael Artin, Alexander Grothendieck and Jean-Louis Verdier,
*Théorie des topos et cohomologie étale des schémas (SGA 4), Tome 3*,
Lecture Notes in Mathematics 305, Springer, Berlin, 1973;
DOI `10.1007/BFb0070714`. The inspected
[LaTeX re-edition](https://www.normalesup.org/~forgogozo/SGA4/tomes/tome3.pdf)
is version `71766d9`, 30 July 2024. Its pagination differs from the original;
original page numbers appear in the margins. The programme uses exposé IX
4.7 and exposé XVIII 1.1.3, with the further derived suppliers explicitly
identified when needed.

### SGA4Half

Pierre Deligne, *Cohomologie étale*, Lecture Notes in Mathematics 569,
Springer-Verlag, Berlin, 1977; DOI `10.1007/BFb0091516`.
This is SGA 4½, with the collaboration of J. F. Boutot, A. Grothendieck,
L. Illusie and J. L. Verdier. The inspected
[1977 scan](https://websites.math.leidenuniv.nl/edixhoven/teaching/2015-2016/TAG/SGA4.5.pdf)
uses printed pagination six pages behind the PDF page number. Formula
inspection used the page images. Relevant locators are [Cycle]
1.1.1–1.1.6 (printed pp. 131–132) and 2.1.2–2.1.5; [Dualité] 1.3,
2.1–2.5, 3.2 and 3.4; and [Arcata] VI (2.3.3), printed p. 70.
The last formula fixes the source torsor/Abel–Jacobi sign; the plan retains
the separate comparison with Aglib's conventions.

### Milne2021JacobianVarieties

J. S. Milne, *Jacobian Varieties*,
[corrected author version](https://www.jmilne.org/math/xnotes/JVs.pdf),
12 June 2021, of Chapter VII in *Arithmetic Geometry* (1986), pp. 167–212,
with unchanged numbering. The plan uses 5.1 and 6.6–6.11; locators referring
to printed p. 16 or p. 22 use this author copy. Its theta construction uses
the specified rational base point. Its fibre-length argument retains the
actual geometric hypotheses described in the plan.

### Milne1986AbelianVarieties

James S. Milne, “Abelian Varieties,” in Gary Cornell and Joseph H. Silverman
(eds.), *Arithmetic Geometry*, Springer, New York, 1986, pp. 103–150;
DOI `10.1007/978-1-4613-8655-1_5`.
The inspected [corrected author text](https://www.jmilne.org/math/xnotes/AVs.pdf)
is dated 2 January 2022. The plan's “AVs” locators use this author-copy
pagination and result numbering, including 7.1–7.2, 8.2–8.3 and 16.1.

### Milne2008AbelianVarietiesNotes

James S. Milne, *Abelian Varieties*, course notes, version 2.00,
16 March 2008, [author's course notes](https://www.jmilne.org/math/CourseNotes/AV.pdf).
The plan's “AV” locators refer to this version and its part/section numbering.
References from these notes to inaccessible Mumford passages remain
secondhand, unchecked attributions.

### Inspected preliminary abelian-variety draft

B. Edixhoven, G. van der Geer and B. Moonen, *Abelian Varieties*, preliminary
draft chapter files on [Moonen's author page](https://www.math.ru.nl/~bmoonen/research.html#bookabvar).
The inspected Cartier/dual/Weil chapters bear the footer date
15 September 2011 and were downloaded on 29 October 2026. This identifies
the inspected draft; its bibliography entry remains incomplete
(**citation needed**). Relevant printed locators are (3.21)–(3.24),
pp. 41–43; (6.6), (6.12)–(6.18), pp. 90–96; (7.2)–(7.17), pp. 98–104;
(8.1)–(8.7), pp. 113–115; and (11.11)–(11.22), pp. 162–168.
The stronger graded-bialgebra splitting in (6.12) is not adopted. The plan
retains the necessary graded-algebra consequence and all actual theorem
suppliers as open obligations. Cited quotient/descent and Riemann–Roch inputs,
the unproved Fact (8.7), and the unposted Jacobian chapter do not acquire
proof coverage here. Mumford and Howe sources not accessed in the accepted
investigation remain unchecked; no proof attribution to them is added.
