# Sheaf cohomology on sites

This family develops original `Sheaf.H`, represented-object Ext, Čech
complexes and their canonical maps on actual sites. Generic statements retain
their topology, sheafification, coefficient, Ext and injective hypotheses.
Scheme geometry belongs to the corresponding scheme family.

| Family | Reusable interface and current consumer |
| --- | --- |
| [Cech](Cech/README.md) | Native `CategoryTheory.Cech` complexes, split-cover exactness under the terminal-section and product hypotheses, coefficient and intersection comparisons, and short exact sequences from supplied sectionwise exactness. [Topological comparisons and cocycles](../../../Topology/Sheaves/Cech/README.md) have their own owner. |
| [Large](Large/README.md) | Large-valued represented-object cohomology and injective suppliers; consumed by the actual small-etale slice entry. [Finite coproducts](Large/FiniteCoproduct.lean) give all-degree represented-cohomology decomposition from bijectivity of the actual section restriction map for every coefficient sheaf. |
| [Slice](Slice/README.md) | Exact slice adjunction, free-representable Ext comparison, original maps and `H'`; the concrete small-etale consumer is [Cohomology/SliceComparison](../../../AlgebraicGeometry/EtaleCohomology/Cohomology/SliceComparison.lean). |
| [ModuleCoefficients](ModuleCoefficients/README.md) | Original module/abelian comparisons, actual injective acyclicity, evaluation and slice maps; concrete small-etale consumers belong to [EtaleCohomology/Coefficients](../../../AlgebraicGeometry/EtaleCohomology/Coefficients/Cohomology.lean). |
| [Hypercohomology](../Hypercohomology/README.md) | Free-representable sources and degree-zero ordinary-cohomology comparisons. |
| [Coefficient continuity](Continuity/FiniteCoefficientContinuity.lean) | Canonical filtered-colimit comparison in original `Sheaf.H`; finite generating hypercovers supply invertibility in all degrees. The scheme consumer is [fixed qcqs continuity](../../../AlgebraicGeometry/EtaleCohomology/Continuity/README.md). |
| [Basis acyclicity](BasisAcyclicity/Basic.lean) | Čech acyclicity on a cofinal cover basis gives positive represented-object Ext vanishing on basis objects, and original `Sheaf.H` vanishing when a terminal object lies in the basis. The quasicoherent étale family uses these generic suppliers. |
| [Exact-sequence vanishing](Vanishing/ExactSequence.lean) | Original connecting homomorphisms transport supplied vanishing and surjectivity through actual short exact coefficient sequences. |
| [Split complexes](Splitting.lean) | On any site, a split short complex `0 → A → B → C → 0` of abelian sheaves gives `Sheaf.H.splittingAddEquiv : H^n(B) ≃+ H^n(A) × H^n(C)` and `Sheaf.H.kerAddEquivOfSplitting : ker H^n(g) ≃+ H^n(A)`, with injective first map; sheafification and the Ext universe remain explicit. The consumer is the split square-zero unit sequence [Ring/Sheaf/SquareZeroSplitting](../../../Algebra/Category/Ring/Sheaf/SquareZeroSplitting.lean). |

[Global/Comparison](Global/Comparison.lean) defines intrinsic additive global
sections represented by the original constant-integer sheaf and compares their
native right derivatives with original Ext. It selects no terminal object.
[Terminal/Comparison](Terminal/Comparison.lean) is the optional comparison with
actual evaluation at a supplied terminal object, retaining the native size lift
and original section maps.

## Filtered coefficients and compatible systems

[CoefficientComparison](Continuity/CoefficientComparison.lean) defines
`Sheaf.H.coefficientColimitComparison` as the original
`colimit.post G (Sheaf.functorH J n)`. Its normalization at every coefficient
cocone injection and its square with the original connecting homomorphism
are retained. [Dimension shifting](Continuity/CoefficientContinuity.lean)
deduces invertibility from exact colimits, degree-zero preservation and
acyclicity of colimits of injectives.

[FiniteCoefficientContinuity](Continuity/FiniteCoefficientContinuity.lean)
supplies these cohomological inputs for a generating one-hypercover family
whose degree-zero index and every pairwise degree-one index are finite. Its coefficient category is
`Sheaf J AddCommGrpCat.{max u v}`. It retains a terminal object, finite
products in each over-category, sheafification, local-bijectivity and
sheaf-composition with the forgetful functor, enough injectives, and
`HasExt.{e}`. The filtered index has type `Type (max u v)`; colimits of that
shape in `AddCommGrpCat.{e}` remain explicit, so the Ext universe need not be
identified with the coefficient universe.

[Injective systems](Continuity/InjectiveSystem.lean) use actual adjunctions
between varying categories, with left adjoints preserving monomorphisms,
enough injectives and the required products. The product envelopes and
embeddings retain the original right-adjoint identity and composition
comparisons; [system coherence](Continuity/InjectiveDiagram/SystemCoherence.lean)
uses their coherence laws.
[RepresentedDiagram](Continuity/RepresentedDiagram.lean) constructs actual
represented Ext diagrams from these coherent adjunction systems, a cartesian
source system and an arbitrary coefficient system. Transitions use the native
Ext transfer and the original source and coefficient arrows; identity,
composition and coefficient naturality are proved from the system data.
The additive, exactness, source-cartesianness and independent Ext-universe
hypotheses remain explicit. The actual small-etale cohomology diagram
specializes this constructor.
[RepresentedDiagram/ExactSequences](Continuity/RepresentedDiagram/ExactSequences.lean)
constructs `Functor.extPrecompMapConnectingComplexHom`, the morphism of native
represented Ext connecting fragments induced by the given exact functor, source
map and short-complex morphism.
[SchemeSystemColimits](Continuity/SchemeSystemColimits.lean) proves the
identity-arrow diagonal final. For a filtered index, supplied tail colimits
and an outer colimit compute the actual arrow and diagonal colimits, retaining
the original comparison legs. This categorical result leaves the geometric
tail-colimit premise to its scheme consumer.

[SectionArrows](Continuity/InjectiveDiagram/SectionArrows.lean) derives the
whole square, system-square, Arrow-functor and cone naturality laws from the
given section functors and their original pullback identity and composition
laws. [Cone](Continuity/InjectiveDiagram/Cone.lean) also constructs the actual
coefficient natural transformation, colimit map and injection equations.
The small-etale consumers supply their original adjunction and section maps.

[CohomologyCocone](Continuity/InjectiveDiagram/CohomologyCocone.lean) constructs
the actual represented-Ext cocone and its colimit-desc comparison from the
single cartesian source system, coefficient functor and original transfer
triangles. Its local endpoint and stage/apex Ext hypotheses retain their stated
universes. The raw exact-functor argument is shared through
[Ext/SourceTransfer](../../Abelian/Ext/SourceTransfer.lean).

## Coverwise acyclicity

The basis criterion assumes Čech exactness of the coefficient on the selected
covers. Under its displayed sheafification, local-bijectivity, Ext and
enough-injectives hypotheses, it concludes positive Ext vanishing from the
actual free-representable source on each basis object. For a terminal basis
object it concludes positive original `Sheaf.H` vanishing, with independent
Ext size. Geometric producers of the Čech hypothesis remain separate inputs.

[SplitTerminal](SplitTerminal.lean) constructs the local-image subgroup
subsheaf and supplies section surjectivity when terminal covers split. Its
small-etale consumer is
[EtaleCohomology/StrictlyLocal](../../../AlgebraicGeometry/EtaleCohomology/StrictlyLocal/README.md).
