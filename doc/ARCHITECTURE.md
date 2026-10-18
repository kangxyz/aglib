# Overall design principles

The library is organized by mathematical objects, hypotheses and reusable constructions. These principles govern future extensions as well as the current extraction. [NAMING.md](NAMING.md) gives concrete naming conventions and approved examples; local family guides give the actual interfaces and results.

## Mathematical ownership

The library's remit is general algebraic geometry and related mathematics. A migration batch admits general definitions and theorems with their necessary lower foundations. Existing downstream demand helps identify interfaces; it does not limit the library's mathematical scope. Specialized application objects and their comparison data retain downstream owners.

Choose an owner from the complete statement, the constructed objects and the dependency direction. A current consumer records usage; it does not determine admission or placement. Rings, ideals, modules, categories, complexes, topological sheaves and schemes have their own mathematical subjects. Origin in a curve or K-theory file records provenance and does not make a general lemma part of that application layer.

Use the pinned Mathlib object and interface when available. Extend its native mathematical owner, or introduce a focused subject next to it when the admitted objects require that extension. `Aglib` identifies imports; the declaration namespace identifies the object. This distinction permits a module to extend a native namespace without duplicating its object or inheriting the source package's identity.

The reference crosswalk is concrete: commutative algebra extends Mathlib RingTheory; generic complexes and D+ extend Algebra/Homology and CategoryTheory; site/topological sheaves precede scheme modules; scheme properties and morphisms use AlgebraicGeometry. Stacks separates Chapters 10, 12–13, 17–18, 20–21, 26, 28–30, 33 and 35 along those subjects. Hartshorne's Schemes and Cohomology and EGA I's scheme-language orientation guide reading routes. [REFERENCES.md](REFERENCES.md) records the inspected primary records and exact pinned paths. These references organize subjects without attributing an uninspected theorem or requiring identical book/software layouts.

## Dependency direction

Keep a directed acyclic graph of precise imports. Object constructions and general algebra/categorical primitives precede local properties; those precede functorial, exact and cohomological consequences; specialized applications consume the general theory. The mathematical role determines the lowest useful owner.

If a lower object needs a generic map currently hidden in a higher source, split that map into its own lower owner and retain its original premises. Do not import an application aggregate to recover one general helper. Keep generic resolution, Ext, cone, truncation and total-complex results outside scheme specialization; keep generic sites/topological sheaves below structural-field cohomology.

The implemented graph decides precise dependencies. A reading order or book chapter order is not a substitute for inspecting the actual imports and object types.

## Selecting a source family

Use the actual pinned Mathlib subject as the first reference, inspecting its
contents rather than matching a namespace or directory name mechanically.
Otherwise select the mathematical object, property or construction described by
the complete interface. The following decisions apply to extensions:

| Interface | Source owner | Reason |
| --- | --- | --- |
| A scheme property | `AlgebraicGeometry.Properties` or its established Mathlib subject | A property of the scheme itself is distinct from a property of a structural morphism. |
| A morphism property and its selected objects over a base | `AlgebraicGeometry.Morphisms` | Finite-etale objects of `Over X` are selected by their structural morphisms; their category, fibres and base change belong in `Morphisms.FiniteEtale`. |
| Polynomial/Laurent spectra and their relative products | `AlgebraicGeometry.Spec.PolynomialLaurent` | The family includes both spectra and base changes over possibly nonaffine schemes. Its objects are not all affine spaces or globally affine schemes. |
| Scheme-valued base-change diagrams | `AlgebraicGeometry.BaseChange` | A construction with codomain `Scheme` belongs below the module-sheaf operations that consume it. |
| Scheme module sheaves and their ordinary complexes | `AlgebraicGeometry.Modules`, including `Modules.Complex` | Ordinary restriction, quasi-isomorphism and contraction infrastructure is distinct from a cohomology computation. |
| Derived categories of scheme module sheaves | `AlgebraicGeometry.Modules.DerivedCategory` | General derived restriction and Hom transport precede their perfect-complex consequences; interfaces distinguish actual complexes from localized objects. |
| Perfect complexes and local models | `AlgebraicGeometry.Modules.PerfectComplexes` | The complete object name is needed: a module is not a complex. Chain categories and derived objects must be distinguished in the interface. |
| Arbitrary-site module sheaf/presheaf interfaces | `Algebra.Category.ModuleCat.Sheaf` / `Presheaf` | A scheme specialization must not own a statement quantified over arbitrary sites. |
| Finitely generated module categories | `Algebra.Category.FGModuleCat` | These interfaces use the actual native `FGModuleCat`, rather than the category of all modules. |
| Generic and topological Cech constructions | `CategoryTheory.Sites.SheafCohomology.Cech` / `Topology.Sheaves.Cech` | An arbitrary category and the opens of a topological space have different object-level dependencies. |

A whole family must fit its owner, including relative constructions and its
weakest general statements. Split a mixed file when the lower declarations need
neither the stronger hypothesis nor the specialized objects of its parent.
For example, arbitrary-scheme stalk dimension belongs below smooth dimension;
flat stalk base change belongs below its etale use. A ring-only lemma does not
acquire scheme hypotheses from a geometric consumer.

Check every declaration in a proposed new leaf, including its helper
definitions. A `CommRingCat` localization map belongs to ring/localization
theory, even when its first use is a smooth Cartier argument; it does not belong
to `Scheme.Hom`. A regularity lemma without a flatness premise does not belong
to a flatness-only family. Group natural-isomorphism and adjunction facts by
their respective interfaces rather than collecting unrelated operations in a
generic transport file. Trivial wrapper maps can be replaced by the canonical
native expressions, retaining any equations actually used by consumers.

An established native subject can justify a deliberate spelling or location.
For example, Mathlib's `Geometrically` and `Group` subjects remain valid owners,
and its finite-type ring theory contains monoid-algebra property results. A
namespace alone is not a rule for moving these results across source roots.
Explain a non-obvious extension in the family guide; avoid cosmetic uniformity.

Cohomology legitimately contains derived direct images, resolutions and their
comparison/computation methods, not only declarations mentioning `Sheaf.H`.
Godement remains such a method family. Move an independent ordinary-complex
primitive to its lower owner without relocating the entire derived-cohomology
surface merely because its objects are complexes.

## Canonical implementations and comparisons

There is one canonical implementation of each mathematical object or map. Specializations and compatibility bridges delegate to it, rather than constructing a second copy with a similar name. Comparisons should identify the actual object, coefficient action and forward map needed by the consumer.

The generic site tensor feeds scheme module tensors and invertible wrappers. Generic symmetry remains below finite-locally-free exactness, projection formula and Picard laws. Canonical finite-type pushforward lives below guarded coherent specializations. Identity/composition, affine scalar, restriction, section and unit equations expose these constructions for reuse.

An isomorphism of some replacement object does not identify the original map. Cohomology comparisons must preserve the actual `Sheaf.H`, structural scalars and canonical pullback/tensor map. Derived computations retain the installed unit and its equation. A one-sided contraction is not a two-sided equivalence.

When changing an owner or namespace, check name resolution at every moved use.
For example, module-sheaf restriction and cochain-complex restriction are
different functors; use `Complex.restrict` explicitly where a surrounding
module-sheaf namespace would select the other operation. Preserved source
tokens alone do not establish preserved elaborated objects.

When a bundled type moves upstream, its extensions can use the type's native
namespace while their files remain downstream. Dot notation searches that
namespace: keeping a K-theory extension under the former application-owned
type name can break a call such as `C.K`. General bundling constructors belong
with the upstream object; K-theory extensions still belong in the K-theory
package. This preserves one type and a usable interface without an upstream
dependency on the application.

## Interfaces and hypotheses

Prefer one reusable class or explicit data interface for a mathematical property. Finite locally free objects use the canonical local-basis class; bridges preserve the same cover and basis witness. Keep universe and size bounds, quantifiers, canonical maps and exact hypotheses visible.

Expose proved general facts as ordinary theorems or justified instances. A
global proposition packaging a missing theorem over all schemes is an input
obligation, not a replacement for that theorem. When its existing proof is
admitted, provide the pointwise native interface and remove unnecessary input
parameters from its corollaries and consumers. Retain conditional inputs only
for genuinely unsupplied results or deliberately abstract mathematics; record
that distinction in the family guide. Do not add a definitions-only layer merely
to preserve a retired input wrapper.

Finite type, finite presentation, local freeness and coherence are distinct properties. General quasicoherent finite-type categories and finite-presentation transport work below the locally Noetherian coherent interpretation. `Scheme.CoherentSheaf` retains an explicit locally Noetherian guard. Exact coherent functors keep the guards needed for their abelian/exact structures; an unused section variable must not become an accidental theorem premise.

The selected exact-category functor preserves chosen conflations in `CategoryTheory.ExactCategory`. It remains distinct from other native exact-functor notions. A supplied injective resolution or essentially small model is different from a theorem of existence for arbitrary categories.

Ordinary Godement totalization is categorically exact on complex objects. Augmentation/QI and D+ calculation retain bounded-below or explicit lower-bound premises; the termwise comparison retains both term bounds. Flat cartesian comparison, flasque/local-QI computation and original-unit equations retain their own hypotheses. These generic constructions alone do not prove geometric rank, proper finiteness or relative base change. [INTERFACES.md](INTERFACES.md) distinguishes the proved geometric suppliers from the remaining explicit inputs.

## The smallest useful maintained family

Create occupied structure for an admitted object/result and a current consumer. A family may own its basic object, local properties and comparisons without acquiring empty future layers. Split a mixed file when its subjects, conditions or dependency directions differ; do not relocate it wholesale under whichever application used it first.

Each family README is the authority for objects, focused imports, canonical interfaces, principal mathematical results, exact conditions and remaining explicit inputs. It names lower prerequisites and present consumers. Root `doc/` coordinates the overview, reading routes, design/naming, development and source provenance instead of duplicating every local API.

Keep maintained text and identifiers in English, preserve exact source locators and copyright/license notices, and avoid unrelated cleanup. Credit actual contributors under the [contribution conventions](DEVELOPMENT.md#contribution-conventions). Earlier source names remain provenance; adapters for original application packages belong to those packages.

## Extension admission and current acceptance

For a new extension, identify the source revision/range and the intended mathematical contribution first. Check the actual statement, object, hypotheses and dependencies; record a generic lift and its original specialization explicitly. Generality alone does not authorize importing an unrelated application surface.

Select the native owner and precise lower dependencies, reconcile canonical implementations, and register every admitted leaf in the module surface and provenance under the assigned owners. Use modern `module` headers, precise `public import` and exposed public interfaces where the project reduction/visibility contract requires them. Production depends on Mathlib and lower `Aglib` leaves; tests and downstream packages are consumers.

Validate the changed surface and affected consumers against the current module identities, namespaces and source snapshot. Reconcile enrollment, import direction, public visibility, source correspondence and foundation coverage. A changed source/condition or map needs the affected mathematical phase; a writing or naming change must not silently resolve a proof obligation.

Builds, lints, finite checks, source hashes and kernel replay report their actual coverage. They do not supply a retained theorem-family parameter, establish an unbounded assertion from finite evidence or replace independent mathematical/writing acceptance. [WORK_PLAN.md](WORK_PLAN.md) records current integration coverage, while [INTERFACES.md](INTERFACES.md) records the explicit mathematical boundary.
