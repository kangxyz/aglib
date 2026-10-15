# Overall design principles

The library is organized by mathematical objects, hypotheses and reusable constructions. These principles govern future extensions as well as the current extraction. [NAMING.md](NAMING.md) gives concrete naming conventions and approved examples; local family guides give the actual interfaces and results.

## Mathematical ownership

Choose an owner from the complete statement and its current consumer. Rings, ideals, modules, categories, complexes, topological sheaves and schemes have their own mathematical subjects. Origin in a curve, K-theory or perfect-complex file records provenance and does not make a general lemma part of that application layer.

Use the pinned Mathlib object and interface when available. Extend its native mathematical owner, or introduce a focused subject next to it when the admitted objects require that extension. `Aglib` identifies imports; the declaration namespace identifies the object. This distinction permits a module to extend a native namespace without duplicating its object or inheriting the source package's identity.

The reference crosswalk is concrete: commutative algebra extends Mathlib RingTheory; generic complexes and D+ extend Algebra/Homology and CategoryTheory; site/topological sheaves precede scheme modules; scheme properties and morphisms use AlgebraicGeometry. Stacks separates Chapters 10, 12–13, 17–18, 20–21, 26, 28–30, 33 and 35 along those subjects. Hartshorne's Schemes and Cohomology and EGA I's scheme-language orientation guide reading routes. [REFERENCES.md](REFERENCES.md) records the inspected primary records and exact pinned paths. These references organize subjects without attributing an uninspected theorem or requiring identical book/software layouts.

## Dependency direction

Keep a directed acyclic graph of precise imports. Object constructions and general algebra/categorical primitives precede local properties; those precede functorial, exact and cohomological consequences; specialized applications consume the general theory. The mathematical role determines the lowest useful owner.

If a lower object needs a generic map currently hidden in a higher source, split that map into its own lower owner and retain its original premises. Do not import an application aggregate to recover one general helper. Keep generic resolution, Ext, cone, truncation and total-complex results outside scheme specialization; keep generic sites/topological sheaves below structural-field cohomology.

The implemented graph decides precise dependencies. A reading order or book chapter order is not a substitute for inspecting the actual imports and object types.

## Canonical implementations and comparisons

There is one canonical implementation of each mathematical object or map. Specializations and compatibility bridges delegate to it, rather than constructing a second copy with a similar name. Comparisons should identify the actual object, coefficient action and forward map needed by the consumer.

The generic site tensor feeds scheme module tensors and invertible wrappers. Generic symmetry remains below finite-locally-free exactness, projection formula and Picard laws. Canonical finite-type pushforward lives below guarded coherent specializations. Identity/composition, affine scalar, restriction, section and unit equations expose these constructions for reuse.

An isomorphism of some replacement object does not identify the original map. Cohomology comparisons must preserve the actual `Sheaf.H`, structural scalars and canonical pullback/tensor map. Derived computations retain the installed unit and its equation. A one-sided contraction is not a two-sided equivalence.

## Interfaces and hypotheses

Prefer one reusable class or explicit data interface for a mathematical property. Finite locally free objects use the canonical local-basis class; bridges preserve the same cover and basis witness. Keep universe and size bounds, quantifiers, canonical maps and exact hypotheses visible.

Finite type, finite presentation, local freeness and coherence are distinct properties. General quasicoherent finite-type categories and finite-presentation transport work below the locally Noetherian coherent interpretation. `Scheme.CoherentSheaf` retains an explicit locally Noetherian guard. Exact coherent functors keep the guards needed for their abelian/exact structures; an unused section variable must not become an accidental theorem premise.

The selected exact-category functor preserves chosen conflations in `CategoryTheory.ExactCategory`. It remains distinct from other native exact-functor notions. A supplied injective resolution or essentially small model is different from a theorem of existence for arbitrary categories.

Ordinary Godement totalization is categorically exact on complex objects. Augmentation/QI and D+ calculation retain bounded-below or explicit lower-bound premises; term comparison retains both term bounds. Flat cartesian comparison, flasque/local-QI computation and original-unit equations retain their own hypotheses. New canonical constructions do not discharge older explicit rank, proper-finiteness or relative-base-change input families.

## The smallest useful maintained family

Create occupied structure for an admitted object/result and a current consumer. A family may own its basic object, local properties and comparisons without acquiring empty future layers. Split a mixed file when its subjects, conditions or dependency directions differ; do not relocate it wholesale under whichever application used it first.

Each family README is the authority for objects, focused imports, canonical interfaces, principal mathematical results, exact conditions and remaining explicit inputs. It names lower prerequisites and present consumers. Root `doc/` coordinates the overview, reading routes, design/naming, development and source provenance instead of duplicating every local API.

Keep maintained text and identifiers in English, preserve exact source locators and contributor/license headers, and avoid unrelated cleanup. Earlier source names remain provenance; adapters for original application packages belong to those packages.

## Extension admission and current acceptance

For a new extension, identify the source revision/range and the intended mathematical contribution first. Check the actual statement, object, hypotheses and dependencies; record a generic lift and its original specialization explicitly. Generality alone does not authorize importing an unrelated application surface.

Select the native owner and precise lower dependencies, reconcile canonical implementations, and register every admitted leaf in the module surface and provenance under the assigned owners. Use modern `module` headers, precise `public import` and exposed public interfaces where the project reduction/visibility contract requires them. Production depends on Mathlib and lower `Aglib` leaves; tests and downstream packages are consumers.

Validate the changed surface and affected consumers against the current module identities, namespaces and source snapshot. Reconcile enrollment, import direction, public visibility, source correspondence and foundation coverage. A changed source/condition or map needs the affected mathematical phase; a writing or naming change must not silently resolve a proof obligation.

Builds, lints, finite checks, source hashes and kernel replay report their actual coverage. They do not supply a retained theorem-family parameter, establish an unbounded assertion from finite evidence or replace independent mathematical/writing acceptance. [WORK_PLAN.md](WORK_PLAN.md) records current integration coverage, while [INTERFACES.md](INTERFACES.md) records the explicit mathematical boundary.
