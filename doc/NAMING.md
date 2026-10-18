# Naming and mathematical ownership

`Aglib` is the import root. Declaration namespaces belong to native mathematical objects and constructions: for example `Module`, `Algebra`, `CategoryTheory`, `TopCat.Sheaf` and `AlgebraicGeometry.Scheme`. R5Lab and Quillen identities are source provenance. Future extensions follow the ownership and dependency principles in [ARCHITECTURE.md](ARCHITECTURE.md).

## Package and repository identity

The Lake package and main Lean module are `Aglib`; the positive test module is `AglibTest`. The repository is `kangxyz/aglib`; its checkout directory is not fixed. Keep `algebraic-geometry` as the mathematical subject keyword. Original source repository names and native mathematical namespaces retain their identities.

## Use the parent context

A source path should identify the mathematical subject with enough context to distinguish it. Repeated object endings are unnecessary when the parent already fixes that object. Approved family prefixes include `Aglib.AlgebraicGeometry.Morphisms.Finite`, `.Smooth` and `.Etale`, and `Aglib.AlgebraicGeometry.Modules.Coherent`, `.QuasiCoherent`, `.LocallyFree`, `.Invertible`, `.Differentials` and `.Flat`. These are family names; use an existing leaf named in its README for an exact import.

This is a contextual rule. Preserve complete mathematical object names where they carry meaning: `StructureSheaf`, `ClosedImmersion`, `RegularLocalRing` and `RootsOfUnity` are examples. The actual type `AlgebraicGeometry.Scheme.CoherentSheaf` retains its name and its locally Noetherian guard. Shortening the source-family or helper namespace to `Modules.Coherent` does not change that type or remove the guard.

The parent must fix the same mathematical object. `Morphisms.Finite` and
`Modules.Coherent` satisfy that condition. `Modules.Perfect` does not: its objects
are complexes, so use `Modules.PerfectComplexes`. A declaration such as
`Scheme.Modules.Complex.Perfect` already has the complex context; module paths
and declaration namespaces need not be identical. In a family name, plural
`PerfectComplexes` names the collection of objects and its interfaces; use a
singular object name when naming an individual bundled type.

Names must cover every object in the family. `Spec.PolynomialLaurent` includes
polynomial and Laurent spectra and their actual relative base changes. Calling
that whole family `AffineSpace` omits its Laurent object, while `AffineScheme`
would misclassify relative products over nonaffine bases. The name does not
assert an unconstructed multiplicative-group structure.

File names should state the object, property or comparison they provide. `Products.IntegerBase` records products over the integer spectrum; `IntegralBase` would incorrectly suggest an arbitrary integral-base hypothesis. `InternalHom` denotes the constructed structure-linear internal-Hom sheaf and its actual section/restricted-morphism comparisons. The name alone supplies no closed-monoidal adjunction or derived-Hom theorem.

Use the same property spelling at comparable levels: `Morphisms.Finite` and `Modules.Coherent.Pushforward.Finite` both concern finite morphisms, whereas `QuasiCoherent.FiniteType` concerns finite-type sheaves. Preserve this mathematical distinction.

## Follow exact Mathlib spellings when present

The pinned Mathlib tree is the first source of established module spelling and object names. `Mathlib.Algebra.Homology.CochainComplexPlus` and `Mathlib.Algebra.Homology.DerivedCategory.RightDerivedFunctorPlus` are exact existing Mathlib files and remain deliberate exceptions to splitting every compound into directories. `Plus` is the actual bounded-below category in these interfaces.

`Mathlib.AlgebraicGeometry.Stalk` and `Mathlib.AlgebraicGeometry.Geometrically.Connected` follow the pinned subjects. New occupied extensions may introduce a directory beside a native file, provided their guide explains the mathematical correspondence; a subject correspondence need not reproduce Mathlib's entire layout.

Within the generic complex layer, `Aglib.Algebra.Homology.CochainComplex.KernelSequence`, `Aglib.Algebra.Homology.CochainComplex.DegreewiseSplitMono` and `Aglib.Algebra.Homology.CochainComplex.SingleShift` identify their actual owner. `Aglib.Algebra.Homology.MappingCone.Acyclicity` and `.QuasiIso` group the two actual cone results. A split morphism is degreewise unless a chain retraction is actually supplied.

## Name results and conditions precisely

Use established Mathlib abbreviations such as `NatTrans`, `QuasiIso`, `Cech` and `Plus`. Avoid opaque initials and exploratory labels when a mathematical term exists. A file containing bounded-below quasi-isomorphism propagation is `PlusQuasiIso`; `WeakMaps` obscures the property being proved. Names such as `Basic`, `Comparison`, `Unit` and `Locality` require an owning family and a guide stating the compared objects and actual conditions.

Predicate and theorem names should expose the conclusion and meaningful hypotheses. Retain bound, flatness, finite-local-freeness, flasque, cartesian-square and unit-compatibility conditions. Do not abbreviate away a condition or imply an unconditional supplier from a predicate definition. Namespace shortening never strengthens a theorem.

The selected-conflation interface uses `CategoryTheory.ExactCategory.ExactStructure` and its `ExactFunctor`. The latter is distinct from Mathlib's other bundled exact-functor notion; keep that owner and write its fully qualified name when the distinction matters.

## One interface and its bridges

Keep one implementation of each object/map. A specialization or historical adapter should delegate transparently to the canonical implementation and record the actual object/map/forward-arrow comparison where needed. Generic primitives belong below their local-property and application consumers. A source filename, provenance origin or old application name does not select the new namespace.

Keep general finite-type quasicoherent interfaces in `Scheme.Modules.QuasiCoherent`; locally Noetherian coherent and exact specializations belong in `Scheme.Modules.Coherent`. The actual guarded `Scheme.CoherentSheaf` type expresses the additional mathematical interpretation. General module helpers do not acquire a coherent owner merely because a coherent category consumes them.

Homological algebra, generic site/topological sheaves and scheme-specialized cohomology retain separate owners. Preserve the distinction between ordinary-complex categorical exactness, bounded augmentation/QI, two-bound comparison and original-unit derived calculation.

## Maintain the record

Source modules use modern `module`, precise `public import` and the project's exposed public-interface policy. Family READMEs record reusable interfaces, main mathematical results, hypotheses, explicit inputs and present consumers. Root documentation owns cross-family routes and conventions. [REFERENCES.md](REFERENCES.md) records source identity; module and namespace correspondence are maintained by their assigned map owners.

These conventions consolidate the earlier object-first/native-owner, precise-import, single-implementation and colocated-documentation decisions. Historical names remain at their original source locators. A rename needs current-source import, consumer and provenance reconciliation; earlier path/namespace checks are not evidence for the renamed surface.
