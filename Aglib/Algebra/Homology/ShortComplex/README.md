# Short exactness of diagrams


[Retract](Retract.lean), imported as `Aglib.Algebra.Homology.ShortComplex.Retract`,
gives `CategoryTheory.ShortComplex.shortExact_of_retract`. In the stated category
with zero morphisms and homology, an actual retract of a short exact short complex
is short exact. The supplied retraction is in the short-complex category, so its
maps preserve the diagram. A degreewise split morphism of cochain complexes does
not by itself supply this retraction data.

[Subcategory](Subcategory.lean), imported as `Aglib.Algebra.Homology.ShortComplex.Subcategory`,
gives `CategoryTheory.ShortComplex.shortExact_map_of_comp_iso`. For additive functors
`G : C ⥤ P.FullSubcategory` and `F : C ⥤ D` between preadditive categories, a supplied
natural isomorphism `G ⋙ P.ι ≅ F` transfers short exactness of `S.map F` to
`(S.map G).map P.ι`, retaining both maps through the full subcategory.

[MapHomology](MapHomology.lean), imported as
`Aglib.Algebra.Homology.ShortComplex.MapHomology`, gives the native
`CategoryTheory.ShortComplex.compositeHomologyDataIdentity` and
`mapHomologyIso_comp_hom`. For exact additive functors between abelian categories,
the latter identifies the actual canonical homology-comparison morphism for the
composite with the composition of the two individual comparison morphisms. The more
precise `mapHomologyIso_comp_hom_of_preservesLeftHomology` needs only preservation
of the displayed left homology under the first functor, its image under the second,
and the original complex under their composite. This pointwise statement is the
single implementation; the exact-functor theorem delegates to it. Object and
morphism universes remain independent.

The comparison proof was extracted from
`AlgebraicGeometry/Cohomology/BaseChange/CechComparison.lean`; its previous
`AlgebraicGeometry.Scheme.Cohomology` names remain compatibility delegations.
There is one implementation in this lower family. The field Cech comparison and
the generic scalar-extension homology comparison use this same implementation.

These results are below finite-free tensor retractions and scalar/sheaf exactness
arguments. They do not assert that an arbitrary additive functor preserves
homology or that tensor product commutes with arbitrary cohomology.

[Adjunction](Adjunction.lean) gives `Adjunction.homologyUnit` and
`Adjunction.homologyComparison` for an additive adjunction whose right adjoint
preserves homology. The latter is the mate of the actual adjunction unit on
homology. Its unit equation and coefficient naturality retain the original
maps. Preservation of the displayed homologies by the left adjoint identifies
it with the inverse native comparison. Scalar extension specializes this
single generic implementation in
[ChangeOfRings/Homology](../../Category/ModuleCat/ChangeOfRings/Homology.lean).

[MapHomology/Components](MapHomology/Components.lean) proves compatibility of
the native comparison with the actual homology-to-opcycles morphism and the
original projection to opcycles. These equations underlie the natural
zero-degree cochain homology embedding. They use exact additive functors and
retain the native structure maps.

[Finrank](Finrank.lean) proves dimension identities for the original
homology of a short complex over a field. With only finite middle term,
homology dimension plus the two differential-image dimensions equals
middle dimension. A finite third term gives the equivalent identity
`dim H + dim X₃ = dim opcycles + dim cokernel(g)`, retaining the original
categorical opcycles and cokernel. These identities apply directly to
residue-field complexes; no homology/base-change isomorphism is assumed.

[Semicontinuity](Semicontinuity.lean) applies the dimension identity to the
original scalar-extended short complex. Its homology dimension is upper
semicontinuous when the middle term is finite and the third term is finitely
presented and flat. The first term need not be finite, and the base ring need
not be Noetherian. The proof identifies the native opcycles and cokernel
with their actual scalar extensions and uses local constancy of the third
term's fibre rank.

[AlgebraTests](AlgebraTests.lean) proves universal module-tensor exactness
from exactness after every commutative algebra extension in the base-ring
universe. The original coefficient complex tensored with a module is a
retract of its tensor product with the trivial square-zero algebra. The
native coefficient maps and their split retraction preserve the original
differentials; no flatness assumption or alternative tensor functor is used.

[Regular](Regular.lean) proves pointwise preservation of the original left
and right homology data for a regular outgoing differential under an
additive cokernel-preserving functor. For an additive adjunction with
homology-preserving right adjoint, its original homology mate is then
invertible. A projective final object and projective original outgoing
cokernel supply this condition; the first two objects need not be
projective.

The [base-change criteria](BaseChange/README.md) specialize these results
to the unchanged extension/restriction mate, including the local
residue-surjectivity/free-cokernel equivalence and arbitrary-base-change
consequence. [Adjunction/Exactness](Adjunction/README.md) owns the lower
actual cycle sequence and the naturality argument detecting its exactness.

The extraction leaf compiled through the shared guarded wrapper with
`build Aglib.Algebra.Homology.ShortComplex.MapHomology`, receipt
`.lake/verification/cohomology/1792072930712221000-60669` (including the pointwise
left-homology generalization). The affected field Cech
consumer compiled with `build Aglib.AlgebraicGeometry.Cohomology.BaseChange.CechComparison`,
receipt `.lake/verification/cohomology/1792072566845036000-37322`, after replacing its
proof with delegation. No aggregate library compilation was run.

[ModuleQuasiIso](ModuleQuasiIso.lean) proves
`ShortComplex.quasiIso_of_liftCycles_of_reflectBoundaries` for modules over an
arbitrary ring, with independent ring and carrier universes. Lifting every
cycle and reflecting boundaries proves that the actual map is a
quasi-isomorphism, using native kernel/range-quotient homology data. The
one-element Koszul tensor augmentation consumes this selected generic proof
from the user-supplied Motivic source.

The same component owner also proves
`homologyπ_mapHomologyIso_hom`, `map_homologyπ_mapHomologyIso_inv`
and `mapCyclesIso_inv_iCycles`. The actual homology projection from cycles
and cycle inclusion commute with the original comparisons in both
directions. These equations use the same exact additive functors and
independent category universes; scalar-coinduction Ext normalization and
higher-image open restriction consume them. The source passed
`1792144127942933000-87382` and its production-only public consumer passed
`1792144212660631000-88415`, including all three reassociated equations
and only the standard axioms.
