# Actual group kernels, deck translations and coefficient transport

[Basic](Basic.lean) owns `Scheme.Group.Kernel.group`, the literal group-object
pullback of a morphism along the actual unit, and its actual `inclusion`.
Its `marking` is universal on every over-category test scheme. Forgetting the
group law gives the stated scheme pullback. These constructions work over any
scheme; the finite and etale instances require the corresponding condition on
the original morphism.

[PrimeDegree](PrimeDegree.lean) proves geometric cyclicity of that actual
kernel for a finite-etale group morphism of prime geometric degree. Degree
means the cardinality of every actual algebraically closed geometric fibre in
the displayed universe. Neither a cyclic kernel nor a chosen marking is an
input. The cyclic coefficient may retain nontrivial Galois descent action.

[DeckTranslation](DeckTranslation.lean) proves that a deck morphism of the
displayed finite-etale group map is translation by its value at the unit when
the source is geometrically connected. Its actual kernel point has the exact
order of the deck automorphism. An actual deck generator of positive order
equal to the geometric degree yields cyclicity on every algebraically closed
field-valued fibre, including composite orders. The translation and its
injective monoid representation are the separate field-independent suppliers
in [Translation](../Translation.lean).

[Remarking](Remarking.lean) keeps the source, target and group arrow fixed
while transporting the coefficient along a specified actual group
isomorphism. The lower `CategoryTheory.KernelMarking.transportCoefficient`
retains the universal property on every test object; the new inclusion is the
inverse coefficient map followed by the original inclusion. Mathlib's
`yonedaGrp` evaluated at the actual test object gives the point-group comparison.
Its forward map is literal postcomposition with the specified group morphism.
Kernel-fibre and marked
monodromy equations retain the original finite-etale hypotheses.

The companion base-change leaves reuse the single canonical implementation
`Scheme.Group.BaseChange.groupSchemeBaseChange`. `BaseChange.CyclicKernel`
transports actual cyclic coefficients and actual geometric fibre degrees;
the universal marking already belongs to `BaseChange.MarkedKernel`.
`BaseChange.FullFaithful` lifts actual finite-etale group maps and isomorphisms
under supplied fullness and faithfulness of finite-etale pullback, with exact
pullback equations. `BaseChange.UnitRange` and `Limits.OverRange` retain the
actual unit and projection ranges. `BaseChange.Composition` identifies the
two existing composition isomorphisms by equality of their actual maps.

The compatible-closure-embedding conjugacy equation belongs to
`FundamentalGroup.Field.EmbeddingConjugacy`, using the original field algebra
and the same two displayed embeddings. It has no characteristic-zero premise.
`Cohomology.EtaleH1.GroupBaseChange` gives the represented group and H1 squares
from the actual group-isomorphism equation, retaining geometric point,
Galois-category/fibre-functor and Ext-universe inputs. `RepresentedKernel`
constructs the represented categorical kernel from an actual monomorphism and
section lifts on all over-category tests; it supplies no quotient epimorphy.

Fibre reconstruction reuses `Scheme.EtaleH1.MarkedCoefficients` and
`SchemeTorsorClassification`. The client `AglibTest.GroupBaseChange` compares
the packet's original action-classification construction with that native
group isomorphism by equality of the original forward map. Arithmetic cyclic
characters, incoming marked carriers and Tate comparison endpoints remain
downstream; none is a premise or conclusion of these general suppliers.
