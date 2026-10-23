# Marked DVRs in actual filtered colimits

Let F be a small filtered diagram in `CommRingCat.{u}`, indexed by a
category whose object and morphism types lie in the same universe, and
let c be its
actual colimit cocone, and let p be a natural number. Assume every F(i)
is a DVR and its natural p is irreducible. Suppose the actual point
g:c.pt→K to a field has the property that every composite g∘cᵢ has kernel
maximalIdeal(F(i)). The point g need not be surjective.

The candidate proves that c.pt is a domain and a DVR, its original
natural p is irreducible, and ker(g)=maximalIdeal(c.pt). Neither flatness
nor injectivity of the transition maps is an assumption. The carrier,
cocone, and point are unchanged.

The forgetful functor from commutative rings preserves filtered
colimits. Native `Concrete.isColimit_exists_rep` therefore represents
every element by an actual stage element. The native filtered equality
criterion makes an equation between two such elements true at a later
stage. Applied to p*x=0, it proves p regular in the colimit, hence all
its powers nonzero. The stage DVR factorizations map to
x=u*p^n for every nonzero x in the colimit. Multiplication of these
factorizations proves that the colimit is a domain.

The unit-or-one-minus-unit property maps from each stage, proving the
colimit local. The stage kernel equations identify ker(g) with (p) by
mapping an actual divisibility witness. They also identify ker(g) with
the actual maximal ideal of the colimit: a representative of a nonunit
is a nonunit at its stage, hence has zero residue, while a unit cannot
map to zero in K. Thus the maximal ideal is (p). Its nonzero generator
is irreducible, and the mapped unit-power factorizations give the native
DVR structure through
`IsDiscreteValuationRing.ofHasUnitMulPowIrreducibleFactorization`.

The current consumer is the limit stage of the actual `SuccStruct`
diagram in `Over (CommRingCat.of K)`. The required colimit field point is
the object map in this over-category, and its cocone equations give the
displayed compatibility. This lemma proves the DVR/kernel predicate
along the construction; it does not assume closure of that predicate
under colimits or final surjectivity.

Source basis: Aglib HEAD `8b93cc5940dc93f39a2eaf05e6985af28250a578`,
Lean 4.34.1, and Mathlib `d13f23b723b8a846827a245b89c10fc7d3f11612`.
Its suppliers are the original categorical filtered-colimit APIs and
the native DVR factorization criterion; the actual assembly is new
proof work.
