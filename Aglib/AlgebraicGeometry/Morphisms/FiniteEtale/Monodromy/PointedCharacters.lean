/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Aglib.AlgebraicGeometry.Morphisms.FiniteEtale.Monodromy.Coefficients
public import Aglib.AlgebraicGeometry.Morphisms.FiniteEtale.PointedCover
public import Aglib.AlgebraicGeometry.SchemeOverField

/-!
This module retains the assigned pointed-character and geometric-comparison declarations.
The original source context below describes the full pre-split family;
its stated hypotheses and uninstantiated comparison boundaries remain in force.
-/

@[expose] public section

open _root_.AlgebraicGeometry.Scheme.OverField (Base FScheme)

/-!
# Primitive pointed characters and marked incoming isogenies

Source: `K2-018#eq:k2018-pointed-character` and
`K2-018#prop:k2018-arithmetic-characters`, lines 341–445 of
`research/exposes/K2/018/expose.tex` at
`e73d98b1b5c1e5abcdebf7d058e436d792b87982`.

The direct continuous cocycle model `PointedH1` is used explicitly. Primitive
classes are first identified with surjective continuous equivariant characters,
using proved order preservation and finite cyclic algebra. General finite-etale
monodromy inputs then classify pointed geometrically connected coefficient
covers. The separately proved geometry comparison gives marked incoming cyclic
isogenies of actual group schemes over F, up to marked F-isomorphism.

The monodromy background quantifies over general finite etale coefficient
schemes and finite discrete modules; none of its fields mentions H¹, primitive
order, or isogenies. The geometric coefficient marking uses actual points over
an algebraically closed field and an explicit descent action. In particular,
cyclicity alone never identifies a coefficient scheme with the chi-square twist.
G and N are supplied continuous fundamental-group model data. Their actual
fundamental-group realization and the etale/cochain comparison are named
background boundaries, rather than an implicit replacement by discrete cohomology.
Each declaration's source pointer uses the module source basis above.
-/

noncomputable section

open CategoryTheory MonoidalCategory CartesianMonoidalCategory MonObj
open scoped CategoryTheory.MonObj
open AlgebraicGeometry
open AlgebraicGeometry.Scheme.FiniteEtale.PointedCovers
open GroupCohomology.PointedCohomology GroupCohomology.PrimitiveCharacters

namespace GroupCohomology.PrimitiveCharacters.Translation

universe u v
attribute [local instance] Over.cartesianMonoidalCategory

variable {G N : Type*} [Group G] [Group N] [MulDistribMulAction G N]
  [TopologicalSpace G] [TopologicalSpace N]

variable {F K : Type u} [Field F] [Field K]
variable (s : Spec (CommRingCat.of K) ⟶ Base F)
variable (sigma : G →* Aut (Over.mk s))

/-- Pointed connected coefficient-cover classes for
`K2-018#prop:k2018-arithmetic-characters`, on the module source basis. -/
abbrev CoverClasses (A H : Grp (FScheme F)) := Quotient (coverSetoid A H)

/-- General finite-cover monodromy data, used in
`K2-018#prop:k2018-arithmetic-characters`, on the module source basis.
Its fields are faithfulness, connectedness/transitivity, and realization of
transitive finite actions. No primitive or isogeny theorem is supplied. -/
structure CoverMonodromyData (A H : Grp (FScheme F)) (R : Type v)
    [AddCommGroup R] [DistribMulAction G R] [TopologicalSpace R]
    [IsTopologicalAddGroup R]
    (realization : CoefficientRealization s sigma A R) where
  /-- General monodromy extraction used in
  `K2-018#prop:k2018-arithmetic-characters`, on the module source basis. -/
  monodromy : CoverClasses A H → EquivariantCharacter G N R
  /-- General finite-cover faithfulness used in
  `K2-018#prop:k2018-arithmetic-characters`, on the module source basis. -/
  faithful : Function.Injective monodromy
  /-- General connectedness/transitivity comparison used in
  `K2-018#prop:k2018-arithmetic-characters`, on the module source basis. -/
  connected_transitive : ∀ c, letI := translationAction (forgetCharacter (monodromy c))
    MulAction.IsPretransitive N R
  /-- General transitive-action realization used in
  `K2-018#prop:k2018-arithmetic-characters`, on the module source basis. -/
  realizes : ∀ f : EquivariantCharacter G N R,
    (letI := translationAction (forgetCharacter f); MulAction.IsPretransitive N R) →
    ∃ c, monodromy c = f

/-- General finite-etale monodromy background across coefficient schemes and
finite discrete additive modules for `K2-018#prop:k2018-arithmetic-characters`,
on the module source basis. The fixed G,N,sigma must be instantiated by the
continuous fundamental-group/Galois model of the pointed base H. -/
structure FiniteEtaleMonodromyBackground (H : Grp (FScheme F)) where
  /-- Continuous arithmetic-group operations in the general model for
  `K2-018#eq:k2018-pointed-character`, on the module source basis. -/
  topologicalG : IsTopologicalGroup G
  /-- Continuous geometric-group operations in the general model for
  `K2-018#eq:k2018-pointed-character`, on the module source basis. -/
  topologicalN : IsTopologicalGroup N
  /-- Continuous arithmetic action on the geometric group in the general model
  for `K2-018#eq:k2018-pointed-character`, on the module source basis. -/
  geometricActionContinuous : ContinuousSMul G N
  /-- General coefficient classification used in
  `K2-018#prop:k2018-arithmetic-characters`, on the module source basis. -/
  coefficients : ∀ (A : Grp (FScheme F)) (R : Type v)
    [AddCommGroup R] [DistribMulAction G R] [TopologicalSpace R]
    [DiscreteTopology R] [IsTopologicalAddGroup R] [ContinuousSMul G R] [Finite R],
    IsFinite A.X.hom → Etale A.X.hom →
    ∀ r : CoefficientRealization s sigma A R, CoverMonodromyData (N := N) s sigma A H R r

/-- Connected monodromy is surjective, deduced using the proved translation
criterion in `K2-018#prop:k2018-arithmetic-characters`, on the module source
basis. Surjectivity is not a background field. -/
def CoverMonodromyData.toSurjective {A H : Grp (FScheme F)} {R : Type v}
    [AddCommGroup R] [DistribMulAction G R] [TopologicalSpace R]
    [IsTopologicalAddGroup R] {r : CoefficientRealization s sigma A R}
    (M : CoverMonodromyData (N := N) s sigma A H R r) :
    CoverClasses A H → SurjectiveCharacters (G := G) (N := N) R := fun c =>
  ⟨M.monodromy c, (forgetCharacter_surjective_iff _).mp
    ((translation_transitive_iff_surjective _).mp (M.connected_transitive c))⟩

/-- The general monodromy class equivalence is derived from its named standard
properties in `K2-018#prop:k2018-arithmetic-characters`, on the module source basis. -/
def CoverMonodromyData.classesEquiv {A H : Grp (FScheme F)} {R : Type v}
    [AddCommGroup R] [DistribMulAction G R] [TopologicalSpace R]
    [IsTopologicalAddGroup R] {r : CoefficientRealization s sigma A R}
    (M : CoverMonodromyData (N := N) s sigma A H R r) :
    CoverClasses A H ≃ SurjectiveCharacters (G := G) (N := N) R :=
  Equiv.ofBijective (M.toSurjective s sigma) ⟨
    fun c d h => M.faithful (congrArg Subtype.val h), by
    intro f
    obtain ⟨c, hc⟩ := M.realizes f.1
      ((translation_transitive_iff_surjective _).mpr
        ((forgetCharacter_surjective_iff _).mpr f.2))
    exact ⟨c, Subtype.ext hc⟩⟩

/-- Forward monodromy characterization of the general class equivalence in
`K2-018#prop:k2018-arithmetic-characters`, on the module source basis. -/
@[simp] theorem CoverMonodromyData.classesEquiv_apply {A H : Grp (FScheme F)} {R : Type v}
    [AddCommGroup R] [DistribMulAction G R] [TopologicalSpace R]
    [IsTopologicalAddGroup R] {r : CoefficientRealization s sigma A R}
    (M : CoverMonodromyData (N := N) s sigma A H R r) (c : CoverClasses A H) :
    ((M.classesEquiv s sigma) c).1 = M.monodromy c := rfl

end GroupCohomology.PrimitiveCharacters.Translation

/- Migration source: the R5Lab/Aglib mirror; exact module in the migration record.
R5 revision c82abf3a72ce1e1cedf4a4f1fe08bea994ad4df5.
SHA256 96820901d132efdab2d3d2681c379bf51dd58e482dd828607a666acdb46a534c.
Definitions, hypotheses and universes are retained modulo native names. -/
