/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

/- Current interface basis: 46f53465aaf3b0167049e9c8e9e2294111bb4281.
Original construction and mathematical provenance are retained below. -/
public import Aglib.AlgebraicGeometry.EtaleCohomology.H1.TorsorPushout
public import Aglib.AlgebraicGeometry.EtaleCohomology.H1.TorsorTrivial
public import Mathlib.CategoryTheory.Sites.CartesianMonoidal
public import Mathlib.Algebra.Category.Grp.CartesianMonoidal

/-!
# Contracted sum of actual abelian sheaf torsors

Construction for `K2-018#eq:k2018-pointed-character`, frozen basis
`7f86e4a1763cc4ec35e9b0a8acd659750355a0de`. We take the actual Cartesian
product torsor and push it out along coefficient addition. Its Ext class is
proved to be the sum, using the two projection maps and coefficient additivity.
-/

@[expose] public section

noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
open scoped MonoidalCategory
namespace AlgebraicGeometry.Scheme.EtaleCohomology
universe u
attribute [local instance] hasSheafifyLarge AddCommGrpCat.cartesianMonoidalCategory
variable {X : Scheme.{u}} {L M : AbelianSheaf.{u, u + 1} X}

/-- Cartesian product of the actual coefficient sheaves (not tensor product). -/
abbrev torsorProductCoefficient (L M : AbelianSheaf.{u, u + 1} X) : AbelianSheaf.{u, u + 1} X :=
  L ⊗ M

/-- The product of two genuine sheaf torsors is a torsor for the product sheaf. -/
def torsorProduct (P : Torsor L) (Q : Torsor M) : Torsor (torsorProductCoefficient L M) where
  carrier := P.carrier ⊗ Q.carrier
  action U a t := (P.action U a.1 t.1, Q.action U a.2 t.2)
  zero_action U t := Prod.ext (P.zero_action U t.1) (Q.zero_action U t.2)
  add_action U a b t := Prod.ext (P.add_action U a.1 b.1 t.1) (Q.add_action U a.2 b.2 t.2)
  naturality f a t := Prod.ext (P.naturality f a.1 t.1) (Q.naturality f a.2 t.2)
  unique_transport U s t := by
    obtain ⟨a, ha, hua⟩ := P.unique_transport U s.1 t.1
    obtain ⟨b, hb, hub⟩ := Q.unique_transport U s.2 t.2
    refine ⟨(a, b), Prod.ext ha hb, ?_⟩
    intro c hc
    exact Prod.ext (hua c.1 (congrArg Prod.fst hc)) (hub c.2 (congrArg Prod.snd hc))
  locally_nonempty U := by
    refine (Scheme.smallEtaleTopology X).superset_covering ?_
      ((Scheme.smallEtaleTopology X).intersection_covering
        (P.locally_nonempty U) (Q.locally_nonempty U))
    rintro V f ⟨⟨p⟩, ⟨q⟩⟩
    exact ⟨(p, q)⟩

/-- The actual first product projection is coefficient-equivariant. -/
noncomputable def torsorProductFst (P : Torsor L) (Q : Torsor M) :
    Torsor.Hom (CartesianMonoidalCategory.fst L M) (torsorProduct P Q) P where
  map := ⟨{ app _ := TypeCat.ofHom Prod.fst
            naturality {_ _} _ := rfl }⟩
  equivariant _ _ _ := rfl

/-- The actual second product projection is coefficient-equivariant. -/
noncomputable def torsorProductSnd (P : Torsor L) (Q : Torsor M) :
    Torsor.Hom (CartesianMonoidalCategory.snd L M) (torsorProduct P Q) Q where
  map := ⟨{ app _ := TypeCat.ofHom Prod.snd
            naturality {_ _} _ := rfl }⟩
  equivariant _ _ _ := rfl

/-- Addition as an actual morphism from the product coefficient sheaf. -/
def torsorCoefficientAdd (L : AbelianSheaf.{u, u + 1} X) : torsorProductCoefficient L L ⟶ L :=
  CartesianMonoidalCategory.fst L L + CartesianMonoidalCategory.snd L L

/-- Contracted sum is built from Cartesian product and actual coefficient pushout. -/
def torsorSum (P Q : Torsor L) : Torsor L :=
  torsorPushout (torsorProduct P Q) (torsorCoefficientAdd L)

/-- Inverse torsor constructed by pushing out along coefficient negation. -/
def torsorNeg (P : Torsor L) : Torsor L := torsorPushout P (-𝟙 L)

section ExtClass
universe w
variable [HasExt.{w} (AbelianSheaf.{u, u + 1} X)]

/-- The class of the constructed contracted sum is the Ext sum. This does not
use Stacks03AJ or transport a group law through a class bijection. -/
theorem torsorExtClass_sum (P Q : Torsor L) :
    torsorExtClass (torsorSum P Q) = torsorExtClass P + torsorExtClass Q := by
  rw [torsorSum, torsorExtClass_pushout, torsorCoefficientAdd, coefficientMap_add,
    AddMonoidHom.add_apply, torsorExtClass_naturality (torsorProductFst P Q),
    torsorExtClass_naturality (torsorProductSnd P Q)]

/-- Negation of a torsor negates its canonical Ext class. -/
theorem torsorExtClass_neg (P : Torsor L) :
    torsorExtClass (torsorNeg P) = -torsorExtClass P := by
  rw [torsorNeg, torsorExtClass_pushout]
  change (torsorExtClass P).comp (Abelian.Ext.mk₀ (-𝟙 L)) (add_zero 1) = _
  rw [Abelian.Ext.mk₀_neg, Abelian.Ext.comp_neg, Abelian.Ext.comp_mk₀_id]

variable (h : Stacks03AJ.{u, w} X)

/-- Contracted sum descends to actual torsor isomorphism classes. The operation
on representatives is the constructed geometric sum; bijectivity supplies only
the equality criterion for the quotient. -/
def torsorClassSum (a b : TorsorClass L) : TorsorClass L :=
  Quotient.liftOn₂ a b (fun P Q => Quotient.mk (Torsor.isomorphicSetoid L) (torsorSum P Q))
    (by
      intro P Q P' Q' hp hq
      apply (h.bijective L).injective
      change torsorExtClass (torsorSum P Q) = torsorExtClass (torsorSum P' Q')
      rw [torsorExtClass_sum, torsorExtClass_sum,
        torsorExtClass_iso (Classical.choice hp), torsorExtClass_iso (Classical.choice hq)])

/-- Geometric inverse descends to actual isomorphism classes. -/
def torsorClassNeg (a : TorsorClass L) : TorsorClass L :=
  Quotient.liftOn a (fun P => Quotient.mk (Torsor.isomorphicSetoid L) (torsorNeg P))
    (by
      intro P Q hp
      apply (h.bijective L).injective
      change torsorExtClass (torsorNeg P) = torsorExtClass (torsorNeg Q)
      rw [torsorExtClass_neg, torsorExtClass_neg, torsorExtClass_iso (Classical.choice hp)])

/-- Additivity for the constructed operation on isomorphism classes. -/
theorem torsorClassToH1_sum (a b : TorsorClass L) :
    torsorClassToH1 L (torsorClassSum h a b) = torsorClassToH1 L a + torsorClassToH1 L b := by
  refine Quotient.inductionOn₂ a b ?_
  exact fun P Q => torsorExtClass_sum P Q

/-- Negation formula for the constructed inverse on isomorphism classes. -/
theorem torsorClassToH1_neg (a : TorsorClass L) :
    torsorClassToH1 L (torsorClassNeg h a) = -torsorClassToH1 L a := by
  refine Quotient.inductionOn a ?_
  exact fun P => torsorExtClass_neg P

/-- The abelian group law uses actual contracted sum and actual negative
coefficient pushout. Stacks03AJ is used to prove the laws by injectivity of
the canonical class map, not to choose or transport the operations. -/
@[instance_reducible]
def torsorClassAddCommGroup (L : AbelianSheaf.{u, u + 1} X) : AddCommGroup (TorsorClass L) := by
  letI : Zero (TorsorClass L) := ⟨Quotient.mk (Torsor.isomorphicSetoid L) (trivialTorsor L)⟩
  letI : Add (TorsorClass L) := ⟨torsorClassSum h⟩
  letI : Neg (TorsorClass L) := ⟨torsorClassNeg h⟩
  exact {
    nsmul := nsmulRec
    zsmul := zsmulRec
    add_assoc a b c := by
      apply (h.bijective L).injective
      change torsorClassToH1 L (torsorClassSum h (torsorClassSum h a b) c) =
        torsorClassToH1 L (torsorClassSum h a (torsorClassSum h b c))
      simp only [torsorClassToH1_sum, add_assoc]
    add_comm a b := by
      apply (h.bijective L).injective
      change torsorClassToH1 L (torsorClassSum h a b) = torsorClassToH1 L (torsorClassSum h b a)
      simp only [torsorClassToH1_sum, add_comm]
    zero_add a := by
      apply (h.bijective L).injective
      change torsorClassToH1 L (torsorClassSum h (Quotient.mk _ (trivialTorsor L)) a) = _
      simp only [torsorClassToH1_sum, torsorClassToH1_mk, torsorExtClass_trivial, zero_add]
    add_zero a := by
      apply (h.bijective L).injective
      change torsorClassToH1 L (torsorClassSum h a (Quotient.mk _ (trivialTorsor L))) = _
      simp only [torsorClassToH1_sum, torsorClassToH1_mk, torsorExtClass_trivial, add_zero]
    neg_add_cancel a := by
      apply (h.bijective L).injective
      change torsorClassToH1 L (torsorClassSum h (torsorClassNeg h a) a) =
        torsorClassToH1 L (Quotient.mk _ (trivialTorsor L))
      simp only [torsorClassToH1_sum, torsorClassToH1_neg, torsorClassToH1_mk,
        torsorExtClass_trivial, neg_add_cancel] }

/-- The canonical extension/boundary map is an additive equivalence for the
proved contracted-sum group law. Its only comparison premise is Stacks03AJ. -/
def torsorClassAddEquiv (L : AbelianSheaf.{u, u + 1} X) :
    letI := torsorClassAddCommGroup h L
    TorsorClass L ≃+ H1Etale X L := by
  letI := torsorClassAddCommGroup h L
  exact { torsorClassEquiv h L with map_add' := torsorClassToH1_sum h }

end ExtClass
end AlgebraicGeometry.Scheme.EtaleCohomology

/- Migration source: the R5Lab/Aglib mirror; exact module in the migration record.
R5 revision c82abf3a72ce1e1cedf4a4f1fe08bea994ad4df5.
SHA256 436ffe32d464ce9570e14f1fb4c3c9d3956394c05e75ef10179dbb46537a58e7.
Definitions, hypotheses and universes are retained modulo native names. -/
