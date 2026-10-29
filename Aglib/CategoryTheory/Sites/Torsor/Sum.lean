/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.CategoryTheory.Sites.Torsor.Trivial
public import Mathlib.CategoryTheory.Sites.CartesianMonoidal
public import Mathlib.Algebra.Category.Grp.CartesianMonoidal

/-! # The actual contracted-sum operations on torsor classes

The product torsor, pushout along coefficient addition and negative coefficient
pushout define the operations. The proved classifier supplies their quotient
well-definedness and laws without choosing or transporting new operations.
-/

@[expose] public section

noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory.Limits Opposite

namespace CategoryTheory.Sheaf

universe u v w e
variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
open scoped MonoidalCategory
attribute [local instance] AddCommGrpCat.cartesianMonoidalCategory
variable {L M : Sheaf J AddCommGrpCat.{w}}

/-- Cartesian product of the actual coefficient sheaves (not tensor product). -/
abbrev torsorProductCoefficient (L M : Sheaf J AddCommGrpCat.{w}) : Sheaf J AddCommGrpCat.{w} :=
  L ⊗ M

/-- The product of two genuine sheaf torsors is a torsor for the product sheaf. -/
def torsorProduct (P : Torsor L) (Q : Torsor M) : Torsor (torsorProductCoefficient L M) where
  carrier := P.carrier ⊗ Q.carrier
  action U a t := (P.action U a.1 t.1, Q.action U a.2 t.2)
  zero_action U t := _root_.Prod.ext (P.zero_action U t.1) (Q.zero_action U t.2)
  add_action U a b t := _root_.Prod.ext (P.add_action U a.1 b.1 t.1) (Q.add_action U a.2 b.2 t.2)
  naturality f a t := _root_.Prod.ext (P.naturality f a.1 t.1) (Q.naturality f a.2 t.2)
  unique_transport U s t := by
    obtain ⟨a, ha, hua⟩ := P.unique_transport U s.1 t.1
    obtain ⟨b, hb, hub⟩ := Q.unique_transport U s.2 t.2
    refine ⟨(a, b), _root_.Prod.ext ha hb, ?_⟩
    intro c hc
    exact _root_.Prod.ext (hua c.1 (congrArg _root_.Prod.fst hc))
      (hub c.2 (congrArg _root_.Prod.snd hc))
  locally_nonempty U := by
    refine J.superset_covering ?_
      (J.intersection_covering
        (P.locally_nonempty U) (Q.locally_nonempty U))
    rintro V f ⟨⟨p⟩, ⟨q⟩⟩
    exact ⟨(p, q)⟩

/-- The actual first product projection is coefficient-equivariant. -/
noncomputable def torsorProductFst (P : Torsor L) (Q : Torsor M) :
    Torsor.Hom (CartesianMonoidalCategory.fst L M) (torsorProduct P Q) P where
  map := ⟨{ app _ := TypeCat.ofHom _root_.Prod.fst
            naturality {_ _} _ := rfl }⟩
  equivariant _ _ _ := rfl

/-- The actual second product projection is coefficient-equivariant. -/
noncomputable def torsorProductSnd (P : Torsor L) (Q : Torsor M) :
    Torsor.Hom (CartesianMonoidalCategory.snd L M) (torsorProduct P Q) Q where
  map := ⟨{ app _ := TypeCat.ofHom _root_.Prod.snd
            naturality {_ _} _ := rfl }⟩
  equivariant _ _ _ := rfl

/-- Addition as an actual morphism from the product coefficient sheaf. -/
def torsorCoefficientAdd (L : Sheaf J AddCommGrpCat.{w}) : torsorProductCoefficient L L ⟶ L :=
  CartesianMonoidalCategory.fst L L + CartesianMonoidalCategory.snd L L


variable [HasSheafify J AddCommGrpCat.{w}]
variable [J.WEqualsLocallyBijective AddCommGrpCat.{w}]

/-- Contracted sum is built from Cartesian product and actual coefficient pushout. -/
def torsorSum (P Q : Torsor L) : Torsor L :=
  torsorPushout (torsorProduct P Q) (torsorCoefficientAdd L)

/-- Inverse torsor constructed by pushing out along coefficient negation. -/
def torsorNeg (P : Torsor L) : Torsor L := torsorPushout P (-𝟙 L)

section ExtClass
variable [HasExt.{e} (Sheaf J AddCommGrpCat.{w})]

/-- The class of the constructed contracted sum is the Ext sum. This does not
use classification or transport a group law through a class bijection. -/
theorem torsorExtClass_sum (P Q : Torsor L) :
    torsorExtClass (torsorSum P Q) = torsorExtClass P + torsorExtClass Q := by
  rw [torsorSum, torsorExtClass_pushout, torsorCoefficientAdd, H.map_add_apply,
    torsorExtClass_naturality (torsorProductFst P Q),
    torsorExtClass_naturality (torsorProductSnd P Q)]

/-- Negation of a torsor negates its canonical Ext class. -/
theorem torsorExtClass_neg (P : Torsor L) :
    torsorExtClass (torsorNeg P) = -torsorExtClass P := by
  rw [torsorNeg, torsorExtClass_pushout]
  change (torsorExtClass P).comp (Abelian.Ext.mk₀ (-𝟙 L)) (add_zero 1) = _
  rw [Abelian.Ext.mk₀_neg, Abelian.Ext.comp_neg, Abelian.Ext.comp_mk₀_id]


/-- Contracted sum descends to actual torsor isomorphism classes. The operation
on representatives is the constructed geometric sum; bijectivity supplies only
the equality criterion for the quotient. -/
def torsorClassSum (a b : TorsorClass L) : TorsorClass L :=
  _root_.Quotient.liftOn₂ a b
    (fun P Q => _root_.Quotient.mk (Torsor.isomorphicSetoid L) (torsorSum P Q))
    (by
      intro P Q P' Q' hp hq
      apply (torsorClassToH1_bijective L).injective
      change torsorExtClass (torsorSum P Q) = torsorExtClass (torsorSum P' Q')
      rw [torsorExtClass_sum, torsorExtClass_sum,
        torsorExtClass_iso (Classical.choice hp), torsorExtClass_iso (Classical.choice hq)])

/-- Geometric inverse descends to actual isomorphism classes. -/
def torsorClassNeg (a : TorsorClass L) : TorsorClass L :=
  _root_.Quotient.liftOn a (fun P => _root_.Quotient.mk (Torsor.isomorphicSetoid L) (torsorNeg P))
    (by
      intro P Q hp
      apply (torsorClassToH1_bijective L).injective
      change torsorExtClass (torsorNeg P) = torsorExtClass (torsorNeg Q)
      rw [torsorExtClass_neg, torsorExtClass_neg, torsorExtClass_iso (Classical.choice hp)])

/-- Additivity for the constructed operation on isomorphism classes. -/
theorem torsorClassToH1_sum (a b : TorsorClass L) :
    torsorClassToH1 L (torsorClassSum a b) = torsorClassToH1 L a + torsorClassToH1 L b := by
  refine _root_.Quotient.inductionOn₂ a b ?_
  exact fun P Q => torsorExtClass_sum P Q

/-- Negation formula for the constructed inverse on isomorphism classes. -/
theorem torsorClassToH1_neg (a : TorsorClass L) :
    torsorClassToH1 L (torsorClassNeg a) = -torsorClassToH1 L a := by
  refine _root_.Quotient.inductionOn a ?_
  exact fun P => torsorExtClass_neg P

/-- The abelian group law uses actual contracted sum and actual negative
coefficient pushout. The proved classifier supplies the laws by injectivity of
the canonical class map; the operations are the original constructions. -/
@[instance_reducible]
def torsorClassAddCommGroup (L : Sheaf J AddCommGrpCat.{w}) : AddCommGroup (TorsorClass L) := by
  letI : Zero (TorsorClass L) := ⟨_root_.Quotient.mk (Torsor.isomorphicSetoid L) (trivialTorsor L)⟩
  letI : Add (TorsorClass L) := ⟨torsorClassSum⟩
  letI : Neg (TorsorClass L) := ⟨torsorClassNeg⟩
  exact {
    nsmul := nsmulRec
    zsmul := zsmulRec
    add_assoc a b c := by
      apply (torsorClassToH1_bijective L).injective
      change torsorClassToH1 L (torsorClassSum (torsorClassSum a b) c) =
        torsorClassToH1 L (torsorClassSum a (torsorClassSum b c))
      simp only [torsorClassToH1_sum, add_assoc]
    add_comm a b := by
      apply (torsorClassToH1_bijective L).injective
      change torsorClassToH1 L (torsorClassSum a b) = torsorClassToH1 L (torsorClassSum b a)
      simp only [torsorClassToH1_sum, add_comm]
    zero_add a := by
      apply (torsorClassToH1_bijective L).injective
      change torsorClassToH1 L (torsorClassSum (_root_.Quotient.mk _ (trivialTorsor L)) a) = _
      simp only [torsorClassToH1_sum, torsorClassToH1_mk, torsorExtClass_trivial, zero_add]
    add_zero a := by
      apply (torsorClassToH1_bijective L).injective
      change torsorClassToH1 L (torsorClassSum a (_root_.Quotient.mk _ (trivialTorsor L))) = _
      simp only [torsorClassToH1_sum, torsorClassToH1_mk, torsorExtClass_trivial, add_zero]
    neg_add_cancel a := by
      apply (torsorClassToH1_bijective L).injective
      change torsorClassToH1 L (torsorClassSum (torsorClassNeg a) a) =
        torsorClassToH1 L (_root_.Quotient.mk _ (trivialTorsor L))
      simp only [torsorClassToH1_sum, torsorClassToH1_neg, torsorClassToH1_mk,
        torsorExtClass_trivial, neg_add_cancel] }

/-- The canonical extension/boundary map is an additive equivalence for the
proved contracted-sum group law. Its class bijection is the proved actual classifier. -/
def torsorClassAddEquiv (L : Sheaf J AddCommGrpCat.{w}) :
    letI := torsorClassAddCommGroup L
    TorsorClass L ≃+ H L 1 := by
  letI := torsorClassAddCommGroup L
  exact { torsorClassEquiv L with map_add' := torsorClassToH1_sum }

end ExtClass
end CategoryTheory.Sheaf
