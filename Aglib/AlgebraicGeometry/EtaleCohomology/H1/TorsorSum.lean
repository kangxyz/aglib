/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.CategoryTheory.Sites.Torsor.Sum
public import Aglib.AlgebraicGeometry.EtaleCohomology.H1.TorsorPushout
public import Aglib.AlgebraicGeometry.EtaleCohomology.H1.TorsorTrivial

/-! # The original etale contracted-sum operations

The product, terminal-one pushout and representative operations remain the
original data. Their values agree with the generic operations; the generic
proofs supply the class formulas and group laws on those same data.
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
  CategoryTheory.Sheaf.torsorProductCoefficient L M

/-- The product of two genuine sheaf torsors is a torsor for the product sheaf. -/
abbrev torsorProduct (P : Torsor L) (Q : Torsor M) : Torsor (torsorProductCoefficient L M) :=
  CategoryTheory.Sheaf.torsorProduct P Q

/-- The actual first product projection is coefficient-equivariant. -/
abbrev torsorProductFst (P : Torsor L) (Q : Torsor M) :
    Torsor.Hom (CartesianMonoidalCategory.fst L M) (torsorProduct P Q) P :=
  CategoryTheory.Sheaf.torsorProductFst P Q

/-- The actual second product projection is coefficient-equivariant. -/
abbrev torsorProductSnd (P : Torsor L) (Q : Torsor M) :
    Torsor.Hom (CartesianMonoidalCategory.snd L M) (torsorProduct P Q) Q :=
  CategoryTheory.Sheaf.torsorProductSnd P Q

/-- Addition as an actual morphism from the product coefficient sheaf. -/
abbrev torsorCoefficientAdd (L : AbelianSheaf.{u, u + 1} X) : torsorProductCoefficient L L ⟶ L :=
  CategoryTheory.Sheaf.torsorCoefficientAdd L

/-- Contracted sum is built from Cartesian product and actual coefficient pushout. -/
def torsorSum (P Q : Torsor L) : Torsor L :=
  torsorPushout (torsorProduct P Q) (torsorCoefficientAdd L)

/-- Inverse torsor constructed by pushing out along coefficient negation. -/
def torsorNeg (P : Torsor L) : Torsor L := torsorPushout P (-𝟙 L)

/-- The original contracted sum is the intrinsic sum on the same actual torsors. -/
theorem torsorSum_eq_generic (P Q : Torsor L) :
    torsorSum P Q = CategoryTheory.Sheaf.torsorSum P Q :=
  torsorPushout_eq_generic (torsorProduct P Q) (torsorCoefficientAdd L)

/-- The original negative pushout is the intrinsic negative torsor. -/
theorem torsorNeg_eq_generic (P : Torsor L) :
    torsorNeg P = CategoryTheory.Sheaf.torsorNeg P :=
  torsorPushout_eq_generic P (-𝟙 L)

section ExtClass
universe w
variable [HasExt.{w} (AbelianSheaf.{u, u + 1} X)]

/-- The class of the constructed contracted sum is the Ext sum. This does not
use Stacks03AJ or transport a group law through a class bijection. -/
theorem torsorExtClass_sum (P Q : Torsor L) :
    torsorExtClass (torsorSum P Q) = torsorExtClass P + torsorExtClass Q := by
  simpa only [torsorSum_eq_generic] using CategoryTheory.Sheaf.torsorExtClass_sum P Q

/-- Negation of a torsor negates its canonical Ext class. -/
theorem torsorExtClass_neg (P : Torsor L) :
    torsorExtClass (torsorNeg P) = -torsorExtClass P := by
  simpa only [torsorNeg_eq_generic] using CategoryTheory.Sheaf.torsorExtClass_neg P

variable (h : Stacks03AJ.{u, w} X)

/-- Contracted sum descends to actual torsor isomorphism classes. The operation
on representatives is the constructed geometric sum; bijectivity supplies only
the equality criterion for the quotient. -/
def torsorClassSum (a b : TorsorClass L) : TorsorClass L :=
  _root_.Quotient.liftOn₂ a b
    (fun P Q => _root_.Quotient.mk (Torsor.isomorphicSetoid L) (torsorSum P Q))
    (by
      intro P Q P' Q' hp hq
      apply (h.bijective L).injective
      change torsorExtClass (torsorSum P Q) = torsorExtClass (torsorSum P' Q')
      rw [torsorExtClass_sum, torsorExtClass_sum,
        torsorExtClass_iso (Classical.choice hp), torsorExtClass_iso (Classical.choice hq)])

/-- Geometric inverse descends to actual isomorphism classes. -/
def torsorClassNeg (a : TorsorClass L) : TorsorClass L :=
  _root_.Quotient.liftOn a (fun P => _root_.Quotient.mk (Torsor.isomorphicSetoid L) (torsorNeg P))
    (by
      intro P Q hp
      apply (h.bijective L).injective
      change torsorExtClass (torsorNeg P) = torsorExtClass (torsorNeg Q)
      rw [torsorExtClass_neg, torsorExtClass_neg, torsorExtClass_iso (Classical.choice hp)])

/-- The original representative sum descends to the same generic class operation. -/
theorem torsorClassSum_eq_generic (a b : TorsorClass L) :
    torsorClassSum h a b = CategoryTheory.Sheaf.torsorClassSum a b := by
  refine _root_.Quotient.inductionOn₂ a b ?_
  intro P Q
  exact congrArg (_root_.Quotient.mk (Torsor.isomorphicSetoid L)) (torsorSum_eq_generic P Q)

/-- The original representative inverse descends to the same generic class operation. -/
theorem torsorClassNeg_eq_generic (a : TorsorClass L) :
    torsorClassNeg h a = CategoryTheory.Sheaf.torsorClassNeg a := by
  refine _root_.Quotient.inductionOn a ?_
  intro P
  exact congrArg (_root_.Quotient.mk (Torsor.isomorphicSetoid L)) (torsorNeg_eq_generic P)

/-- Additivity for the constructed operation on isomorphism classes. -/
theorem torsorClassToH1_sum (a b : TorsorClass L) :
    torsorClassToH1 L (torsorClassSum h a b) = torsorClassToH1 L a + torsorClassToH1 L b := by
  simpa only [torsorClassSum_eq_generic] using CategoryTheory.Sheaf.torsorClassToH1_sum a b

/-- Negation formula for the constructed inverse on isomorphism classes. -/
theorem torsorClassToH1_neg (a : TorsorClass L) :
    torsorClassToH1 L (torsorClassNeg h a) = -torsorClassToH1 L a := by
  simpa only [torsorClassNeg_eq_generic] using CategoryTheory.Sheaf.torsorClassToH1_neg a

/-- The original operations form the abelian group proved by the generic classifier. -/
@[instance_reducible]
def torsorClassAddCommGroup (L : AbelianSheaf.{u, u + 1} X) : AddCommGroup (TorsorClass L) := by
  have ha (a b c : TorsorClass L) :
      CategoryTheory.Sheaf.torsorClassSum (CategoryTheory.Sheaf.torsorClassSum a b) c =
        CategoryTheory.Sheaf.torsorClassSum a (CategoryTheory.Sheaf.torsorClassSum b c) := by
    let := CategoryTheory.Sheaf.torsorClassAddCommGroup L
    exact add_assoc a b c
  have hc (a b : TorsorClass L) :
      CategoryTheory.Sheaf.torsorClassSum a b = CategoryTheory.Sheaf.torsorClassSum b a := by
    let := CategoryTheory.Sheaf.torsorClassAddCommGroup L
    exact add_comm a b
  have hz (a : TorsorClass L) :
      CategoryTheory.Sheaf.torsorClassSum
        (_root_.Quotient.mk (Torsor.isomorphicSetoid L) (trivialTorsor L)) a = a := by
    let := CategoryTheory.Sheaf.torsorClassAddCommGroup L
    exact zero_add a
  have hz' (a : TorsorClass L) :
      CategoryTheory.Sheaf.torsorClassSum a
        (_root_.Quotient.mk (Torsor.isomorphicSetoid L) (trivialTorsor L)) = a := by
    let := CategoryTheory.Sheaf.torsorClassAddCommGroup L
    exact add_zero a
  have hn (a : TorsorClass L) :
      CategoryTheory.Sheaf.torsorClassSum (CategoryTheory.Sheaf.torsorClassNeg a) a =
        _root_.Quotient.mk (Torsor.isomorphicSetoid L) (trivialTorsor L) := by
    let := CategoryTheory.Sheaf.torsorClassAddCommGroup L
    exact neg_add_cancel a
  letI : Zero (TorsorClass L) :=
    ⟨_root_.Quotient.mk (Torsor.isomorphicSetoid L) (trivialTorsor L)⟩
  letI : Add (TorsorClass L) := ⟨torsorClassSum h⟩
  letI : Neg (TorsorClass L) := ⟨torsorClassNeg h⟩
  exact {
    nsmul := nsmulRec
    zsmul := zsmulRec
    add_assoc a b c := by
      change torsorClassSum h (torsorClassSum h a b) c =
        torsorClassSum h a (torsorClassSum h b c)
      simpa only [torsorClassSum_eq_generic] using ha a b c
    add_comm a b := by
      change torsorClassSum h a b = torsorClassSum h b a
      simpa only [torsorClassSum_eq_generic] using hc a b
    zero_add a := by
      change torsorClassSum h (_root_.Quotient.mk _ (trivialTorsor L)) a = a
      simpa only [torsorClassSum_eq_generic] using hz a
    add_zero a := by
      change torsorClassSum h a (_root_.Quotient.mk _ (trivialTorsor L)) = a
      simpa only [torsorClassSum_eq_generic] using hz' a
    neg_add_cancel a := by
      change torsorClassSum h (torsorClassNeg h a) a =
        _root_.Quotient.mk _ (trivialTorsor L)
      simpa only [torsorClassSum_eq_generic, torsorClassNeg_eq_generic] using hn a }

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
