/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Mathlib.CategoryTheory.Whiskering

/-!
# Composition comparisons and change of models

Horizontal comparison of two functors respects comparison cocycles. A commuting
square of model maps therefore gives the same map between chosen models. These
lemmas do not require a category structure on the collection of models.
-/

@[expose] public section

namespace CategoryTheory

universe v₁ v₂ v₃ u₁ u₂ u₃

variable {A : Type u₁} {B : Type u₂} {C : Type u₃}
  [Category.{v₁} A] [Category.{v₂} B] [Category.{v₃} C]

/-- Compare a composite by changing its first and then its second functor. -/
def compositionPairIso {F G : A ⥤ B} {H I : B ⥤ C}
    (α : F ≅ G) (β : H ≅ I) : F ⋙ H ≅ G ⋙ I :=
  Functor.isoWhiskerRight α H ≪≫ Functor.isoWhiskerLeft G β

lemma compositionPairIso_eq_hcomp {F G : A ⥤ B} {H I : B ⥤ C}
    (α : F ≅ G) (β : H ≅ I) : compositionPairIso α β = NatIso.hcomp α β := by
  apply Iso.ext
  ext X
  exact (NatTrans.hcomp_app' α.hom β.hom X).symm

@[simp]
lemma compositionPairIso_trans {F G J : A ⥤ B} {H I K : B ⥤ C}
    (α : F ≅ G) (α' : G ≅ J) (β : H ≅ I) (β' : I ≅ K) :
    compositionPairIso α β ≪≫ compositionPairIso α' β' =
      compositionPairIso (α ≪≫ α') (β ≪≫ β') := by
  simp only [compositionPairIso_eq_hcomp]
  apply Iso.ext
  exact (NatTrans.exchange α.hom α'.hom β.hom β'.hom).symm

/-- Transport a map across model comparisons. Equality of the original model
square, together with the two comparison cocycles, implies choice independence. -/
lemma iso_conjugate_eq_of_square {U V X X' Y Y' : C}
    (p : U ≅ X) (p' : U ≅ X') (q : V ≅ Y) (q' : V ≅ Y')
    (a : X ≅ Y) (a' : X' ≅ Y') (s : X' ≅ X) (t : Y' ≅ Y)
    (hp : p' ≪≫ s = p) (hq : q' ≪≫ t = q)
    (ha : s ≪≫ a = a' ≪≫ t) :
    p ≪≫ a ≪≫ q.symm = p' ≪≫ a' ≪≫ q'.symm := by
  subst p
  subst q
  apply Iso.ext
  have h := congrArg Iso.hom ha
  dsimp at h ⊢
  simp only [Category.assoc] at h ⊢
  rw [← Category.assoc s.hom, h]
  simp

end CategoryTheory
