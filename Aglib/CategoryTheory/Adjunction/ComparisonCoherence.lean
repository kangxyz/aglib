/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.CategoryTheory.Adjunction.LeftAdjointComparison

/-! # Coherence of specified comparisons under original adjunction conjugacy -/

@[expose] public noncomputable section

open CategoryTheory

namespace CategoryTheory

section IdentityNormalization
variable {A B : Type*} [Category* A] [Category* B]
  {L₁ L₂ : A ⥤ B} {R₁ R₂ : B ⥤ A} {I J : A ⥤ A}

/-- Removing an original identity adjunction from a specified comparison preserves its mate. -/
theorem conjugateEquiv_normalizedComparison
    (a : L₁ ⊣ R₁) (b : L₂ ⊣ R₂) (c : I ⊣ J)
    (e : L₁ ≅ I ⋙ L₂) (E : R₁ ≅ R₂ ⋙ J) (d : I ≅ 𝟭 A) (D : J ≅ 𝟭 A)
    (he : conjugateEquiv (c.comp b) a e.hom = E.inv)
    (hd : conjugateEquiv Adjunction.id c d.hom = D.inv) :
    conjugateEquiv b a
      (e ≪≫ Functor.isoWhiskerRight d L₂ ≪≫ Functor.leftUnitor L₂).hom =
      (E ≪≫ Functor.isoWhiskerLeft R₂ D ≪≫ Functor.rightUnitor R₂).inv := by
  simp only [Iso.trans_hom, Functor.isoWhiskerRight_hom]
  rw [← conjugateEquiv_comp _ (c.comp b),
    ← conjugateEquiv_comp _ (Adjunction.id.comp b),
    conjugateEquiv_leftUnitor_hom, conjugateEquiv_whiskerRight, hd, he]
  simp only [Iso.trans_inv, Functor.isoWhiskerLeft_inv, Category.assoc]

end IdentityNormalization

section Composition
variable {A B C D : Type*} [Category* A] [Category* B] [Category* C] [Category* D]
  {Li : A ⥤ D} {Ri : D ⥤ A} {Lj : A ⥤ C} {Rj : C ⥤ A}
  {Ll : A ⥤ B} {Rl : B ⥤ A} {Lf : B ⥤ C} {Rf : C ⥤ B}
  {Lk : C ⥤ D} {Rk : D ⥤ C} {Lt : B ⥤ D} {Rt : D ⥤ B}

/-- Coherence of specified left comparisons follows from coherence of their actual conjugates. -/
theorem adjunctionComparison_comp_of_conjugate
    (ai : Li ⊣ Ri) (aj : Lj ⊣ Rj) (al : Ll ⊣ Rl)
    (af : Lf ⊣ Rf) (ak : Lk ⊣ Rk) (atotal : Lt ⊣ Rt)
    (σf : Ll ⋙ Lf ≅ Lj) (σk : Lj ⋙ Lk ≅ Li) (σt : Ll ⋙ Lt ≅ Li)
    (Ef : Rf ⋙ Rl ≅ Rj) (Ek : Rk ⋙ Rj ≅ Ri) (Et : Rt ⋙ Rl ≅ Ri)
    (c : Lt ≅ Lf ⋙ Lk) (d : Rt ≅ Rk ⋙ Rf)
    (hf : conjugateEquiv aj (al.comp af) σf.hom = Ef.inv)
    (hk : conjugateEquiv ai (aj.comp ak) σk.hom = Ek.inv)
    (ht : conjugateEquiv ai (al.comp atotal) σt.hom = Et.inv)
    (hc : conjugateEquiv (af.comp ak) atotal c.hom = d.inv)
    (hE : Et = Functor.isoWhiskerRight d Rl ≪≫ Functor.associator Rk Rf Rl ≪≫
      Functor.isoWhiskerLeft Rk Ef ≪≫ Ek) :
    σt = Functor.isoWhiskerLeft Ll c ≪≫ (Functor.associator Ll Lf Lk).symm ≪≫
      Functor.isoWhiskerRight σf Lk ≪≫ σk := by
  apply Iso.ext
  apply (conjugateEquiv ai (al.comp atotal)).injective
  simp only [Iso.trans_hom, Functor.isoWhiskerLeft_hom,
    Functor.isoWhiskerRight_hom, Iso.symm_hom]
  rw [← conjugateEquiv_comp _ (al.comp (af.comp ak)),
    ← conjugateEquiv_comp _ ((al.comp af).comp ak),
    ← conjugateEquiv_comp _ (aj.comp ak), conjugateEquiv_whiskerLeft,
    conjugateEquiv_whiskerRight, conjugateEquiv_associator_inv, hc, hf, hk, ht]
  simpa only [Iso.trans_inv, Functor.isoWhiskerRight_inv,
    Functor.isoWhiskerLeft_inv, Category.assoc] using congrArg Iso.inv hE

end Composition

section Identity
variable {A B : Type*} [Category* A] [Category* B]
  {L : A ⥤ B} {R : B ⥤ A} {I J : B ⥤ B}

/-- Identity normalization of a specified comparison follows from its actual original mate. -/
theorem adjunctionComparison_id_of_conjugate
    (a : L ⊣ R) (c : I ⊣ J) (σ : L ⋙ I ≅ L) (E : J ⋙ R ≅ R)
    (d : I ≅ 𝟭 B) (D : J ≅ 𝟭 B)
    (hσ : conjugateEquiv a (a.comp c) σ.hom = E.inv)
    (hd : conjugateEquiv Adjunction.id c d.hom = D.inv)
    (hE : E = Functor.isoWhiskerRight D R ≪≫ Functor.leftUnitor R) :
    σ = Functor.isoWhiskerLeft L d ≪≫ Functor.rightUnitor L := by
  apply Iso.ext
  apply (conjugateEquiv a (a.comp c)).injective
  simp only [Iso.trans_hom, Functor.isoWhiskerLeft_hom]
  rw [← conjugateEquiv_comp _ (a.comp Adjunction.id),
    conjugateEquiv_rightUnitor_hom, conjugateEquiv_whiskerLeft, hd, hσ]
  simpa only [Iso.trans_inv, Functor.isoWhiskerRight_inv] using congrArg Iso.inv hE

end Identity

end CategoryTheory
