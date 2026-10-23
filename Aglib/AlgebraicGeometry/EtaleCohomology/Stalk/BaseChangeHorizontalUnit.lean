/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.BaseChangeMap

/-! # The original underived exchange and the horizontal adjunction units -/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits

private theorem conjugate_iso_chain {C D : Type*} [Category* C] [Category* D]
    {L₀ L₁ L₂ L₃ : C ⥤ D} {R₀ R₁ R₂ R₃ : D ⥤ C}
    (a₀ : L₀ ⊣ R₀) (a₁ : L₁ ⊣ R₁) (a₂ : L₂ ⊣ R₂) (a₃ : L₃ ⊣ R₃)
    (e₀ : L₁ ≅ L₀) (m : L₂ ≅ L₁) (e₁ : L₂ ≅ L₃)
    (r₀ : R₀ ≅ R₁) (rₘ : R₁ ≅ R₂) (r₁ : R₂ ≅ R₃)
    (h₀ : conjugateEquiv a₀ a₁ e₀.hom = r₀.hom)
    (hₘ : conjugateEquiv a₁ a₂ m.hom = rₘ.hom)
    (h₁ : conjugateEquiv a₂ a₃ e₁.inv = r₁.hom) :
    conjugateEquiv a₀ a₃ (e₁.symm ≪≫ m ≪≫ e₀).hom = (r₀ ≪≫ rₘ ≪≫ r₁).hom := by
  simp only [Iso.trans_hom, Iso.symm_hom]
  rw [← conjugateEquiv_comp a₀ a₂ a₃, ← conjugateEquiv_comp a₀ a₁ a₂,
    h₀, hₘ, h₁, Category.assoc]

private theorem horizontal_unit_of_eq
    {A B C D : Type*} [Category* A] [Category* B] [Category* C] [Category* D]
    {L₁ : A ⥤ B} {R₁ : B ⥤ A} {L₂ : C ⥤ D} {R₂ : D ⥤ C}
    (a₁ : L₁ ⊣ R₁) (a₂ : L₂ ⊣ R₂) {G : A ⥤ C} {H : B ⥤ D}
    (β : G ⋙ L₂ ⟶ L₁ ⋙ H) (ρ : R₁ ⋙ G ⟶ H ⋙ R₂)
    (hρ : (mateEquiv a₁ a₂ (TwoSquare.mk _ _ _ _ β)).natTrans = ρ) (F : A) :
    G.map (a₁.unit.app F) ≫ ρ.app (L₁.obj F) =
      a₂.unit.app (G.obj F) ≫ R₂.map (β.app F) := by
  rw [← hρ]
  exact unit_mateEquiv a₁ a₂ (TwoSquare.mk _ _ _ _ β) F

universe u

namespace AlgebraicGeometry.Scheme.EtaleCohomology

attribute [local instance] hasSheafifyLarge

private theorem conjugate_inverseImageComp_inv {X S T : Scheme.{u}}
    (f : S ⟶ X) (g : T ⟶ S) :
    conjugateEquiv (inverseImageAdjunction (g ≫ f))
      ((inverseImageAdjunction f).comp (inverseImageAdjunction g))
      (inverseImageComp f g).inv = (directImageCompIso f g).inv := by
  apply (cancel_epi (directImageCompIso f g).hom).1
  rw [← conjugateEquiv_inverseImageComp_hom f g, conjugateEquiv_comp,
    Iso.inv_hom_id, conjugateEquiv_id, conjugateEquiv_inverseImageComp_hom,
    Iso.hom_inv_id]

variable {X S X' S' : Scheme.{u}} (f : X ⟶ S) (f' : X' ⟶ S')
  (g : S' ⟶ S) (g' : X' ⟶ X) (h : f' ≫ g = g' ≫ f)

/-- The native right-adjoint comparison of the original commuting scheme square. -/
def directImageSquareIso :
    directImage g' ⋙ directImage f ≅ directImage f' ⋙ directImage g :=
  directImageCompIso f g' ≪≫
    eqToIso (congrArg (fun k : X' ⟶ S => directImage k) h.symm) ≪≫
      (directImageCompIso g f').symm

/-- Conjugating the actual inverse-image square recovers the native direct-image square. -/
theorem conjugateEquiv_inverseImageSquareIso_hom :
    conjugateEquiv ((inverseImageAdjunction f).comp (inverseImageAdjunction g'))
      ((inverseImageAdjunction g).comp (inverseImageAdjunction f'))
      (inverseImageSquareIso f f' g g' h).hom =
        (directImageSquareIso f f' g g' h).hom := by
  exact conjugate_iso_chain
    ((inverseImageAdjunction f).comp (inverseImageAdjunction g'))
    (inverseImageAdjunction (g' ≫ f)) (inverseImageAdjunction (f' ≫ g))
    ((inverseImageAdjunction g).comp (inverseImageAdjunction f'))
    (inverseImageComp f g')
    (eqToIso (congrArg (fun k : X' ⟶ S => inverseImage k) h))
    (inverseImageComp g f') (directImageCompIso f g')
    (eqToIso (congrArg (fun k : X' ⟶ S => directImage k) h.symm))
    (directImageCompIso g f').symm
    (conjugateEquiv_inverseImageComp_hom f g')
    (conjugateEquiv_inverseImage_eqToHom h) (conjugate_inverseImageComp_inv g f')

/-- The horizontal mate of the original exchange is the native direct-image square. -/
theorem mate_baseChangeMap :
    (mateEquiv (inverseImageAdjunction g') (inverseImageAdjunction g)
      (TwoSquare.mk _ _ _ _ (baseChangeMap f f' g g' h))).natTrans =
        (directImageSquareIso f f' g g' h).hom := by
  exact (iterated_mateEquiv_conjugateEquiv
    (inverseImageAdjunction f) (inverseImageAdjunction f')
    (inverseImageAdjunction g) (inverseImageAdjunction g')
    (TwoSquare.mk _ _ _ _ (inverseImageSquareIso f f' g g' h).hom)).trans
      (conjugateEquiv_inverseImageSquareIso_hom f f' g g' h)

/-- The original exchange is normalized by the original horizontal adjunction units. -/
theorem baseChangeMap_horizontal_unit (F : AbelianSheaf.{u, u + 1} X) :
    (directImage f).map ((inverseImageAdjunction g').unit.app F) ≫
        (directImageSquareIso f f' g g' h).hom.app ((inverseImage g').obj F) =
      (inverseImageAdjunction g).unit.app ((directImage f).obj F) ≫
        (directImage g).map ((baseChangeMap f f' g g' h).app F) := by
  exact horizontal_unit_of_eq (inverseImageAdjunction g') (inverseImageAdjunction g)
    (baseChangeMap f f' g g' h) (directImageSquareIso f f' g g' h).hom
    (mate_baseChangeMap f f' g g' h) F

end AlgebraicGeometry.Scheme.EtaleCohomology
