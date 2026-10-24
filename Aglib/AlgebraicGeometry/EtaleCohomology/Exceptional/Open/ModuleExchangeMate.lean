/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.Exceptional.Open.ModuleInverseImageCoherence

/-! # The original native module exchange and its horizontal unit normalization -/

@[expose] public noncomputable section

open CategoryTheory

universe u

namespace AlgebraicGeometry.Scheme.EtaleCohomology

open Coefficients

variable (Λ : Type (u + 1)) [Ring Λ]

/-- The inverse native composition comparison has the inverse original mate. -/
theorem conjugateEquiv_moduleInverseImageCompIso_inv {X S T : Scheme.{u}}
    (f : S ⟶ X) (g : T ⟶ S) :
    conjugateEquiv (moduleInverseImageAdjunction (g ≫ f) Λ)
      ((moduleInverseImageAdjunction f Λ).comp (moduleInverseImageAdjunction g Λ))
      (moduleInverseImageCompIso Λ f g).inv = (moduleDirectImageCompIso Λ f g).hom := by
  apply (cancel_epi (moduleDirectImageCompIso Λ f g).inv).1
  rw [← conjugateEquiv_moduleInverseImageCompIso_hom Λ f g, conjugateEquiv_comp,
    Iso.inv_hom_id, conjugateEquiv_id, conjugateEquiv_moduleInverseImageCompIso_hom,
    Iso.inv_hom_id]

variable {X X' S S' : Scheme.{u}}
  (f : X ⟶ S) (f' : X' ⟶ S') (g : S' ⟶ S) (g' : X' ⟶ X)
  (h : f' ≫ g = g' ≫ f)

/-- The inverse-image square retains the original native composition comparisons. -/
def moduleInverseImageSquareIso :
    moduleInverseImage g Λ ⋙ moduleInverseImage f' Λ ≅
      moduleInverseImage f Λ ⋙ moduleInverseImage g' Λ :=
  (moduleInverseImageCompIso Λ g f').symm ≪≫
    eqToIso (congrArg (fun k : X' ⟶ S => moduleInverseImage k Λ) h) ≪≫
      moduleInverseImageCompIso Λ f g'

/-- The direct-image square retains the original native composition comparisons. -/
def moduleDirectImageSquareIso :
    moduleDirectImage g' Λ ⋙ moduleDirectImage f Λ ≅
      moduleDirectImage f' Λ ⋙ moduleDirectImage g Λ :=
  (moduleDirectImageCompIso Λ f g').symm ≪≫
    eqToIso (congrArg (fun k : X' ⟶ S => moduleDirectImage k Λ) h.symm) ≪≫
      moduleDirectImageCompIso Λ g f'

/-- The native inverse- and direct-image squares are original conjugate mates. -/
theorem conjugateEquiv_moduleInverseImageSquareIso_hom :
    conjugateEquiv ((moduleInverseImageAdjunction f Λ).comp
      (moduleInverseImageAdjunction g' Λ))
      ((moduleInverseImageAdjunction g Λ).comp (moduleInverseImageAdjunction f' Λ))
      (moduleInverseImageSquareIso Λ f f' g g' h).hom =
        (moduleDirectImageSquareIso Λ f f' g g' h).hom := by
  let a₀ := (moduleInverseImageAdjunction f Λ).comp (moduleInverseImageAdjunction g' Λ)
  let a₁ := moduleInverseImageAdjunction (g' ≫ f) Λ
  let a₂ := moduleInverseImageAdjunction (f' ≫ g) Λ
  let a₃ := (moduleInverseImageAdjunction g Λ).comp (moduleInverseImageAdjunction f' Λ)
  change conjugateEquiv a₀ a₃ _ = _
  simp only [moduleInverseImageSquareIso, Iso.trans_hom, Iso.symm_hom, eqToIso.hom]
  rw [← conjugateEquiv_comp a₀ a₂ a₃, ← conjugateEquiv_comp a₀ a₁ a₂,
    conjugateEquiv_moduleInverseImageCompIso_hom,
    conjugateEquiv_moduleInverseImage_eqToHom Λ h,
    conjugateEquiv_moduleInverseImageCompIso_inv]
  simp only [moduleDirectImageSquareIso, Iso.trans_hom, Iso.symm_hom,
    eqToIso.hom, Category.assoc]

/-- The actual underived native module exchange is the mate of the inverse-image square. -/
def moduleBaseChangeMap :
    moduleDirectImage f Λ ⋙ moduleInverseImage g Λ ⟶
      moduleInverseImage g' Λ ⋙ moduleDirectImage f' Λ :=
  (mateEquiv (moduleInverseImageAdjunction f Λ) (moduleInverseImageAdjunction f' Λ)
    (TwoSquare.mk _ _ _ _ (moduleInverseImageSquareIso Λ f f' g g' h).hom)).natTrans

/-- The original native exchange has the original horizontal direct-image square as mate. -/
theorem mate_moduleBaseChangeMap :
    (mateEquiv (moduleInverseImageAdjunction g' Λ) (moduleInverseImageAdjunction g Λ)
      (TwoSquare.mk _ _ _ _ (moduleBaseChangeMap Λ f f' g g' h))).natTrans =
        (moduleDirectImageSquareIso Λ f f' g g' h).hom := by
  exact (iterated_mateEquiv_conjugateEquiv
    (moduleInverseImageAdjunction f Λ) (moduleInverseImageAdjunction f' Λ)
    (moduleInverseImageAdjunction g Λ) (moduleInverseImageAdjunction g' Λ)
    (TwoSquare.mk _ _ _ _ (moduleInverseImageSquareIso Λ f f' g g' h).hom)).trans
      (conjugateEquiv_moduleInverseImageSquareIso_hom Λ f f' g g' h)

/-- A native exchange has the original unit equation for its horizontal mate. -/
theorem moduleExchange_mate_unit
    (β : moduleDirectImage f Λ ⋙ moduleInverseImage g Λ ⟶
      moduleInverseImage g' Λ ⋙ moduleDirectImage f' Λ) (M : ModuleSheaf X Λ) :
    (moduleDirectImage f Λ).map ((moduleInverseImageAdjunction g' Λ).unit.app M) ≫
      ((mateEquiv (moduleInverseImageAdjunction g' Λ) (moduleInverseImageAdjunction g Λ)
        (TwoSquare.mk _ _ _ _ β)).natTrans).app
          ((moduleInverseImage g' Λ).obj M) =
    (moduleInverseImageAdjunction g Λ).unit.app ((moduleDirectImage f Λ).obj M) ≫
      (moduleDirectImage g Λ).map (β.app M) :=
  unit_mateEquiv (moduleInverseImageAdjunction g' Λ) (moduleInverseImageAdjunction g Λ)
    (TwoSquare.mk _ _ _ _ β) M

/-- The actual native exchange satisfies the original horizontal adjunction-unit equation. -/
@[reassoc]
theorem moduleBaseChangeMap_horizontal_unit (M : ModuleSheaf X Λ) :
    (moduleDirectImage f Λ).map ((moduleInverseImageAdjunction g' Λ).unit.app M) ≫
        (moduleDirectImageSquareIso Λ f f' g g' h).hom.app
          ((moduleInverseImage g' Λ).obj M) =
      (moduleInverseImageAdjunction g Λ).unit.app ((moduleDirectImage f Λ).obj M) ≫
        (moduleDirectImage g Λ).map ((moduleBaseChangeMap Λ f f' g g' h).app M) := by
  have hc := congrArg (fun α =>
    (moduleDirectImage f Λ).map ((moduleInverseImageAdjunction g' Λ).unit.app M) ≫
      α.app ((moduleInverseImage g' Λ).obj M))
    (mate_moduleBaseChangeMap Λ f f' g g' h)
  exact hc.symm.trans (moduleExchange_mate_unit Λ f f' g g'
    (moduleBaseChangeMap Λ f f' g g' h) M)

end AlgebraicGeometry.Scheme.EtaleCohomology
