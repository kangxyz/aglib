/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import
  Aglib.AlgebraicGeometry.EtaleCohomology.Exceptional.Derived.CartesianExchangeComparison

/-! # The right mate of the original Cartesian exchange is the original image square

All four derived models are retained. The square is assembled from the native
direct-image compositors and the literal commuting-arrow equality.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry.Scheme.EtaleCohomology
open Coefficients
universe u wX wS wX' wS'
variable (Λ : Type (u + 1)) [Ring Λ]

/-- Native inverse-image equality transport has its original direct-image mate. -/
theorem conjugateEquiv_moduleDerivedInverseImage_eqToHom
    {X S : Scheme.{u}} {f g : X ⟶ S} (h : f = g)
    [HasDerivedCategory.{wX} (ModuleSheaf X Λ)]
    [HasDerivedCategory.{wS} (ModuleSheaf S Λ)] :
    conjugateEquiv (moduleDerivedAdjunction Λ g) (moduleDerivedAdjunction Λ f)
      (eqToHom (congrArg (fun k => moduleDerivedInverseImage Λ k) h)) =
      eqToHom (congrArg (fun k => moduleDerivedDirectImage Λ k) h.symm) := by
  cases h
  exact conjugateEquiv_id _

/-- The inverse original compositor has the forward original direct-image mate. -/
theorem conjugateEquiv_moduleDerivedInverseImageCompIso_inv
    {X S T : Scheme.{u}} (f : S ⟶ X) (g : T ⟶ S)
    [HasDerivedCategory.{wX} (ModuleSheaf X Λ)]
    [HasDerivedCategory.{wS} (ModuleSheaf S Λ)]
    [HasDerivedCategory.{wX'} (ModuleSheaf T Λ)] :
    conjugateEquiv (moduleDerivedAdjunction Λ (g ≫ f))
      ((moduleDerivedAdjunction Λ f).comp (moduleDerivedAdjunction Λ g))
      (moduleDerivedInverseImageCompIso Λ f g).inv =
      (moduleDerivedDirectImageCompIso Λ f g).hom := by
  apply (cancel_epi (moduleDerivedDirectImageCompIso Λ f g).inv).mp
  rw [← conjugateEquiv_moduleDerivedInverseImageCompIso_hom Λ f g,
    conjugateEquiv_comp, Iso.inv_hom_id, conjugateEquiv_id,
    conjugateEquiv_moduleDerivedInverseImageCompIso_hom, Iso.inv_hom_id]

variable {X X' S S' : Scheme.{u}}
  (f : X ⟶ S) (f' : X' ⟶ S') (g : S' ⟶ S) (g' : X' ⟶ X)
  (h : f' ≫ g = g' ≫ f)
  [HasDerivedCategory.{wX} (ModuleSheaf X Λ)]
  [HasDerivedCategory.{wS} (ModuleSheaf S Λ)]
  [HasDerivedCategory.{wX'} (ModuleSheaf X' Λ)]
  [HasDerivedCategory.{wS'} (ModuleSheaf S' Λ)]

/-- The original structural square of installed direct-image functors. -/
def moduleDerivedDirectImageSquareIso :
    moduleDerivedDirectImage Λ g' ⋙ moduleDerivedDirectImage Λ f ≅
      moduleDerivedDirectImage Λ f' ⋙ moduleDerivedDirectImage Λ g :=
  (moduleDerivedDirectImageCompIso Λ f g').symm ≪≫
    eqToIso (congrArg (fun k : X' ⟶ S => moduleDerivedDirectImage Λ k) h.symm) ≪≫
      moduleDerivedDirectImageCompIso Λ g f'

/-- The actual inverse- and direct-image squares are conjugate under the original adjunctions. -/
theorem conjugateEquiv_moduleDerivedInverseImageSquareIso_hom :
    conjugateEquiv ((moduleDerivedAdjunction Λ f).comp (moduleDerivedAdjunction Λ g'))
      ((moduleDerivedAdjunction Λ g).comp (moduleDerivedAdjunction Λ f'))
      (moduleDerivedInverseImageSquareIso Λ f f' g g' h).hom =
      (moduleDerivedDirectImageSquareIso Λ f f' g g' h).hom := by
  let a₀ := (moduleDerivedAdjunction Λ f).comp (moduleDerivedAdjunction Λ g')
  let a₁ := moduleDerivedAdjunction Λ (g' ≫ f)
  let a₂ := moduleDerivedAdjunction Λ (f' ≫ g)
  let a₃ := (moduleDerivedAdjunction Λ g).comp (moduleDerivedAdjunction Λ f')
  change conjugateEquiv a₀ a₃ _ = _
  simp only [moduleDerivedInverseImageSquareIso, Iso.trans_hom, Iso.symm_hom, eqToIso.hom]
  rw [← conjugateEquiv_comp a₀ a₂ a₃, ← conjugateEquiv_comp a₀ a₁ a₂,
    conjugateEquiv_moduleDerivedInverseImageCompIso_hom,
    conjugateEquiv_moduleDerivedInverseImage_eqToHom Λ h,
    conjugateEquiv_moduleDerivedInverseImageCompIso_inv]
  simp only [moduleDerivedDirectImageSquareIso, Iso.trans_hom, Iso.symm_hom,
    eqToIso.hom, Category.assoc]

/-- The second mate of the actual exchange is the original structural direct-image square. -/
theorem mate_moduleDerivedBaseChangeMap :
    (mateEquiv (moduleDerivedAdjunction Λ g') (moduleDerivedAdjunction Λ g)
      (TwoSquare.mk _ _ _ _ (moduleDerivedBaseChangeMap Λ f f' g g' h))).natTrans =
      (moduleDerivedDirectImageSquareIso Λ f f' g g' h).hom :=
  (iterated_mateEquiv_conjugateEquiv
    (moduleDerivedAdjunction Λ f) (moduleDerivedAdjunction Λ f')
    (moduleDerivedAdjunction Λ g) (moduleDerivedAdjunction Λ g')
    (TwoSquare.mk _ _ _ _ (moduleDerivedInverseImageSquareIso Λ f f' g g' h).hom)).trans
      (conjugateEquiv_moduleDerivedInverseImageSquareIso_hom Λ f f' g g' h)

end AlgebraicGeometry.Scheme.EtaleCohomology
