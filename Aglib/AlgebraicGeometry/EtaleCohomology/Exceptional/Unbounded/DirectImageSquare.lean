/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import
  Aglib.AlgebraicGeometry.EtaleCohomology.Exceptional.Unbounded.InverseImageSquareComparison
public import Aglib.AlgebraicGeometry.EtaleCohomology.Exceptional.Unbounded.StructuralCoherence

/-!
# Original unbounded direct-image squares and the second exchange mate

The direct-image square uses the original structural compositors and the
literal equality of scheme morphisms. It is conjugate to the actual localized
inverse-image square. Taking the second mate of the original unbounded
exchange gives this same direct-image square. All four models are retained;
no properness, base-change invertibility or dimension bound is assumed.
-/

@[expose] public noncomputable section

open CategoryTheory

namespace AlgebraicGeometry.Scheme.EtaleCohomology

open Coefficients

universe u wX wS wX' wS'

variable (Λ : Type (u + 1)) [Ring Λ]

/-- The inverse original localized compositor has the forward original
unbounded direct-image compositor as its conjugate. -/
theorem conjugateEquiv_moduleUnboundedDerivedInverseImageCompIso_inv
    {X S T : Scheme.{u}} (f : S ⟶ X) (g : T ⟶ S)
    [HasDerivedCategory.{wX} (ModuleSheaf X Λ)]
    [HasDerivedCategory.{wS} (ModuleSheaf S Λ)]
    [HasDerivedCategory.{wX'} (ModuleSheaf T Λ)] :
    conjugateEquiv (moduleUnboundedDerivedAdjunction Λ (g ≫ f))
      ((moduleUnboundedDerivedAdjunction Λ f).comp (moduleUnboundedDerivedAdjunction Λ g))
      (moduleUnboundedDerivedInverseImageCompIso Λ f g).inv =
      (moduleUnboundedDerivedDirectImageCompIso Λ f g).hom := rfl

variable {X X' S S' : Scheme.{u}}
  (f : X ⟶ S) (f' : X' ⟶ S') (g : S' ⟶ S) (g' : X' ⟶ X)
  (h : f' ≫ g = g' ≫ f)
  [HasDerivedCategory.{wX} (ModuleSheaf X Λ)]
  [HasDerivedCategory.{wS} (ModuleSheaf S Λ)]
  [HasDerivedCategory.{wX'} (ModuleSheaf X' Λ)]
  [HasDerivedCategory.{wS'} (ModuleSheaf S' Λ)]

/-- The structural square of the same installed unbounded direct-image functors. -/
def moduleUnboundedDerivedDirectImageSquareIso :
    moduleUnboundedDerivedDirectImage Λ g' ⋙ moduleUnboundedDerivedDirectImage Λ f ≅
      moduleUnboundedDerivedDirectImage Λ f' ⋙ moduleUnboundedDerivedDirectImage Λ g :=
  (moduleUnboundedDerivedDirectImageCompIso Λ f g').symm ≪≫
    eqToIso (congrArg (fun k : X' ⟶ S => moduleUnboundedDerivedDirectImage Λ k) h.symm) ≪≫
      moduleUnboundedDerivedDirectImageCompIso Λ g f'

/-- The actual localized inverse-image square and the original structural
direct-image square are conjugate under the installed unbounded adjunctions. -/
theorem conjugateEquiv_moduleUnboundedDerivedInverseImageSquareIso_hom :
    conjugateEquiv
      ((moduleUnboundedDerivedAdjunction Λ f).comp (moduleUnboundedDerivedAdjunction Λ g'))
      ((moduleUnboundedDerivedAdjunction Λ g).comp (moduleUnboundedDerivedAdjunction Λ f'))
      (moduleUnboundedDerivedInverseImageSquareIso Λ f f' g g' h).hom =
      (moduleUnboundedDerivedDirectImageSquareIso Λ f f' g g' h).hom := by
  let a₀ := (moduleUnboundedDerivedAdjunction Λ f).comp (moduleUnboundedDerivedAdjunction Λ g')
  let a₁ := moduleUnboundedDerivedAdjunction Λ (g' ≫ f)
  let a₂ := moduleUnboundedDerivedAdjunction Λ (f' ≫ g)
  let a₃ := (moduleUnboundedDerivedAdjunction Λ g).comp (moduleUnboundedDerivedAdjunction Λ f')
  change conjugateEquiv a₀ a₃ _ = _
  rw [moduleUnboundedDerivedInverseImageSquareIso_eq_comp]
  simp only [Iso.trans_hom, Iso.symm_hom, eqToIso.hom]
  rw [← conjugateEquiv_comp a₀ a₂ a₃, ← conjugateEquiv_comp a₀ a₁ a₂,
    conjugateEquiv_moduleUnboundedDerivedInverseImageCompIso_hom,
    conjugateEquiv_moduleUnboundedDerivedInverseImage_eqToHom Λ h,
    conjugateEquiv_moduleUnboundedDerivedInverseImageCompIso_inv]
  simp only [moduleUnboundedDerivedDirectImageSquareIso, Iso.trans_hom, Iso.symm_hom,
    eqToIso.hom, Category.assoc]

/-- The second mate of the same original unbounded exchange is the original
direct-image square, not an unrelated isomorphism between its endpoints. -/
theorem mate_moduleUnboundedDerivedBaseChangeMap :
    (mateEquiv (moduleUnboundedDerivedAdjunction Λ g') (moduleUnboundedDerivedAdjunction Λ g)
      (TwoSquare.mk _ _ _ _ (moduleUnboundedDerivedBaseChangeMap Λ f f' g g' h))).natTrans =
      (moduleUnboundedDerivedDirectImageSquareIso Λ f f' g g' h).hom :=
  (iterated_mateEquiv_conjugateEquiv
    (moduleUnboundedDerivedAdjunction Λ f) (moduleUnboundedDerivedAdjunction Λ f')
    (moduleUnboundedDerivedAdjunction Λ g) (moduleUnboundedDerivedAdjunction Λ g')
    (TwoSquare.mk _ _ _ _
      (moduleUnboundedDerivedInverseImageSquareIso Λ f f' g g' h).hom)).trans
      (conjugateEquiv_moduleUnboundedDerivedInverseImageSquareIso_hom Λ f f' g g' h)

end AlgebraicGeometry.Scheme.EtaleCohomology
