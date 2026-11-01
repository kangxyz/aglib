/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.CategoryTheory.Functor.OpenCompositionCoherence
public import Aglib.AlgebraicGeometry.EtaleCohomology.Exceptional.Derived.LowerShriekCompositionCoherence

/-! # Contraction of original open compositors along actual arrow equalities -/

@[expose] public noncomputable section
open CategoryTheory
namespace AlgebraicGeometry.Scheme.EtaleCohomology
open Coefficients
universe u wX wA wB wC
variable (Λ : Type (u + 1)) [Ring Λ]
  {X A B C : Scheme.{u}}
  [HasDerivedCategory.{wX} (ModuleSheaf X Λ)]
  [HasDerivedCategory.{wA} (ModuleSheaf A Λ)]
  [HasDerivedCategory.{wB} (ModuleSheaf B Λ)]
  [HasDerivedCategory.{wC} (ModuleSheaf C Λ)]

/-- The original open compositor followed by its specified arrow equality. -/
def moduleDerivedLowerShriekOverIso (k : X ⟶ A) (m : A ⟶ B) (j : X ⟶ B)
    [Etale k] [Etale m] [Etale j] (e : k ≫ m = j) :
    moduleDerivedLowerShriek k Λ ⋙ moduleDerivedLowerShriek m Λ ≅
      moduleDerivedLowerShriek j Λ :=
  (moduleDerivedLowerShriekCompIso Λ m k).symm ≪≫
    eqToIso (moduleDerivedLowerShriek_congr Λ e)

/-- The two original contractions of three opens agree, with actual equality transports. -/
theorem moduleDerivedLowerShriekOverIso_assoc
    (k : X ⟶ A) (m : A ⟶ B) (n : B ⟶ C)
    (j : X ⟶ B) (t : X ⟶ C)
    [Etale k] [Etale m] [Etale n] [Etale j] [Etale t]
    (e : k ≫ m = j) (e' : j ≫ n = t) :
    OpenCompositionEquation
      (moduleDerivedLowerShriekOverIso Λ k m j e)
      (moduleDerivedLowerShriekOverIso Λ j n t e')
      (moduleDerivedLowerShriekOverIso Λ k (m ≫ n) t
        ((Category.assoc k m n).symm.trans ((congrArg (fun l => l ≫ n) e).trans e')))
      (moduleDerivedLowerShriekCompIso Λ n m).symm := by
  subst j
  subst t
  apply openCompositionEquation_of_associates
    (eqToIso (moduleDerivedLowerShriek_congr Λ (Category.assoc k m n).symm))
    (moduleDerivedLowerShriekCompIso Λ (m ≫ n) k)
    (moduleDerivedLowerShriekCompIso Λ n m)
    (moduleDerivedLowerShriekCompIso Λ n (k ≫ m))
    (moduleDerivedLowerShriekCompIso Λ m k)
    (moduleDerivedLowerShriekCompIso_assoc Λ n m k)
  · simp only [moduleDerivedLowerShriekOverIso, eqToIso_refl, Iso.trans_refl]
  · simp only [moduleDerivedLowerShriekOverIso, eqToIso_refl, Iso.trans_refl]
  · rfl
  · rfl

end AlgebraicGeometry.Scheme.EtaleCohomology
