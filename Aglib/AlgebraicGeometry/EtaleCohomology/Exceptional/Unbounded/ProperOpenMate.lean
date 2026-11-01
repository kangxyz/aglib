/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.Exceptional.Unbounded.LowerShriekBaseChangeMate
public import Aglib.CategoryTheory.Adjunction.ConjugacyOfInverseMate

/-! # The original unbounded proper/open mixed mate and its actual conjugacy -/
@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry.Scheme.EtaleCohomology
open Coefficients
universe u wV wU wY wX
variable {V U Y X : Scheme.{u}} (g : V ⟶ U) (i : V ⟶ Y) (j : U ⟶ X) (f : Y ⟶ X)
  [Etale i] [Etale j] (h : IsPullback g i j f) (Λ : Type (u + 1)) [Ring Λ]
  [HasDerivedCategory.{wV} (ModuleSheaf V Λ)]
  [HasDerivedCategory.{wU} (ModuleSheaf U Λ)]
  [HasDerivedCategory.{wY} (ModuleSheaf Y Λ)]
  [HasDerivedCategory.{wX} (ModuleSheaf X Λ)]

/-- The genuine etale exchange, now regarded as an iso on all unbounded objects. -/
def moduleUnboundedCartesianExchangeIso :
    moduleUnboundedDerivedDirectImage Λ f ⋙ moduleUnboundedDerivedInverseImage Λ j ≅
      moduleUnboundedDerivedInverseImage Λ i ⋙ moduleUnboundedDerivedDirectImage Λ g := by
  letI := moduleUnboundedDerivedBaseChange_isIso_of_etale g i j f h Λ
  exact asIso (moduleUnboundedDerivedBaseChangeMap Λ f g j i h.w)

/-- The forward original open square has the inverse original etale exchange as conjugate. -/
theorem conjugateEquiv_moduleUnboundedLowerShriekCartesianBaseChangeIso_hom :
    conjugateEquiv
      ((moduleUnboundedDerivedAdjunction Λ g).comp
        (moduleUnboundedDerivedLowerShriekAdjunction i Λ))
      ((moduleUnboundedDerivedLowerShriekAdjunction j Λ).comp
        (moduleUnboundedDerivedAdjunction Λ f))
      (moduleUnboundedDerivedLowerShriekCartesianBaseChangeIso g i j f h Λ).hom =
      (moduleUnboundedCartesianExchangeIso g i j f h Λ).inv :=
  conjugateEquiv_eq_inv_of_inverse_mate
    (moduleUnboundedDerivedLowerShriekAdjunction j Λ)
    (moduleUnboundedDerivedLowerShriekAdjunction i Λ)
    (moduleUnboundedDerivedAdjunction Λ g) (moduleUnboundedDerivedAdjunction Λ f)
    (moduleUnboundedDerivedLowerShriekCartesianBaseChangeIso g i j f h Λ)
    (moduleUnboundedCartesianExchangeIso g i j f h Λ)
    (moduleUnboundedDerivedInverseImageSquareIso Λ f g j i h.w).hom
    (moduleUnboundedDerivedLowerShriekCartesianBaseChangeIso_inv_mate g i j f h Λ) rfl

/-- The literal mixed mate, without properness or torsion assumptions. -/
def moduleUnboundedProperOpenMate :
    moduleUnboundedDerivedDirectImage Λ g ⋙ moduleUnboundedDerivedLowerShriek j Λ ⟶
      moduleUnboundedDerivedLowerShriek i Λ ⋙ moduleUnboundedDerivedDirectImage Λ f :=
  (mateEquiv (moduleUnboundedDerivedAdjunction Λ g) (moduleUnboundedDerivedAdjunction Λ f)
    (TwoSquare.mk _ _ _ _
      (moduleUnboundedDerivedLowerShriekCartesianBaseChangeIso g i j f h Λ).hom)).natTrans
end AlgebraicGeometry.Scheme.EtaleCohomology
