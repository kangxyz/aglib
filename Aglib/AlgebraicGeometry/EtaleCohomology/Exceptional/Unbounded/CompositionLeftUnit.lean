/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import
  Aglib.AlgebraicGeometry.EtaleCohomology.Exceptional.Unbounded.ChosenLeftUnitContraction
public import
  Aglib.AlgebraicGeometry.EtaleCohomology.Exceptional.Unbounded.ChosenIdentityNormalization

/-! # The left-unit law for the original choice-independent exceptional compositor -/

@[expose] public noncomputable section
open CategoryTheory
namespace AlgebraicGeometry.Scheme.EtaleCohomology
open Coefficients
universe u wX wY wA wB wD
variable {X Y : Scheme.{u}} (f : X ⟶ Y) [QuasiCompact f]
  [CompactSpace X] [QuasiSeparatedSpace X] [CompactSpace Y] [QuasiSeparatedSpace Y]
  [IsSeparated f] [LocallyOfFiniteType f]
  (Λ : Type (u + 1)) [Ring Λ]
  [hX : HasDerivedCategory.{wX} (ModuleSheaf X Λ)]
  [hY : HasDerivedCategory.{wY} (ModuleSheaf Y Λ)]
  [firstModels : ∀ E : Hom.DenseCompactification (𝟙 X),
    HasDerivedCategory.{wA} (ModuleSheaf E.Xbar Λ)]
  [targetModels : ∀ E : Hom.DenseCompactification f,
    HasDerivedCategory.{wD} (ModuleSheaf E.Xbar Λ)]
  [compositeModels : ∀ E : Hom.DenseCompactification ((𝟙 X) ≫ f),
    HasDerivedCategory.{wB} (ModuleSheaf E.Xbar Λ)]

variable (N : ℕ) (hN : 0 < N) (hΛ : N • (1 : Λ) = 0)

/-- The actual chosen compositor has the original epsilon as its left unit.
The target is normalized only by original arrow equality and original model-family transport. -/
theorem moduleExceptionalDirectImageUnboundedCompIso_id_comp :
    moduleExceptionalDirectImageUnboundedCompIso (𝟙 X) f Λ N hN hΛ ≪≫
      moduleExceptionalDirectImageUnboundedCongr Λ hX hY (Category.id_comp f)
        compositeModels targetModels N hN hΛ =
    Functor.isoWhiskerRight (moduleExceptionalDirectImageUnboundedIdIso X Λ N hN hΛ)
        (moduleExceptionalDirectImageUnbounded f Λ) ≪≫
      Functor.leftUnitor (moduleExceptionalDirectImageUnbounded f Λ) := by
  have h := moduleExceptionalUnboundedLeftUnitContraction f Λ (moduleExceptionalCompactification f)
    N hN hΛ
  have hε := congrArg
    (fun e => Functor.isoWhiskerRight e (moduleExceptionalDirectImageUnbounded f Λ) ≪≫
      Functor.leftUnitor (moduleExceptionalDirectImageUnbounded f Λ))
    (moduleExceptionalDirectImageUnboundedIdIso_singleModel X Λ hX N hN hΛ)
  exact h.trans hε

end AlgebraicGeometry.Scheme.EtaleCohomology
