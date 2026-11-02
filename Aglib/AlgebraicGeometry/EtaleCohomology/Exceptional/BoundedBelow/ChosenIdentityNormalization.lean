/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import
  Aglib.AlgebraicGeometry.EtaleCohomology.Exceptional.BoundedBelow.IdentityFactorizationCoherence
public import Aglib.AlgebraicGeometry.EtaleCohomology.Exceptional.BoundedBelow.UnitModelTorsion

/-! # The single-value contraction is the original chosen exceptional epsilon -/

@[expose] public noncomputable section
open CategoryTheory
namespace AlgebraicGeometry.Scheme.EtaleCohomology
open Coefficients
universe u wX wM
variable (X : Scheme.{u}) [CompactSpace X] [QuasiSeparatedSpace X]
  (Λ : Type (u + 1)) [Ring Λ]
  [hX : HasDerivedCategory.{wX} (ModuleSheaf X Λ)]
  [models : ∀ C : Hom.DenseCompactification (𝟙 X),
    HasDerivedCategory.{wM} (ModuleSheaf C.Xbar Λ)]

/-- Independent identity-middle models give the same original chosen epsilon. -/
theorem moduleExceptionalIdentityIso_singleModel :
    moduleExceptionalSingleTorsionValueIso (𝟙 X) Λ
        (Hom.DenseCompactification.ofProper (𝟙 X)) hX ≪≫
      moduleSingleIdentityValueIso X Λ hX hX = moduleExceptionalIdentityIso X Λ := by
  apply Iso.ext
  apply NatTrans.ext
  funext K
  apply ObjectProperty.hom_ext
  let C := Hom.DenseCompactification.ofProper (𝟙 X)
  let χ := moduleExceptionalDirectImagePlusIso (𝟙 X) Λ C
  let τ := @moduleCompactificationMixedTransition X X (𝟙 X) _ Λ _ hX hX
    C C (𝟙 C) hX (models C)
  let ε₀ := moduleSingleIdentityAmbientIso X Λ hX (models C)
  let ε₁ := moduleSingleIdentityAmbientIso X Λ hX hX
  change (χ.hom.app K ≫ τ.app K) ≫ ε₁.hom.app K = χ.hom.app K ≫ ε₀.hom.app K
  have h := congrArg (fun a => χ.hom.app K ≫ a.app K)
    (moduleSingleIdentityAmbientIso_mixed X Λ hX (models C) hX)
  exact (Category.assoc _ _ _).trans h

end AlgebraicGeometry.Scheme.EtaleCohomology
