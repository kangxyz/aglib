/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.Algebra.Category.ModuleCat.Differentials.BaseChange
public import Aglib.AlgebraicGeometry.Modules.Differentials.Relative.AffineArrowComparison
public import Aglib.AlgebraicGeometry.Modules.Differentials.Relative.Coefficient


/-!
# Actual affine coefficient coordinates on arbitrary ordinary differentials

The established arrow equality supplies values on every original ordinary
differential vector, including the original integral basis vectors. No new
choice of generic coordinate or differential basis is made.
-/

@[expose] public noncomputable section

open CategoryTheory Opposite TensorProduct
open AlgebraicGeometry.Scheme.Modules AlgebraicGeometry.Scheme.Modules.Differentials

universe u


open CommRingCat.KaehlerDifferential

namespace AlgebraicGeometry.Scheme.Modules.Differentials

/-- The original geometric coefficient on every ordinary differential vector,
expressed through its original affine source and target comparisons. -/
theorem affineCoefficient_apply {Λ A B : CommRingCat.{u}} (α : Λ ⟶ A) (σ : A ⟶ B)
    (v : CommRingCat.KaehlerDifferential α) :
    letI := σ.hom.toAlgebra
    (relativeDifferentialAffineIso (α ≫ σ)).hom.val.app (op ⊤)
      ((relativeDifferentialCongrIso (Spec.map σ ≫ Spec.map α)
        (Spec.map_comp α σ).symm).hom.val.app (op ⊤)
        ((differentialCoefficient (Spec.map α) (Spec.map σ)).val.app (op ⊤)
          ((relativeDifferentialAffineIso α).inv.val.app (op ⊤)
            (tilde.toOpen (CommRingCat.KaehlerDifferential α) ⊤ v)))) =
    tilde.toOpen (CommRingCat.KaehlerDifferential (α ≫ σ)) ⊤
      (affineDifferentialLinearMap α σ ((1 : B) ⊗ₜ[A] v)) := by
  let := σ.hom.toAlgebra
  exact ConcreteCategory.congr_hom (affineCoefficient_scalarAdjoint α σ) v

end AlgebraicGeometry.Scheme.Modules.Differentials
