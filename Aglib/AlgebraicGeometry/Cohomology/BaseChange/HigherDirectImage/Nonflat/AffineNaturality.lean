/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Cohomology.BaseChange.HigherDirectImage.Nonflat.Affine
public import Aglib.AlgebraicGeometry.Cohomology.BaseChange.HigherDirectImage.Nonflat.AffineSheaf
public import Aglib.AlgebraicGeometry.Cohomology.DirectImage.Affine.Cohomology.Naturality
public import Aglib.AlgebraicGeometry.Cohomology.Functoriality.Modules.Open

/-!
# Coefficient naturality of the native nonflat affine comparison

The original coefficient naturality of geometric cohomology and of the affine
section equivalences gives naturality of the actual small scalar mate.
-/

@[expose] public section

noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

open CategoryTheory AlgebraicGeometry
open scoped TensorProduct ChangeOfRings

namespace AlgebraicGeometry.Scheme.Modules

open Cohomology

section Coefficients

variable {R S : CommRingCat.{u}} {X Y : Scheme.{u}}
  (p : Y ⟶ X) (b : Y ⟶ Spec S) (f : X ⟶ Spec R) (σ : R ⟶ S)
  [QuasiCompact f] [QuasiSeparated f] [QuasiCompact b] [QuasiSeparated b]
  (w : p ≫ f = b ≫ Spec.map σ)
  {M M' : X.Modules} {N N' : Y.Modules}
  [M.IsQuasicoherent] [M'.IsQuasicoherent] [N.IsQuasicoherent] [N'.IsQuasicoherent]
  (ψ : M ⟶ (pushforward p).obj N) (ψ' : M' ⟶ (pushforward p).obj N')
  (μ : M ⟶ M') (ν : N ⟶ N') (h : μ ≫ ψ' = ψ ≫ (pushforward p).map ν) (n : ℕ)

include h in
/-- An actual coefficient square is preserved by the native small affine tensor comparison. -/
@[reassoc]
theorem higherDirectImageAffineSectionsTensorMap_naturality :
    (ModuleCat.extendScalars σ.hom).map
        (moduleSpecΓFunctor.map (((pushforward f).rightDerived n).map μ)) ≫
      higherDirectImageAffineSectionsTensorMap p b f σ w ψ' n =
        higherDirectImageAffineSectionsTensorMap p b f σ w ψ n ≫
          moduleSpecΓFunctor.map (((pushforward b).rightDerived n).map ν) := by
  apply ModuleCat.ExtendScalars.hom_ext
  intro x
  apply (moduleHigherDirectImageAffineSectionsLinearEquiv b N'
    (injectiveResolution N') n).injective
  change moduleHigherDirectImageAffineSectionsLinearEquiv b N' (injectiveResolution N') n
      (higherDirectImageAffineSectionsTensorMap p b f σ w ψ' n
        ((ModuleCat.extendScalars σ.hom).map
          (moduleSpecΓFunctor.map (((pushforward f).rightDerived n).map μ))
          ((1 : S) ⊗ₜ[R,σ.hom] x))) =
    moduleHigherDirectImageAffineSectionsLinearEquiv b N' (injectiveResolution N') n
      (moduleSpecΓFunctor.map (((pushforward b).rightDerived n).map ν)
        (higherDirectImageAffineSectionsTensorMap p b f σ w ψ n
          ((1 : S) ⊗ₜ[R,σ.hom] x)))
  rw [ModuleCat.ExtendScalars.map_tmul,
    higherDirectImageAffineSectionsTensorMap_one_tmul p b f σ w ψ' n,
    moduleHigherDirectImageAffineSectionsLinearEquiv_naturality b
      (injectiveResolution N) (injectiveResolution N') (v := ν) n,
    higherDirectImageAffineSectionsTensorMap_one_tmul p b f σ w ψ n,
    moduleHigherDirectImageAffineSectionsLinearEquiv_naturality f
      (injectiveResolution M) (injectiveResolution M') (v := μ) n]
  exact moduleCohomologyMapAlong_naturality p ψ ψ' μ ν h n
    (moduleHigherDirectImageAffineSectionsLinearEquiv f M (injectiveResolution M) n x)

include h in
/-- The actual nonflat affine higher-image map is natural in the original coefficient
square. All four higher-image coefficient arrows are the installed derived-functor arrows. -/
@[reassoc]
theorem higherDirectImageAffineMap_naturality :
    (pullback (Spec.map σ)).map (((pushforward f).rightDerived n).map μ) ≫
      higherDirectImageAffineMap p b f σ w ψ' n =
        higherDirectImageAffineMap p b f σ w ψ n ≫
          ((pushforward b).rightDerived n).map ν := by
  let := moduleHigherDirectImageAffine_isQuasicoherent f M n
  let := moduleHigherDirectImageAffine_isQuasicoherent f M' n
  exact Nonflat.affineMapFromTensor_naturality σ
    (((pushforward f).rightDerived n).map μ) (((pushforward b).rightDerived n).map ν)
    _ _ (higherDirectImageAffineSectionsTensorMap_naturality p b f σ w ψ ψ' μ ν h n)

end Coefficients

end AlgebraicGeometry.Scheme.Modules
