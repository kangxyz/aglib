/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Cohomology.BaseChange.HigherDirectImage.Nonflat.Affine

/-! # Equality transport of the original affine nonflat comparison

Equality of the geometric and scalar morphisms transports the actual affine
comparison through the original module pullback and pushforward comparisons.
-/

@[expose] public section

noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

open CategoryTheory AlgebraicGeometry Opposite

namespace AlgebraicGeometry.Scheme.Modules

/-- Equal geometric and scalar maps retain the same actual affine comparison, with the
original coefficient arrow transported by the native direct-image equality comparison. -/
theorem higherDirectImageAffineMap_congr
    {R S : CommRingCat.{u}} {X Y : Scheme.{u}}
    (p p' : Y ⟶ X) (b : Y ⟶ Spec S) (f : X ⟶ Spec R) (σ σ' : R ⟶ S)
    [QuasiCompact f] [QuasiSeparated f] [QuasiCompact b] [QuasiSeparated b]
    (w : p ≫ f = b ≫ Spec.map σ) (w' : p' ≫ f = b ≫ Spec.map σ')
    {M : X.Modules} {N : Y.Modules} [M.IsQuasicoherent] [N.IsQuasicoherent]
    (ψ : M ⟶ (pushforward p).obj N) (ψ' : M ⟶ (pushforward p').obj N)
    (hp : p = p') (hσ : σ = σ')
    (hψ : ψ ≫ (pushforwardCongr hp).hom.app N = ψ') (n : ℕ) :
    (pullbackCongr (congrArg Spec.map hσ)).hom.app
        (((pushforward f).rightDerived n).obj M) ≫
      higherDirectImageAffineMap p' b f σ' w' ψ' n =
        higherDirectImageAffineMap p b f σ w ψ n := by
  subst p'
  subst σ'
  have hi : (pushforwardCongr (rfl : p = p)).hom.app N = 𝟙 _ := by
    apply Scheme.Modules.hom_ext
    intro O
    rw [pushforwardCongr_hom_app_app]
    change N.presheaf.map (𝟙 (op (p ⁻¹ᵁ O))) = 𝟙 _
    exact N.presheaf.map_id _
  rw [hi, Category.comp_id] at hψ
  subst ψ'
  simp [pullbackCongr]

end AlgebraicGeometry.Scheme.Modules
