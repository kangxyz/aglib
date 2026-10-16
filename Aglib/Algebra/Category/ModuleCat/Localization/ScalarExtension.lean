/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings
public import Mathlib.RingTheory.Localization.BaseChange

/-!
# The original scalar-extension adjunction unit at a localization

When the target ring is a localization through the specified ring map,
the native extension/restriction adjunction unit is a module-localization
map. Composing that original unit with an isomorphism remains localizing.
Thus an original restricted coefficient map whose native scalar mate is
invertible is itself the original localization map.
-/

@[expose] public section

noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory
open scoped TensorProduct ChangeOfRings

namespace ModuleCat

universe r s m

variable {R : Type r} {S : Type s} [CommRing R] [CommRing S]
  (T : Submonoid R) (σ : R →+* S)
  (hσ : letI := σ.toAlgebra; IsLocalization T S)

include hσ in
/-- The original native scalar-extension adjunction unit localizes at the specified submonoid. -/
theorem extendRestrictScalarsAdj_unit_isLocalizedModule (M : ModuleCat.{max m s} R) :
    IsLocalizedModule T ((extendRestrictScalarsAdj.{m} σ).unit.app M).hom := by
  let : Algebra R S := σ.toAlgebra
  let : IsLocalization T S := hσ
  let N : ModuleCat.{max m s} R := ModuleCat.of R (S ⊗[R] M)
  let e : N ≅ (restrictScalars σ).obj ((extendScalars σ).obj M) := by
    refine isoMk (AddEquiv.refl _).toAddCommGrpIso ?_
    intro a
    ext x
    change S ⊗[R] M at x
    change σ a • x = a • x
    exact IsScalarTower.algebraMap_smul S a x
  let ℓ : M →ₗ[R] S ⊗[R] M := TensorProduct.mk R S M 1
  let : IsLocalizedModule T ℓ := inferInstance
  have he : ((extendRestrictScalarsAdj.{m} σ).unit.app M).hom =
      e.toLinearEquiv.toLinearMap.comp ℓ := by
    ext x
    rfl
  rw [he]
  exact IsLocalizedModule.of_linearEquiv T ℓ e.toLinearEquiv

include hσ in
/-- The original adjunction mate of an invertible scalar-extension map is a localization map. -/
theorem isLocalizedModule_homEquiv_of_isIso
    {M : ModuleCat.{max m s} R} {N : ModuleCat.{max m s} S}
    (φ : (extendScalars σ).obj M ⟶ N) [IsIso φ] :
    IsLocalizedModule T (((extendRestrictScalarsAdj.{m} σ).homEquiv M N) φ).hom := by
  let : IsLocalizedModule T ((extendRestrictScalarsAdj.{m} σ).unit.app M).hom :=
    extendRestrictScalarsAdj_unit_isLocalizedModule T σ hσ M
  rw [Adjunction.homEquiv_apply]
  exact IsLocalizedModule.of_linearEquiv T
    ((extendRestrictScalarsAdj.{m} σ).unit.app M).hom
    (asIso ((restrictScalars σ).map φ)).toLinearEquiv

include hσ in
/-- Invertibility of the native scalar mate makes the original restricted map localizing. -/
theorem isLocalizedModule_of_isIso_adjoint
    {M : ModuleCat.{max m s} R} {N : ModuleCat.{max m s} S}
    (ψ : M ⟶ (restrictScalars σ).obj N)
    [IsIso (((extendRestrictScalarsAdj.{m} σ).homEquiv M N).symm ψ)] :
    IsLocalizedModule T ψ.hom := by
  have h := isLocalizedModule_homEquiv_of_isIso T σ hσ
    (((extendRestrictScalarsAdj.{m} σ).homEquiv M N).symm ψ)
  simpa only [Equiv.apply_symm_apply] using h

end ModuleCat
