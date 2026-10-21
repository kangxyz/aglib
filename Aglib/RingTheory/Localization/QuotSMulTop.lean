/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Mathlib.Algebra.Module.LocalizedModule.Submodule
public import Mathlib.RingTheory.QuotSMulTop

/-! The actual scalar quotient of a localized module, with its canonical localization map. -/

@[expose] public section

noncomputable section

open scoped Pointwise

variable {R Rₛ M Mₛ : Type*} [CommRing R] [CommRing Rₛ] [Algebra R Rₛ]
  [AddCommGroup M] [Module R M] [AddCommGroup Mₛ] [Module R Mₛ] [Module Rₛ Mₛ]
  [IsScalarTower R Rₛ Mₛ] (S : Submonoid R) [IsLocalization S Rₛ]
  (j : M →ₗ[R] Mₛ) [IsLocalizedModule S j] (a : R)

namespace Submodule

/-- Localization carries the scalar multiple of the whole module to the corresponding
scalar multiple over the localized ring. -/
theorem localized'_pointwise_smul_top :
    (a • (⊤ : Submodule R M)).localized' Rₛ S j =
      algebraMap R Rₛ a • (⊤ : Submodule Rₛ Mₛ) := by
  rw [← ideal_span_singleton_smul, localized'_smul, localized'_top, localized'_span]
  simp only [Algebra.linearMap_apply, Set.image_singleton, ideal_span_singleton_smul]

end Submodule

namespace QuotSMulTop

/-- The canonical map from `M/aM` to the scalar quotient of the specified localization. -/
def localizationMap : QuotSMulTop a M →ₗ[R] QuotSMulTop (algebraMap R Rₛ a) Mₛ :=
  let e := Submodule.quotEquivOfEq _ _ (Submodule.localized'_pointwise_smul_top S j a)
  (e.restrictScalars R).toLinearMap.comp
    ((a • (⊤ : Submodule R M)).toLocalizedQuotient' Rₛ S j)

@[simp]
theorem localizationMap_mk (x : M) :
    localizationMap S j a (Submodule.Quotient.mk x) =
      (Submodule.Quotient.mk (j x) : QuotSMulTop (algebraMap R Rₛ a) Mₛ) := rfl

/-- The canonical scalar-quotient map is itself a module localization. -/
instance isLocalizedModule_localizationMap :
    IsLocalizedModule S (localizationMap (Rₛ := Rₛ) S j a) := by
  unfold localizationMap
  infer_instance

end QuotSMulTop
