/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.LinearAlgebra.LocalizedModule.Kernel
public import Aglib.RingTheory.Kaehler.Exterior.Map


/-!
# The original raw differential kernel over the same fraction field

The actual raw map followed by the original generic exterior map is the
source localization. Its actual localized map is the identity on the SAME
raw exterior module over the SAME field. Its original kernel is therefore
killed by every original map to a torsion-free module.
-/

@[expose] public noncomputable section

open scoped TensorProduct nonZeroDivisors

universe u v w t


open LinearMap

namespace KaehlerDifferential

variable (Λ : Type w) (R : Type u) (S : Type v) (K : Type t)
  [CommRing Λ] [CommRing R] [CommRing S] [Field K]
  [Algebra Λ R] [Algebra R S] [Algebra Λ S] [IsScalarTower Λ R S]
  [Algebra R K] [Algebra S K] [Algebra Λ K]
  [IsScalarTower R S K] [IsScalarTower Λ R K] [IsScalarTower Λ S K]
  [IsFractionRing R K] [IsFractionRing S K]

/-- The original raw map followed by its original generic map is precisely a
localization of the original scalar-extended raw source. -/
theorem mapExteriorBaseChange_generic_isLocalizedModule (n : ℕ) :
    IsLocalizedModule S⁰
      ((mapExterior Λ S K n).comp (mapExteriorBaseChange Λ R S n)) := by
  let : IsLocalizedModule R⁰ (mapExterior Λ R K n) :=
    mapExterior_isLocalizedModule Λ R K R⁰ n
  have h : (((mapExterior Λ S K n).comp (mapExteriorBaseChange Λ R S n)).restrictScalars R).comp
      (TensorProduct.mk R S (⋀[R]^n (KaehlerDifferential Λ R)) 1) =
      mapExterior Λ R K n := by
    apply LinearMap.ext
    intro ω
    change mapExterior Λ S K n
      (mapExteriorBaseChange Λ R S n ((1 : S) ⊗ₜ[R] ω)) = mapExterior Λ R K n ω
    rw [mapExteriorBaseChange_tmul, one_smul]
    exact mapExterior_tower_apply Λ R S K n ω
  apply (isLocalizedModule_iff_isBaseChange S⁰ K _).mpr
  apply (TensorProduct.isBaseChange R (⋀[R]^n (KaehlerDifferential Λ R)) S).of_comp
  rw [h]
  exact IsLocalizedModule.isBaseChange R⁰ K (mapExterior Λ R K n)

include K in
/-- Every original torsion-free-target map kills the kernel of the original
raw base-change arrow. Generic injectivity is derived, not a premise. -/
theorem mapExteriorBaseChange_ker_le
    {P : Type*} [AddCommGroup P] [Module S P] [Module.IsTorsionFree S P]
    (n : ℕ) (g : S ⊗[R] (⋀[R]^n (KaehlerDifferential Λ R)) →ₗ[S] P) :
    LinearMap.ker (mapExteriorBaseChange Λ R S n) ≤ LinearMap.ker g := by
  let lN := mapExterior Λ S K n
  let f := mapExteriorBaseChange Λ R S n
  let lM := lN.comp f
  let : IsLocalizedModule S⁰ lN := mapExterior_isLocalizedModule Λ S K S⁰ n
  let : IsLocalizedModule S⁰ lM := mapExteriorBaseChange_generic_isLocalizedModule Λ R S K n
  have hid : IsLocalizedModule.map S⁰ lM lN f = LinearMap.id := by
    apply IsLocalizedModule.ext S⁰ lM (IsLocalizedModule.map_units lN)
    exact IsLocalizedModule.map_comp S⁰ lM lN f
  have hf : Function.Injective (IsLocalizedModule.map S⁰ lM lN f) := by
    rw [hid]
    exact Function.injective_id
  exact LinearMap.ker_le_of_localizedMap_injective lM lN f hf g

end KaehlerDifferential
