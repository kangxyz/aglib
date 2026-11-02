/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.RingTheory.Localization.Away.SaturatedChart
public import Mathlib.RingTheory.Localization.AsSubring


/-!
# The original saturated chart in the same actual fraction field

The original chart is retained as a subalgebra of the original principal
localization. Its native localization lift gives its action on the SAME
original fraction field. No replacement affine chart or generic field is
chosen, and the original base-map triangle is proved.
-/

@[expose] public noncomputable section

open scoped nonZeroDivisors

universe u v

namespace Localization.Away

variable (R : Type u) [CommRing R] [IsDomain R]
  (K : Type v) [Field K] [Algebra R K] [IsFractionRing R K]
  (I : Ideal R) (x : R) (hx : x ≠ 0)

/-- The original saturated chart inclusion followed by the original localization lift. -/
def saturatedChartFractionMap : saturatedChart R I x →ₐ[R] K :=
  (Localization.mapToFractionRing K (Submonoid.powers x) (Localization.Away x)
    (Submonoid.powers_le.mpr (mem_nonZeroDivisors_iff_ne_zero.mpr hx))).comp
      (saturatedChart R I x).val

/-- The original saturated chart acts through that literal canonical map. -/
abbrev saturatedChartFractionAlgebra : Algebra (saturatedChart R I x) K :=
  (saturatedChartFractionMap R K I x hx).toRingHom.toAlgebra

/-- The unchanged original base-map triangle. -/
theorem saturatedChartFractionAlgebra_tower :
    letI := saturatedChartFractionAlgebra R K I x hx
    IsScalarTower R (saturatedChart R I x) K := by
  let := saturatedChartFractionAlgebra R K I x hx
  apply IsScalarTower.of_algebraMap_eq
  intro r
  exact ((saturatedChartFractionMap R K I x hx).commutes r).symm

/-- Injectivity is derived from the original localization map and chart inclusion. -/
theorem saturatedChartFractionMap_injective :
    Function.Injective (saturatedChartFractionMap R K I x hx) := by
  let hU : Submonoid.powers x ≤ R⁰ :=
    Submonoid.powers_le.mpr (mem_nonZeroDivisors_iff_ne_zero.mpr hx)
  let F := Localization.mapToFractionRing K (Submonoid.powers x) (Localization.Away x) hU
  have hF : Function.Injective F := by
    apply (IsLocalization.injective_iff_map_algebraMap_eq
      (Submonoid.powers x) F.toRingHom).mpr
    intro a b
    constructor
    · exact congrArg F
    · intro hab
      exact congrArg (algebraMap R (Localization.Away x))
        ((IsFractionRing.injective R K)
          ((F.commutes a).symm.trans (hab.trans (F.commutes b))))
  exact hF.comp Subtype.val_injective

/-- The original field is proved to be the fraction field of the original chart,
with the already fixed canonical chart action. -/
theorem saturatedChart_isFractionRing :
    letI := saturatedChartFractionAlgebra R K I x hx
    IsFractionRing (saturatedChart R I x) K := by
  let := saturatedChartFractionAlgebra R K I x hx
  let := saturatedChartFractionAlgebra_tower R K I x hx
  let : FaithfulSMul (saturatedChart R I x) K :=
    (faithfulSMul_iff_algebraMap_injective (saturatedChart R I x) K).mpr
      (saturatedChartFractionMap_injective R K I x hx)
  apply IsFractionRing.of_field (saturatedChart R I x) K
  intro z
  obtain ⟨a, b, _, he⟩ := IsFractionRing.div_surjective R z
  refine ⟨algebraMap R (saturatedChart R I x) a,
    algebraMap R (saturatedChart R I x) b, ?_⟩
  exact he.symm.trans (congrArg₂ (fun p q : K => p / q)
    (IsScalarTower.algebraMap_apply R (saturatedChart R I x) K a)
    (IsScalarTower.algebraMap_apply R (saturatedChart R I x) K b))

end Localization.Away
