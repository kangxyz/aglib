/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.RingTheory.Extension.Presentation.FittingStopping

/-!
# Evaluated Fitting stopping with the actual generic transcendence degree

The two fraction-field towers belong to the original domain algebra. They
are never constructed from the potentially noninjective selected quotient.
The original coefficient map is faithful because its evaluation into the
target is faithful. Unit evaluation supplies noncontainment at the actual
inverse image of the target maximal ideal.
-/

@[expose] public noncomputable section

universe u v w

namespace Algebra.Presentation

variable {R B K L : Type u} {S : Type v} {σ : Type w} {ι : Type}
variable [CommRing R] [IsDomain R] [IsRegularRing R]
variable [CommRing B] [IsDomain B] [Algebra R B]
variable [Field K] [Algebra R K] [IsFractionRing R K]
variable [Field L] [Algebra B L] [IsFractionRing B L]
variable [Algebra R L] [IsScalarTower R B L]
variable [Algebra K L] [IsScalarTower R K L]
variable [CommRing S] [IsLocalRing S] [Algebra R S] [FaithfulSMul R S]
variable [Finite ι]

/-- Unit evaluation of the Fitting ideal indexed by the actual generic
transcendence degree stops at the literal evaluation prime. -/
theorem isSmoothAt_comap_maximalIdeal_of_generic_trdeg_of_map_fittingIdeal_eq_top
    (P : Presentation R B ι σ) (χ : B →ₐ[R] S) (r : ℕ)
    (hdeg : Algebra.trdeg K L = (r : Cardinal))
    (hfit : (Module.fittingIdeal B (KaehlerDifferential R B) r).map χ.toRingHom = ⊤) :
    Algebra.IsSmoothAt R ((IsLocalRing.maximalIdeal S).comap χ.toRingHom) := by
  let : FaithfulSMul R B := (faithfulSMul_iff_algebraMap_injective R B).mpr (by
    intro x y h
    apply FaithfulSMul.algebraMap_injective R S
    simpa only [χ.commutes] using congrArg χ h)
  let : Algebra.IsAlgebraic B L := IsLocalization.isAlgebraic L (nonZeroDivisors B)
  let : Algebra.IsAlgebraic R K := IsLocalization.isAlgebraic K (nonZeroDivisors R)
  have hB : Algebra.trdeg R B = Algebra.trdeg R L := by
    simpa only [trdeg_eq_zero, add_zero] using trdeg_add_eq R B (A := L)
  have hK : Algebra.trdeg K L = Algebra.trdeg R L := by
    simpa only [trdeg_eq_zero, zero_add] using trdeg_add_eq R K (A := L)
  apply P.isSmoothAt_of_fittingIdeal_kaehler_not_le r (hB.trans (hK.symm.trans hdeg))
  intro hle
  have hmap := (Ideal.map_le_iff_le_comap).mpr hle
  rw [hfit] at hmap
  exact (Ideal.IsMaximal.ne_top
    (inferInstance : (IsLocalRing.maximalIdeal S).IsMaximal)) (top_le_iff.mp hmap)


omit [Finite ι] in
/-- The finite-type stopping statement constructs its finite presentation over
its regular Noetherian coefficient ring, rather than requiring one as input. -/
theorem isSmoothAt_comap_maximalIdeal_of_generic_trdeg_of_map_fittingIdeal_eq_top_of_finiteType
    [Algebra.FiniteType R B] (χ : B →ₐ[R] S) (r : ℕ)
    (hdeg : Algebra.trdeg K L = (r : Cardinal))
    (hfit : (Module.fittingIdeal B (KaehlerDifferential R B) r).map χ.toRingHom = ⊤) :
    Algebra.IsSmoothAt R ((IsLocalRing.maximalIdeal S).comap χ.toRingHom) := by
  let : Algebra.FinitePresentation R B := Algebra.FinitePresentation.of_finiteType.mp inferInstance
  exact isSmoothAt_comap_maximalIdeal_of_generic_trdeg_of_map_fittingIdeal_eq_top
    (Presentation.ofFinitePresentation R B) χ r hdeg hfit

end Algebra.Presentation
