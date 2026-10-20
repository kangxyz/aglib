/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Aglib.RingTheory.DiscreteValuationRing.EtaleBaseChange
public import Aglib.Analysis.Normed.Field.DVR
public import Mathlib.Analysis.Normed.Unbundled.SpectralNorm

/-!
# Compatible spectral norms on finite unramified DVR extensions

Source: `R5Lab.Aglib.Analysis.Normed.Field.UnramifiedDVR`,
revision `f8a3314ddecffcada2ec721d26d56a937bed9690`. The actual objects, maps, norm choices,
universes, and stated hypotheses are retained.
-/

@[expose] public section

noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

open NormedField

/- F3 source: FiniteEtaleNorm.lean; SHA256
  e2c4147fe2114b5852ea14da38343871a388614bbfdf8d69fe37a55d89e4db4f. -/
section F3_FiniteEtaleNorm

/-!
# Compatible spectral norm on finite unramified DVR extensions

The finite fraction-field extension carries mathlib's constructed spectral norm.
Its restriction to the base field is the original norm; it is complete and
ultrametric. A monic integral equation and the formalized spectral root bound
place the finite integral extension in the unit ball. DVR factorization, unit
norms, and preservation of an actual uniformizer prove the converse.

All statements below are proved from pinned mathlib and the existing DVR-map
uniformizer theorem. No new analytic, valuation, or extension-existence premise
is retained. The spectral root bound's source is Bosch–Güntzer–Remmert,
Non-Archimedean Analysis, Proposition 3.1.2/1(1), as documented by mathlib's
`norm_root_le_spectralValue`.
-/

noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open Polynomial IsDiscreteValuationRing
namespace NormedField.NormCompatible

section Normed
variable {S K : Type u} [CommRing S] [IsDomain S] [IsDiscreteValuationRing S]
  [NormedField K] [Algebra S K] [IsFractionRing S K]

/-- A DVR whose elements are bounded and whose uniformizer has strictly small norm
is the closed unit ball of its fraction field. -/
theorem normCompatible_of_bounded_uniformizer
    (hbound : ∀ s : S, ‖algebraMap S K s‖ ≤ 1) {π : S}
    (hπ : Irreducible π) (hsmall : ‖algebraMap S K π‖ < 1) :
    NormCompatible S K := by
  have hunit (u : Sˣ) : ‖algebraMap S K (u : S)‖ = 1 := by
    apply le_antisymm (hbound _)
    have he : algebraMap S K (u : S) * algebraMap S K (↑u⁻¹ : S) = 1 := by
      rw [← map_mul, Units.mul_inv, map_one]
    have hn := congrArg norm he
    rw [norm_mul, norm_one] at hn
    calc
      1 = ‖algebraMap S K (u : S)‖ * ‖algebraMap S K (↑u⁻¹ : S)‖ := hn.symm
      _ ≤ ‖algebraMap S K (u : S)‖ * 1 :=
        mul_le_mul_of_nonneg_left (hbound _) (norm_nonneg _)
      _ = _ := mul_one _
  intro x
  refine ⟨fun hx => ?_, ?_⟩
  · by_cases hx0 : x = 0
    · exact ⟨0, by simp [hx0]⟩
    obtain ⟨n, v, hv⟩ := exists_units_eq_smul_zpow_of_irreducible hπ hx0
    have hpos : 0 < ‖algebraMap S K π‖ :=
      norm_pos_iff.mpr ((map_ne_zero_iff _ (IsFractionRing.injective S K)).mpr hπ.ne_zero)
    have hn : 0 ≤ n := by
      rw [hv, Units.smul_def, Algebra.smul_def, norm_mul, norm_zpow, hunit, _root_.one_mul] at hx
      exact (zpow_le_one_iff_right_of_lt_one₀ hpos hsmall).mp hx
    refine ⟨(v : S) * π ^ n.toNat, ?_⟩
    rw [map_mul, map_pow, hv, Units.smul_def, Algebra.smul_def, ← zpow_natCast,
      Int.toNat_of_nonneg hn]
  · rintro ⟨s, rfl⟩
    exact hbound s
end Normed

section Spectral
variable {R S F K : Type u}
  [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
  [CommRing S] [IsDomain S] [IsDiscreteValuationRing S]
  [NontriviallyNormedField F] [CompleteSpace F] [IsUltrametricDist F]
  [Field K] [Algebra F K] [FiniteDimensional F K]
  [Algebra R F] [IsFractionRing R F] [Algebra R S] [Module.Finite R S]
  [Algebra S K] [IsFractionRing S K] [Algebra R K]
  [IsScalarTower R S K] [IsScalarTower R F K]

omit [IsDomain S] [IsDiscreteValuationRing S] [CompleteSpace F] [IsFractionRing S K] in
/-- Integrality and the spectral root bound place every element of the finite
integral extension in the closed spectral unit ball. -/
theorem spectralNorm_map_le_one (H : NormCompatible R F) (s : S) :
    spectralNorm F K (algebraMap S K s) ≤ 1 := by
  have hi : IsIntegral R (algebraMap S K s) :=
    (Algebra.IsIntegral.isIntegral (R := R) s).algebraMap
  obtain ⟨p, hp, hs⟩ := hi
  have hroot : aeval (algebraMap S K s) (p.map (algebraMap R F)) = 0 := by
    rw [← aeval_eq_aeval_map (IsScalarTower.algebraMap_eq R F K).symm]
    exact hs
  apply le_trans (norm_root_le_spectralValue (f := spectralAlgNorm F K)
    spectralAlgNorm_isPowMul isNonarchimedean_spectralNorm (hp.map _) hroot)
  apply (spectralValue_le_one_iff (hp.map _)).2
  intro n
  rw [coeff_map]
  exact H.norm_map_le_one _

/-- The constructed spectral norm extends the original field norm exactly. -/
theorem spectral_norm_embedding (x : F) :
    letI := spectralNorm.normedField F K
    ‖algebraMap F K x‖ = ‖x‖ := spectralNorm_extends x

/-- The spectral norm on a finite extension is complete. -/
theorem spectral_completeSpace :
    letI := spectralNorm.normedField F K
    CompleteSpace K := spectralNorm.completeSpace F K

/-- The spectral norm on a finite extension is nonarchimedean. -/
theorem spectral_isUltrametricDist :
    letI := spectralNorm.normedField F K
    IsUltrametricDist K := by
  let := spectralNorm.normedField F K
  exact IsUltrametricDist.isUltrametricDist_of_isNonarchimedean_norm
    isNonarchimedean_spectralNorm

/-- A finite unramified local extension of compatible DVRs has a compatible
spectral norm on its actual fraction field. No analytic comparison premise is used. -/
theorem spectral_normCompatible [IsLocalHom (algebraMap R S)]
    [Algebra.EssFiniteType R S] [Algebra.FormallyUnramified R S]
    (H : NormCompatible R F) :
    letI := spectralNorm.normedField F K
    NormCompatible S K := by
  let := spectralNorm.normedField F K
  obtain ⟨π, hπ⟩ := exists_irreducible R
  apply normCompatible_of_bounded_uniformizer (spectralNorm_map_le_one H)
    (IsDiscreteValuationRing.unramified_map_uniformizer hπ)
  change spectralNorm F K (algebraMap S K (algebraMap R S π)) < 1
  rw [← IsScalarTower.algebraMap_apply R S K,
    IsScalarTower.algebraMap_apply R F K, spectralNorm_extends]
  exact H.norm_map_irreducible_lt_one hπ

end Spectral
end NormedField.NormCompatible

end -- closes the source module's noncomputable section
end F3_FiniteEtaleNorm

end
