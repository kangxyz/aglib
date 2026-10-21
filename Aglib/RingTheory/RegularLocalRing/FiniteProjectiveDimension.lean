/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.RingTheory.Regular.QuotientProjectiveDimension
public import Aglib.RingTheory.RegularLocalRing.Parameters

/-!
# Projective dimension bounds over regular local rings

Dimension induction uses a regular first parameter, a finite free presentation,
and the projective-dimension comparison for its principal quotient. This avoids
requiring a separate minimal-resolution or Tor-detection framework. Cancellation
of the regular-element shift takes place in `WithBot ℕ∞`, including infinite and
zero-module projective dimensions.
-/

@[expose] public section

noncomputable section

universe u

open CategoryTheory IsLocalRing

namespace IsRegularLocalRing

/-- Finite modules over a regular local ring have projective dimension bounded
by the ring dimension, without assuming finite projective dimension in advance. -/
theorem projectiveDimension_le_dimension (d : ℕ) (R : Type u) [CommRing R]
    [IsRegularLocalRing R] (hd : ringKrullDim R = (d : ℕ))
    (M : ModuleCat.{u} R) [Module.Finite R M] :
    projectiveDimension M ≤ (d : ℕ) := by
  induction d generalizing R with
  | zero =>
    let := (isField_of_regularLocal_dimension_zero R (by simpa using hd)).toField
    exact Projective.projectiveDimension_le_zero M
  | succ d ih =>
    obtain ⟨x, hx, hxreg, hQ, hdim⟩ := exists_regular_parameter R d hd
    let Q := R ⧸ Ideal.span {x}
    have : IsRegularLocalRing Q := hQ
    obtain ⟨P, _, _, _, _, p, hp⟩ := Module.exists_finite_presentation R M
    let S := p.shortComplexKer
    have hS : S.ShortExact := LinearMap.shortExact_shortComplexKer hp
    have : Module.Finite R S.X₁ := inferInstanceAs (Module.Finite R (LinearMap.ker p))
    have hP : IsSMulRegular P x :=
      ((TensorProduct.rid R P).isSMulRegular_congr x).mp (hxreg.lTensor P)
    have hK : IsSMulRegular S.X₁ x := IsSMulRegular.submodule (LinearMap.ker p) x hP
    let N := ModuleCat.of Q (QuotSMulTop x S.X₁)
    have : Module.Finite Q N :=
      Module.Finite.of_restrictScalars_finite R Q (QuotSMulTop x S.X₁)
    have : HasProjectiveDimensionLE N d :=
      (projectiveDimension_le_iff N d).mp (ih Q hdim N)
    let F := ModuleCat.restrictScalars (Ideal.Quotient.mk (Ideal.span {x}))
    have : HasProjectiveDimensionLE (F.obj N) (d + 1) :=
      ModuleCat.hasProjectiveDimensionLE_restrictScalars_quotient x hx hxreg N d
    let e : F.obj N ≃ₗ[R] QuotSMulTop x S.X₁ :=
      { toFun := id
        invFun := id
        left_inv := fun _ => rfl
        right_inv := fun _ => rfl
        map_add' := fun _ _ => rfl
        map_smul' := fun r m =>
          IsScalarTower.algebraMap_smul (M := QuotSMulTop x S.X₁) Q r m }
    have hquot : projectiveDimension (ModuleCat.of R (QuotSMulTop x S.X₁)) ≤
        (d + 1 : ℕ) := by
      rw [← ModuleCat.projectiveDimension_eq_of_linearEquiv
        (M := F.obj N) (N := ModuleCat.of R (QuotSMulTop x S.X₁)) e]
      exact (projectiveDimension_le_iff _ _).mpr inferInstance
    rw [ModuleCat.projectiveDimension_quotSMulTop_eq_succ_of_isSMulRegular
      S.X₁ x hK hx] at hquot
    have hKdim : projectiveDimension S.X₁ ≤ (d : ℕ) := by
      apply (ENat.WithBot.add_le_add_natCast_right_iff (c := 1)).mp
      simpa only [Nat.cast_add, Nat.cast_one] using hquot
    have : HasProjectiveDimensionLE S.X₁ d :=
      (projectiveDimension_le_iff _ _).mp hKdim
    exact (projectiveDimension_le_iff _ _).mpr
      (hS.hasProjectiveDimensionLT_X₃ (d + 1) inferInstance
        (hasProjectiveDimensionLT_of_ge S.X₂ 1 (d + 2) (by omega)))

end IsRegularLocalRing
