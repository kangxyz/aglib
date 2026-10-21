/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Mathlib.Algebra.Category.ModuleCat.ChangeOfRingsExact
public import Mathlib.LinearAlgebra.TensorProduct.Pi
public import Mathlib.RingTheory.Regular.ProjectiveDimension

/-!
# Projective dimension under a regular principal quotient

Restriction from a quotient by a regular element increases finite projective-dimension bounds
by at most one. The proof uses finite presentations and
short exact sequences, rather than a separate Tor or minimal-resolution API.
This comparison supplies regular-local dimension induction for finite modules.
-/

@[expose] public section

noncomputable section

universe u

open CategoryTheory IsLocalRing

namespace ModuleCat

/-- A finite free module over a regular principal quotient has projective
dimension at most one over the original local ring. -/
theorem projectiveDimension_quotient_free_le_one {R : Type u} [CommRing R]
    [IsLocalRing R] [IsNoetherianRing R] (x : R) (hx : x ∈ maximalIdeal R)
    (hreg : IsSMulRegular R x) (P : Type u) [AddCommGroup P] [Module R P]
    [Module (R ⧸ Ideal.span {x}) P] [IsScalarTower R (R ⧸ Ideal.span {x}) P]
    [Module.Free (R ⧸ Ideal.span {x}) P] [Module.Finite (R ⧸ Ideal.span {x}) P] :
    projectiveDimension (ModuleCat.of R P) ≤ 1 := by
  classical
  let Q := R ⧸ Ideal.span {x}
  let ι := Module.Free.ChooseBasisIndex Q P
  let b := Module.Free.chooseBasis Q P
  have : Fintype ι := Fintype.ofFinite ι
  let e : QuotSMulTop x (ι → R) ≃ₗ[R] P :=
    (QuotSMulTop.equivQuotTensor x (ι → R)).trans
      ((TensorProduct.piScalarRight R R Q ι).trans (b.equivFun.restrictScalars R).symm)
  have hpreg : IsSMulRegular (ι → R) x :=
    IsSMulRegular.of_right_eq_zero_of_smul fun f hf => by
      funext i
      exact hreg.right_eq_zero_of_smul (congrFun hf i)
  rw [← projectiveDimension_eq_of_linearEquiv
      (M := ModuleCat.of R (QuotSMulTop x (ι → R))) (N := ModuleCat.of R P) e,
    projectiveDimension_quotSMulTop_eq_succ_of_isSMulRegular
      (ModuleCat.of R (ι → R)) x hpreg hx]
  calc
    projectiveDimension (ModuleCat.of R (ι → R)) + 1 =
        1 + projectiveDimension (ModuleCat.of R (ι → R)) := add_comm _ _
    _ ≤ 1 + 0 := add_le_add_right
      (Projective.projectiveDimension_le_zero (ModuleCat.of R (ι → R))) 1
    _ = 1 := add_zero _

/-- Restricting a finite module from a regular principal quotient increases a
finite projective-dimension bound by at most one. -/
theorem hasProjectiveDimensionLE_restrictScalars_quotient {R : Type u} [CommRing R]
    [IsLocalRing R] [IsNoetherianRing R] (x : R) (hx : x ∈ maximalIdeal R)
    (hreg : IsSMulRegular R x) (M : ModuleCat.{u} (R ⧸ Ideal.span {x}))
    [Module.Finite (R ⧸ Ideal.span {x}) M] (n : ℕ) [HasProjectiveDimensionLE M n] :
    HasProjectiveDimensionLE
      ((ModuleCat.restrictScalars (Ideal.Quotient.mk (Ideal.span {x}))).obj M) (n + 1) := by
  let Q := R ⧸ Ideal.span {x}
  have hproper : Ideal.span {x} ≠ ⊤ := ne_top_of_le_ne_top
    (maximalIdeal.isMaximal R).ne_top ((Ideal.span_singleton_le_iff_mem (maximalIdeal R)).mpr hx)
  have : Nontrivial Q := Ideal.Quotient.nontrivial_iff.mpr hproper
  have : IsLocalRing Q := IsLocalRing.of_surjective'
    (Ideal.Quotient.mk (Ideal.span {x})) Ideal.Quotient.mk_surjective
  have : IsNoetherianRing Q := isNoetherianRing_of_surjective R Q
    (Ideal.Quotient.mk (Ideal.span {x})) Ideal.Quotient.mk_surjective
  let F := ModuleCat.restrictScalars (Ideal.Quotient.mk (Ideal.span {x}))
  have hfree (P : ModuleCat.{u} Q) [Module.Free Q P] [Module.Finite Q P] :
      HasProjectiveDimensionLE (F.obj P) 1 := by
    let : Module R P := Module.compHom P (Ideal.Quotient.mk (Ideal.span {x}))
    have : IsScalarTower R Q P := IsScalarTower.of_compHom R Q P
    exact (projectiveDimension_le_iff _ 1).mp
      (projectiveDimension_quotient_free_le_one x hx hreg P)
  induction n generalizing M with
  | zero =>
    have : Projective M := projective_iff_hasProjectiveDimensionLT_one.mpr inferInstance
    have : Module.Free Q M := Module.free_of_flat_of_isLocalRing
    exact hfree M
  | succ n ih =>
    obtain ⟨P, _, _, _, _, p, hp⟩ := Module.exists_finite_presentation Q M
    let S := p.shortComplexKer
    have hS : S.ShortExact := LinearMap.shortExact_shortComplexKer hp
    have hK : HasProjectiveDimensionLE S.X₁ n :=
      (hS.hasProjectiveDimensionLT_X₃_iff n inferInstance).mp inferInstance
    have : Module.Finite Q S.X₁ := inferInstanceAs (Module.Finite Q (LinearMap.ker p))
    have hKR : HasProjectiveDimensionLE (F.obj S.X₁) (n + 1) := ih S.X₁
    have hPR : HasProjectiveDimensionLE (F.obj S.X₂) 1 := hfree S.X₂
    exact (hS.map_of_exact F).hasProjectiveDimensionLT_X₃ (n + 2) hKR
      (hasProjectiveDimensionLT_of_ge (F.obj S.X₂) 2 (n + 3) (by omega))

end ModuleCat
