/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.Algebra.Category.ModuleCat.ChangeOfRings.Coinduction
public import Mathlib.LinearAlgebra.Dual.Lemmas

/-!
# Generation by the kernel of evaluation at one

For a finite-dimensional commutative algebra `B` over a field `k`, of
dimension at least two, the functionals vanishing at `1` generate the
literal native coinduced `B`-module `Hom_k(B,M)` for any `k`-module `M`.
The coefficient module need not be finite, nonzero or one-dimensional.

The evaluation map is the actual restriction--coinduction counit. It is
`k`-linear on the original restricted module; no `B`-linearity is asserted.
The action used throughout is the native coinduced action
`(b • φ)(x) = φ(x * b)`.

No reducedness, separability, locality, Gorenstein or nonzero-trace premise
is required. The current consumer is generation on a possibly nonreduced
Cartier hyperplane section of a Cohen--Macaulay curve. Geometric adjunction
and normalization of its boundary map as this original evaluation counit
remain separate upstream obligations.
-/

@[expose] public section

noncomputable section

universe u

open CategoryTheory

namespace ModuleCat.CoextendScalars

section Evaluation

variable (R A : Type u) [CommRing R] [CommRing A] [Algebra R A]

/-- Evaluation at `1` with arbitrary coefficients is the original
restriction--coinduction counit, with its native source-ring linearity. -/
def evaluationAtOneWithCoefficients (M : ModuleCat.{u} R) :
    (ModuleCat.restrictScalars (algebraMap R A)).obj
      ((ModuleCat.coextendScalars (algebraMap R A)).obj M) →ₗ[R] M :=
  ((ModuleCat.restrictCoextendScalarsAdj (algebraMap R A)).counit.app M).hom

@[simp]
theorem evaluationAtOneWithCoefficients_apply (M : ModuleCat.{u} R)
    (φ : (ModuleCat.coextendScalars (algebraMap R A)).obj M) :
    evaluationAtOneWithCoefficients R A M φ =
      (CoextendScalars.equiv (algebraMap R A) M φ) (1 : A) := rfl

/-- The original coinduced action retains multiplication in the source
of the coefficient-valued functional before evaluation. -/
theorem evaluationAtOneWithCoefficients_smul (M : ModuleCat.{u} R) (a : A)
    (φ : (ModuleCat.coextendScalars (algebraMap R A)).obj M) :
    evaluationAtOneWithCoefficients R A M (a • φ) =
      (CoextendScalars.equiv (algebraMap R A) M φ) a := by
  change (a • φ) (1 : A) = φ a
  simpa only [one_mul] using
    CoextendScalars.smul_apply (algebraMap R A) M φ a 1

/-- Evaluation at `1` is the original restriction--coinduction counit,
with its native source-ring linearity. -/
def evaluationAtOne :
    (ModuleCat.restrictScalars (algebraMap R A)).obj
      ((ModuleCat.coextendScalars (algebraMap R A)).obj (ModuleCat.of R R)) →ₗ[R] R :=
  ((ModuleCat.restrictCoextendScalarsAdj (algebraMap R A)).counit.app
    (ModuleCat.of R R)).hom

@[simp]
theorem evaluationAtOne_apply
    (φ : (ModuleCat.coextendScalars (algebraMap R A)).obj (ModuleCat.of R R)) :
    evaluationAtOne R A φ =
      (CoextendScalars.equiv (algebraMap R A) (ModuleCat.of R R) φ) (1 : A) := rfl

/-- Native target-ring multiplication acts by multiplication in the source
of the original functional before evaluation. -/
theorem evaluationAtOne_smul (a : A)
    (φ : (ModuleCat.coextendScalars (algebraMap R A)).obj (ModuleCat.of R R)) :
    evaluationAtOne R A (a • φ) =
      (CoextendScalars.equiv (algebraMap R A) (ModuleCat.of R R) φ) a := by
  change (a • φ) (1 : A) = φ a
  simpa only [one_mul] using
    CoextendScalars.smul_apply (algebraMap R A) (ModuleCat.of R R) φ a 1

end Evaluation

section Generation

variable (k B : Type u) [Field k] [CommRing B] [Algebra k B]

/-- The original functionals with evaluation zero at `1` generate the native
coinduced module over `B`. Evaluation is used only as a `k`-linear map. -/
theorem span_zero_evaluationAtOne_eq_top (hdim : 2 ≤ Module.finrank k B) :
    Submodule.span B
      {φ : (ModuleCat.coextendScalars (algebraMap k B)).obj (ModuleCat.of k k) |
        evaluationAtOne k B φ = 0} = ⊤ := by
  classical
  let U : Submodule k B := Submodule.span k {(1 : B)}
  have hU : U < ⊤ := by
    apply lt_top_iff_ne_top.mpr
    intro htop
    have hle : Module.finrank k U ≤ 1 := by
      simpa [U] using
        (finrank_span_le_card (R := k) ({(1 : B)} : Set B))
    rw [htop, finrank_top] at hle
    omega
  obtain ⟨φ₀, hφ₀, hker⟩ := U.exists_le_ker_of_lt_top hU
  have hφone : φ₀ (1 : B) = 0 :=
    LinearMap.mem_ker.mp (hker (Submodule.subset_span (Set.mem_singleton (1 : B))))
  obtain ⟨u, hu⟩ := DFunLike.ne_iff.mp hφ₀
  have hu0 : φ₀ u ≠ 0 := by simpa only [LinearMap.zero_apply] using hu
  let Ω := (ModuleCat.coextendScalars (algebraMap k B)).obj (ModuleCat.of k k)
  let M := (ModuleCat.restrictScalars (algebraMap k B)).obj (ModuleCat.of B B)
  let e : M ≃ₗ[k] B :=
    { toFun := id
      invFun := id
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl
      map_add' := fun _ _ => rfl
      map_smul' r b := by
        change algebraMap k B r * (show B from b) = r • (show B from b)
        exact (Algebra.smul_def r (show B from b)).symm }
  let ψ : Ω :=
    (CoextendScalars.equiv (algebraMap k B) (ModuleCat.of k k)).symm
      (φ₀.comp e.toLinearMap)
  let N : Submodule B Ω := Submodule.span B {φ : Ω | evaluationAtOne k B φ = 0}
  have hψone : evaluationAtOne k B ψ = 0 := by
    change φ₀ (1 : B) = 0
    exact hφone
  have hψN : ψ ∈ N := Submodule.subset_span hψone
  let t : Ω := (algebraMap k B (φ₀ u)⁻¹ * u) • ψ
  have htN : t ∈ N := N.smul_mem _ hψN
  have htone : evaluationAtOne k B t = 1 := by
    change evaluationAtOne k B ((algebraMap k B (φ₀ u)⁻¹ * u) • ψ) = 1
    rw [evaluationAtOne_smul]
    change φ₀ (algebraMap k B (φ₀ u)⁻¹ * u) = 1
    rw [← Algebra.smul_def, φ₀.map_smul, smul_eq_mul]
    exact inv_mul_cancel₀ hu0
  change N = ⊤
  apply top_unique
  intro φ _
  have hscale :
      evaluationAtOne k B ((algebraMap k B (evaluationAtOne k B φ)) • t) =
        (evaluationAtOne k B φ) • evaluationAtOne k B t :=
    (evaluationAtOne k B).map_smul (evaluationAtOne k B φ) t
  have hz : evaluationAtOne k B (φ - (algebraMap k B (evaluationAtOne k B φ)) • t) = 0 := by
    calc
      evaluationAtOne k B (φ - (algebraMap k B (evaluationAtOne k B φ)) • t) =
          evaluationAtOne k B φ -
            evaluationAtOne k B ((algebraMap k B (evaluationAtOne k B φ)) • t) :=
        (evaluationAtOne k B).map_sub _ _
      _ = evaluationAtOne k B φ - evaluationAtOne k B φ :=
        congrArg (fun z : k => evaluationAtOne k B φ - z)
          (hscale.trans
            ((congrArg (fun z : k => evaluationAtOne k B φ • z) htone).trans
              (mul_one (evaluationAtOne k B φ))))
      _ = 0 := sub_self _
  have hzN : φ - (algebraMap k B (evaluationAtOne k B φ)) • t ∈ N :=
    Submodule.subset_span hz
  have hcN : (algebraMap k B (evaluationAtOne k B φ)) • t ∈ N := N.smul_mem _ htN
  simpa only [sub_add_cancel] using N.add_mem hzN hcN

/-- The generation statement in the literal original-functional presentation
provided by native `CoextendScalars.equiv`. -/
theorem span_functionals_vanishing_at_one_eq_top (hdim : 2 ≤ Module.finrank k B) :
    Submodule.span B
      {φ : (ModuleCat.coextendScalars (algebraMap k B)).obj (ModuleCat.of k k) |
        (CoextendScalars.equiv (algebraMap k B) (ModuleCat.of k k) φ) (1 : B) = 0} = ⊤ := by
  simpa only [evaluationAtOne_apply] using span_zero_evaluationAtOne_eq_top k B hdim

/-- Original coefficient-valued functionals vanishing at `1` generate the
native coinduced module. No condition on the coefficient module is needed. -/
theorem span_zero_evaluationAtOneWithCoefficients_eq_top (M : ModuleCat.{u} k)
    (hdim : 2 ≤ Module.finrank k B) :
    Submodule.span B
      {φ : (ModuleCat.coextendScalars (algebraMap k B)).obj M |
        evaluationAtOneWithCoefficients k B M φ = 0} = ⊤ := by
  classical
  let U : Submodule k B := Submodule.span k {(1 : B)}
  have hU : U < ⊤ := by
    apply lt_top_iff_ne_top.mpr
    intro htop
    have hle : Module.finrank k U ≤ 1 := by
      simpa [U] using
        (finrank_span_le_card (R := k) ({(1 : B)} : Set B))
    rw [htop, finrank_top] at hle
    omega
  obtain ⟨ψ₀, hψ₀, hker⟩ := U.exists_le_ker_of_lt_top hU
  have hψone : ψ₀ (1 : B) = 0 :=
    LinearMap.mem_ker.mp (hker (Submodule.subset_span (Set.mem_singleton (1 : B))))
  obtain ⟨u, hu⟩ := DFunLike.ne_iff.mp hψ₀
  have hu0 : ψ₀ u ≠ 0 := by simpa only [LinearMap.zero_apply] using hu
  let a : B := algebraMap k B (ψ₀ u)⁻¹ * u
  have hψa : ψ₀ a = 1 := by
    change ψ₀ (algebraMap k B (ψ₀ u)⁻¹ * u) = 1
    rw [← Algebra.smul_def, ψ₀.map_smul, smul_eq_mul]
    exact inv_mul_cancel₀ hu0
  let V := (ModuleCat.restrictScalars (algebraMap k B)).obj (ModuleCat.of B B)
  let e : V ≃ₗ[k] B :=
    { toFun := id
      invFun := id
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl
      map_add' := fun _ _ => rfl
      map_smul' r b := by
        change algebraMap k B r * (show B from b) = r • (show B from b)
        exact (Algebra.smul_def r (show B from b)).symm }
  let Ω := (ModuleCat.coextendScalars (algebraMap k B)).obj M
  let N : Submodule B Ω :=
    Submodule.span B {φ : Ω | evaluationAtOneWithCoefficients k B M φ = 0}
  change N = ⊤
  apply top_unique
  intro φ _
  let m : M := evaluationAtOneWithCoefficients k B M φ
  let η : Ω :=
    (CoextendScalars.equiv (algebraMap k B) M).symm
      ((ψ₀.comp e.toLinearMap).smulRight m)
  have hηone : evaluationAtOneWithCoefficients k B M η = 0 := by
    change ψ₀ (1 : B) • m = 0
    exact (congrArg (fun c : k => c • m) hψone).trans (zero_smul k m)
  have hηN : η ∈ N := Submodule.subset_span hηone
  have haηN : a • η ∈ N := N.smul_mem _ hηN
  have haη : evaluationAtOneWithCoefficients k B M (a • η) = m := by
    calc
      evaluationAtOneWithCoefficients k B M (a • η) =
          (CoextendScalars.equiv (algebraMap k B) M η) a :=
        evaluationAtOneWithCoefficients_smul k B M a η
      _ = ψ₀ a • m := rfl
      _ = m := (congrArg (fun c : k => c • m) hψa).trans (one_smul k m)
  have hz : evaluationAtOneWithCoefficients k B M (φ - a • η) = 0 := by
    calc
      evaluationAtOneWithCoefficients k B M (φ - a • η) =
          evaluationAtOneWithCoefficients k B M φ -
            evaluationAtOneWithCoefficients k B M (a • η) :=
        (evaluationAtOneWithCoefficients k B M).map_sub _ _
      _ = m - m := congrArg (fun z : M => m - z) haη
      _ = 0 := sub_self _
  have hzN : φ - a • η ∈ N := Submodule.subset_span hz
  simpa only [sub_add_cancel] using N.add_mem hzN haηN

/-- The arbitrary-coefficient generation theorem in the literal original
functional presentation. The coefficient module has no finiteness or rank premise. -/
theorem span_functionals_vanishing_at_one_with_coefficients_eq_top
    (M : ModuleCat.{u} k) (hdim : 2 ≤ Module.finrank k B) :
    Submodule.span B
      {φ : (ModuleCat.coextendScalars (algebraMap k B)).obj M |
        (CoextendScalars.equiv (algebraMap k B) M φ) (1 : B) = 0} = ⊤ := by
  simpa only [evaluationAtOneWithCoefficients_apply] using
    span_zero_evaluationAtOneWithCoefficients_eq_top k B M hdim

end Generation

end ModuleCat.CoextendScalars
