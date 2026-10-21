/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.RingTheory.ReesAlgebra.Grading
public import Aglib.RingTheory.ReesAlgebra.GradedTransitionGenerators
public import Mathlib.RingTheory.Noetherian.Basic
public import Mathlib.RingTheory.Ideal.Operations

/-!
# Finite graded Rees modules with degree-lowering transitions

The transitions need not be injective. Both compatibility with homogeneous
multiplication and its underlying scalar formula are retained explicitly.
Finite homogeneous generation gives the shifted image estimate. The same
argument applied to the actual homogeneous kernel gives uniform kernel killing.
-/

@[expose] public noncomputable section
set_option autoImplicit false
open DirectSum
open scoped Pointwise
universe u v
namespace reesAlgebra
variable {A : Type u} [CommRing A] (I : Ideal A)
variable {M : Type v} [AddCommGroup M] [Module A M] [Module (reesAlgebra I) M]
variable (E : ℕ → Submodule A M) [DirectSum.Decomposition E]
variable [SetLike.GradedSMul (grading I) E]

/-- Degree-lowering maps on an actual graded module over the native Rees algebra.
The two action equations express different geometric naturality requirements. -/
structure GradedTransition where
  /-- The original transition for every pair of ordered degrees. -/
  map : ∀ {n m : ℕ}, m ≤ n → E n →ₗ[A] E m
  map_self : ∀ (n : ℕ) (x : E n), map (le_refl n) x = x
  map_comp : ∀ {l m n : ℕ} (hlm : l ≤ m) (hmn : m ≤ n) (x : E n),
    map hlm (map hmn x) = map (hlm.trans hmn) x
  /-- Lowering the module degree commutes with homogeneous multiplication. -/
  map_mul : ∀ (r n m : ℕ) (h : m ≤ n) (a : grading I r) (x : E n),
    map (Nat.add_le_add_left h r) (GradedModule.homogeneousSMul (grading I) E a x) =
      GradedModule.homogeneousSMul (grading I) E a (map h x)
  /-- Lowering the action degree recovers the original base-ring scalar action. -/
  map_mul_scalar : ∀ (r n : ℕ) (a : grading I r) (x : E n),
    map (Nat.le_add_left n r) (GradedModule.homogeneousSMul (grading I) E a x) =
      (((a : reesAlgebra I) : Polynomial A).coeff r) • x

namespace GradedTransition
variable {I E} (T : GradedTransition I E)

omit [DirectSum.Decomposition E] in
/-- The degree-zero image of homogeneous multiplication is its coefficient times
the degree-zero image. -/
lemma map_zero_mul (r n : ℕ) (a : grading I r) (x : E n) :
    T.map (Nat.zero_le (r + n)) (GradedModule.homogeneousSMul (grading I) E a x) =
      (((a : reesAlgebra I) : Polynomial A).coeff r) • T.map (Nat.zero_le n) x := by
  rw [← T.map_comp (Nat.zero_le n) (Nat.le_add_left n r), T.map_mul_scalar]
  exact (T.map (Nat.zero_le n)).map_smul _ _

omit [DirectSum.Decomposition E] in
/-- The scalar equation for the actual coefficient in the actual ideal power. -/
lemma map_homogeneous_scalar (r n : ℕ) (a : ↥(I ^ r : Ideal A)) (x : E n) :
    T.map (Nat.le_add_left n r) (GradedModule.homogeneousSMul (grading I) E (homogeneous I r a) x) =
      (a : A) • x := by
  simpa [homogeneous] using T.map_mul_scalar r n (homogeneous I r a) x

omit [DirectSum.Decomposition E] in
/-- Equality of target degrees transports the zero criterion for a transition. -/
lemma map_eq_zero_iff {n m l : ℕ} (h : m ≤ n) (h' : l ≤ n) (e : m = l)
    (x : E n) : T.map h x = 0 ↔ T.map h' x = 0 := by
  subst l
  rfl

/-- The homogeneous kernel of the map to degree zero, as a genuine Rees submodule. -/
def zeroKernel : Submodule (reesAlgebra I) M :=
  GradedModule.gradedSubmodule (grading I) E
    (fun n => LinearMap.ker (T.map (Nat.zero_le n))) (by
      intro r n a x hx
      change T.map (Nat.zero_le (r + n)) (GradedModule.homogeneousSMul (grading I) E a x) = 0
      rw [T.map_zero_mul, LinearMap.mem_ker.mp hx, smul_zero])

lemma mem_zeroKernel (x : M) :
    x ∈ T.zeroKernel ↔ ∀ n, T.map (Nat.zero_le n) (decompose E x n) = 0 := Iff.rfl

lemma homogeneous_mem_zeroKernel {n : ℕ} (x : E n)
    (hx : T.map (Nat.zero_le n) x = 0) : (x : M) ∈ T.zeroKernel :=
  GradedModule.homogeneous_mem_componentSubmodule E _ x hx

lemma zeroKernel_homogeneous (x : M) (hx : x ∈ T.zeroKernel) (n : ℕ) :
    (decompose E x n : M) ∈ T.zeroKernel :=
  T.homogeneous_mem_zeroKernel _ (hx n)

/-- Vectors killed after lowering by at most `c` form a graded Rees submodule. -/
def shiftedKernel (c : ℕ) : Submodule (reesAlgebra I) M :=
  GradedModule.gradedSubmodule (grading I) E
    (fun n => LinearMap.ker (T.map (Nat.sub_le n c))) (by
      intro r n a x hx
      have h : r + n - c ≤ r + (n - c) := by omega
      have hs := T.map_mul r n (n - c) (Nat.sub_le n c) a x
      rw [LinearMap.mem_ker.mp hx] at hs
      have hz : GradedModule.homogeneousSMul (grading I) E a (0 : E (n - c)) = 0 := by
        apply Subtype.ext
        exact smul_zero _
      rw [hz] at hs
      change T.map (Nat.sub_le (r + n) c) (GradedModule.homogeneousSMul (grading I) E a x) = 0
      rw [← T.map_comp h (Nat.add_le_add_left (Nat.sub_le n c) r), hs, map_zero])

/-- The degree-zero image obeys the shifted ideal-power bound componentwise. -/
def imageBound (c : ℕ) : Submodule (reesAlgebra I) M :=
  GradedModule.gradedSubmodule (grading I) E
    (fun n => (I ^ (n - c) • (⊤ : Submodule A (E 0))).comap
      (T.map (Nat.zero_le n))) (by
      intro r n a x hx
      change T.map (Nat.zero_le (r + n)) (GradedModule.homogeneousSMul (grading I) E a x) ∈
        I ^ (r + n - c) • (⊤ : Submodule A (E 0))
      rw [T.map_zero_mul]
      have ha : (((a : reesAlgebra I) : Polynomial A).coeff r) ∈ I ^ r :=
        (a : reesAlgebra I).property r
      have hz : (((a : reesAlgebra I) : Polynomial A).coeff r) •
          T.map (Nat.zero_le n) x ∈
          I ^ (r + (n - c)) • (⊤ : Submodule A (E 0)) := by
        rw [pow_add, Submodule.mul_smul]
        exact Submodule.smul_mem_smul ha hx
      exact (Submodule.smul_mono (Ideal.pow_le_pow_right (by omega)) le_rfl) hz)

/-- Finite generation alone gives a uniform bound for the images in degree zero. -/
theorem exists_image_bound [Module.Finite (reesAlgebra I) M] :
    ∃ c : ℕ, ∀ n (x : E (n + c)),
      T.map (Nat.zero_le (n + c)) x ∈ I ^ n • (⊤ : Submodule A (E 0)) := by
  obtain ⟨c, hc⟩ := GradedModule.exists_bound_span_eq E
    (⊤ : Submodule (reesAlgebra I) M) Module.Finite.fg_top (by simp)
  have htop : (⊤ : Submodule (reesAlgebra I) M) ≤ T.imageBound c := by
    rw [← hc]
    apply Submodule.span_le.mpr
    rintro x ⟨n, hn, hx, _⟩
    apply GradedModule.homogeneous_mem_componentSubmodule E _ (⟨x, hx⟩ : E n)
    change T.map (Nat.zero_le n) ⟨x, hx⟩ ∈ I ^ (n - c) • (⊤ : Submodule A (E 0))
    simp [Nat.sub_eq_zero_of_le hn]
  refine ⟨c, fun n x => ?_⟩
  have h := htop (Submodule.mem_top : (x : M) ∈ (⊤ : Submodule (reesAlgebra I) M)) (n + c)
  change T.map (Nat.zero_le (n + c)) (decompose E (x : M) (n + c)) ∈
    I ^ (n + c - c) • (⊤ : Submodule A (E 0)) at h
  simpa only [DirectSum.decompose_coe, DirectSum.of_eq_same, Nat.add_sub_cancel] using h

/-- Finite homogeneous generation of the actual kernel gives uniform killing.
No injectivity or surjectivity of transition maps is used. -/
theorem exists_kernel_bound [IsNoetherianRing A] [Module.Finite (reesAlgebra I) M] :
    ∃ c : ℕ, ∀ n (x : E (n + c)),
      T.map (Nat.zero_le (n + c)) x = 0 → T.map (Nat.le_add_right n c) x = 0 := by
  obtain ⟨c, hc⟩ := GradedModule.exists_bound_span_eq E T.zeroKernel
    (IsNoetherian.noetherian _) T.zeroKernel_homogeneous
  have hle : T.zeroKernel ≤ T.shiftedKernel c := by
    rw [← hc]
    apply Submodule.span_le.mpr
    rintro x ⟨n, hn, hx, hxK⟩
    apply GradedModule.homogeneous_mem_componentSubmodule E _ (⟨x, hx⟩ : E n)
    have hz := hxK n
    have he : decompose E x n = (⟨x, hx⟩ : E n) := by
      simpa only [DirectSum.of_eq_same] using
        congrArg (fun z => z n) (DirectSum.decompose_coe E (⟨x, hx⟩ : E n))
    rw [he] at hz
    change T.map (Nat.zero_le n) (⟨x, hx⟩ : E n) = 0 at hz
    change T.map (Nat.sub_le n c) (⟨x, hx⟩ : E n) = 0
    exact (T.map_eq_zero_iff (Nat.sub_le n c) (Nat.zero_le n)
      (Nat.sub_eq_zero_of_le hn) _).mpr hz
  refine ⟨c, fun n x hx => ?_⟩
  have h := hle (T.homogeneous_mem_zeroKernel x hx) (n + c)
  change T.map (Nat.sub_le (n + c) c) (decompose E (x : M) (n + c)) = 0 at h
  rw [DirectSum.decompose_coe, DirectSum.of_eq_same] at h
  exact (T.map_eq_zero_iff (Nat.sub_le (n + c) c) (Nat.le_add_right n c)
    (Nat.add_sub_cancel n c) x).mp h

/-- One shift simultaneously bounds degree-zero images and kills the degree-zero
kernel under the original transitions. -/
theorem exists_uniform_bound [IsNoetherianRing A] [Module.Finite (reesAlgebra I) M] :
    ∃ c : ℕ, (∀ n (x : E (n + c)),
      T.map (Nat.zero_le (n + c)) x ∈ I ^ n • (⊤ : Submodule A (E 0))) ∧
      ∀ n (x : E (n + c)), T.map (Nat.zero_le (n + c)) x = 0 →
        T.map (Nat.le_add_right n c) x = 0 := by
  obtain ⟨a, ha⟩ := T.exists_image_bound
  obtain ⟨b, hb⟩ := T.exists_kernel_bound
  refine ⟨a + b, ?_, ?_⟩
  · intro n x
    let P : ℕ → Prop := fun k => ∀ y : E k,
      T.map (Nat.zero_le k) y ∈ I ^ (n + b) • (⊤ : Submodule A (E 0))
    have hP : P (n + b + a) := ha (n + b)
    have e : n + b + a = n + (a + b) := by omega
    have h : P (n + (a + b)) := e ▸ hP
    exact (Submodule.smul_mono (Ideal.pow_le_pow_right (Nat.le_add_right n b)) le_rfl) (h x)
  · intro n x hx
    let P : ℕ → Prop := fun k => ∀ h : n + a ≤ k, ∀ y : E k,
      T.map (Nat.zero_le k) y = 0 → T.map h y = 0
    have hP : P ((n + a) + b) := fun _ => hb (n + a)
    have e : (n + a) + b = n + (a + b) := Nat.add_assoc n a b
    have h : P (n + (a + b)) := e ▸ hP
    rw [← T.map_comp (Nat.le_add_right n a) (show n + a ≤ n + (a + b) by omega),
      h _ x hx, map_zero]

end GradedTransition
end reesAlgebra
