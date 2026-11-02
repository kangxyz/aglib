/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.RingTheory.AdjoinRoot.PowerRelation
public import Aglib.RingTheory.DiscreteValuationRing.PureDegreeP.FiniteDegree
public import Aglib.RingTheory.Kaehler.Exterior.Map
public import Aglib.RingTheory.Kaehler.PureDegreePTrace.Exterior
public import Mathlib.Algebra.Algebra.Subalgebra.IsSimpleOrder
public import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
public import Mathlib.LinearAlgebra.FreeModule.Finite.Matrix


/-!
# Original pure degree-p field presentations and differential transposes

The transpose is formed from the actual differential trace. Generic line
hypotheses refer to the actual exterior powers. The original root-power
formulas give the antidiagonal pairing and generic bijectivity; no integral
line generator is assumed.
-/

@[expose] public noncomputable section

open Polynomial


open KaehlerDifferential

namespace IsPurelyInseparable

variable (K L : Type*) [Field K] [Field L] [Algebra K L]
  [FiniteDimensional K L] [IsPurelyInseparable K L]
  (p : ℕ) [Fact p.Prime] [CharP K p]

/-- Construct the original field presentation from pure prime degree. -/
theorem exists_degreeP_presentation (hdegree : Module.finrank K L = p) :
    ∃ a : K, ∃ z : L, ∃ h : IsAdjoinRootMonic L ((X : K[X]) ^ p - C a),
      algebraMap K L a = z ^ p ∧ h.root = z ∧ h.map = aeval z := by
  classical
  have hp : p.Prime := Fact.out
  have hex : ∃ z : L, z ∉ Set.range (algebraMap K L) := by
    by_contra h
    have hall : ∀ z : L, z ∈ Set.range (algebraMap K L) := by
      simpa only [not_exists, not_not] using h
    have hbot : (⊥ : Subalgebra K L) = ⊤ := by
      apply top_unique
      intro z _
      exact Algebra.mem_bot.mpr (hall z)
    exact hp.ne_one (hdegree.symm.trans (Subalgebra.bot_eq_top_iff_finrank_eq_one.mp hbot))
  obtain ⟨z, hz⟩ := hex
  have hprime : (Module.finrank K L).Prime := by rwa [hdegree]
  have hgen : Algebra.adjoin K {z} = ⊤ := by
    rcases (Subalgebra.isSimpleOrder_of_finrank_prime K L hprime).eq_bot_or_eq_top
        (Algebra.adjoin K {z}) with hbot | htop
    · have hm := Algebra.self_mem_adjoin_singleton K z
      rw [hbot, Algebra.mem_bot] at hm
      exact (hz hm).elim
    · exact htop
  obtain ⟨a, ha⟩ := pow_mem_range_of_finrank_eq_prime K L p hdegree z
  let h := IsAdjoinRootMonic.ofPowerRelation hp.ne_zero hdegree z a ha hgen
  exact ⟨a, z, h, ha,
    IsAdjoinRootMonic.ofPowerRelation_root hp.ne_zero hdegree z a ha hgen,
    IsAdjoinRootMonic.ofPowerRelation_map hp.ne_zero hdegree z a ha hgen⟩

end IsPurelyInseparable

namespace LinearMap

variable {A B M N : Type*} [CommRing A] [CommRing B] [Algebra A B]
  [AddCommGroup M] [Module A M] [Module B M] [IsScalarTower A B M]
  [SMulCommClass B A M] [AddCommGroup N] [Module A N]

/-- Curry scalar multiplication followed by the original linear functional.
The target N is not given a B-action. -/
def smulTranspose (t : M →ₗ[A] N) : M →ₗ[A] (B →ₗ[A] N) where
  toFun m :=
    { toFun b := t (b • m)
      map_add' b c := by rw [add_smul, map_add]
      map_smul' a b := by
        change t ((a • b) • m) = a • t (b • m)
        rw [smul_assoc, map_smul] }
  map_add' m m' := by
    apply LinearMap.ext
    intro b
    change t (b • (m + m')) = t (b • m) + t (b • m')
    rw [smul_add, map_add]
  map_smul' a m := by
    apply LinearMap.ext
    intro b
    change t (b • (a • m)) = a • t (b • m)
    rw [smul_comm b a, map_smul]

@[simp]
theorem smulTranspose_apply (t : M →ₗ[A] N) (m : M) (b : B) :
    smulTranspose t m b = t (b • m) := rfl

/-- The original B-action is transposed by precomposition, pointwise. -/
theorem smulTranspose_smul_apply (t : M →ₗ[A] N) (b c : B) (m : M) :
    smulTranspose t (b • m) c = smulTranspose t m (c * b) := by
  simp only [smulTranspose_apply, mul_smul]

section FieldLines

variable {K L V W : Type*} [Field K] [Field L] [Algebra K L]
  [FiniteDimensional K L] [AddCommGroup V] [Module K V]
  [AddCommGroup W] [Module K W] [Module L W] [IsScalarTower K L W]
  [SMulCommClass L K W]

/-- A nonzero functional on an actual upper line gives a perfect multiplication
pairing into an actual lower line. The source and target actions are unchanged. -/
theorem smulTranspose_bijective_of_lines (t : W →ₗ[K] V)
    (β : W) (c : L) (hnorm : t (c • β) ≠ 0)
    (hV : Module.finrank K V = 1) (hW : Module.finrank L W = 1) :
    Function.Bijective (smulTranspose (B := L) t) := by
  let : FiniteDimensional K V := .of_finrank_pos (by rw [hV]; exact Nat.zero_lt_one)
  let : FiniteDimensional L W := .of_finrank_pos (by rw [hW]; exact Nat.zero_lt_one)
  let : FiniteDimensional K W := Module.Finite.trans L W
  have hβ : β ≠ 0 := by
    intro hzero
    apply hnorm
    rw [hzero, smul_zero, map_zero]
  have hinj : Function.Injective (smulTranspose (B := L) t) := by
    apply LinearMap.ker_eq_bot.mp
    apply LinearMap.ker_eq_bot'.mpr
    intro ω hzero
    obtain ⟨d, hd⟩ := (finrank_eq_one_iff_of_nonzero' β hβ).mp hW ω
    by_cases hd0 : d = 0
    · rw [← hd, hd0, zero_smul]
    · have he : t ((c * d⁻¹) • ω) = 0 := by
        exact LinearMap.congr_fun hzero (c * d⁻¹)
      have hmul : (c * d⁻¹) * d = c := by
        rw [mul_assoc, inv_mul_cancel₀ hd0, mul_one]
      rw [← hd, smul_smul, hmul] at he
      exact (hnorm he).elim
  have hdim : Module.finrank K W = Module.finrank K (L →ₗ[K] V) := by
    rw [← Module.finrank_mul_finrank K L W, hW, mul_one,
      Module.finrank_linearMap, hV, mul_one]
  exact ⟨hinj, (LinearMap.injective_iff_surjective_of_finrank_eq_finrank hdim).mp hinj⟩

end FieldLines

end LinearMap

namespace KaehlerDifferential

section ExteriorMaps

variable (Λ R S T : Type*) [CommRing Λ] [CommRing R] [CommRing S] [CommRing T]
  [Algebra Λ R] [Algebra Λ S] [Algebra Λ T]
  [Algebra R S] [Algebra S T] [Algebra R T]
  [IsScalarTower Λ R S] [IsScalarTower Λ S T] [IsScalarTower Λ R T]
  [IsScalarTower R S T]


end ExteriorMaps

section ExteriorIdentity

variable (Λ R : Type*) [CommRing Λ] [CommRing R] [Algebra Λ R]


end ExteriorIdentity

variable {Λ K L : Type*} [CommRing Λ] [Field K] [Field L]
  [Algebra Λ K] [Algebra K L] [Algebra Λ L] [IsScalarTower Λ K L]
  {p : ℕ} [CharP K p] {a : K}

local notation:max "Q" n:arg => (⋀[K]^(n + 1) (KaehlerDifferential Λ K))
local notation:max "W" n:arg => (⋀[L]^(n + 1) (KaehlerDifferential Λ L))

/-- The actual field differential trace is independent of its original root presentation. -/
theorem pureDegreePFieldTrace_independent [Fact p.Prime]
    (h : IsAdjoinRootMonic L ((X : K[X]) ^ p - C a))
    {a' : K} (h' : IsAdjoinRootMonic L ((X : K[X]) ^ p - C a')) (n : ℕ) :
    pureDegreePTraceExterior (Λ := Λ) h n = pureDegreePTraceExterior (Λ := Λ) h' n := by
  apply LinearMap.ext
  intro ω
  have he := LinearMap.congr_fun (pureDegreePTraceExterior_naturality h h' n) ω
  change pureDegreePTraceExterior (Λ := Λ) h' n (mapExterior Λ L L (n + 1) ω) =
    pureDegreePTraceExterior (Λ := Λ) h n ω at he
  rw [mapExterior_self, LinearMap.id_apply] at he
  exact he.symm

/-- The original field differential trace, transposed through multiplication in L. -/
def pureDegreePFieldTranspose (h : IsAdjoinRootMonic L ((X : K[X]) ^ p - C a)) (n : ℕ) :
    (W n) →ₗ[K] (L →ₗ[K] (Q n)) :=
  LinearMap.smulTranspose (pureDegreePTraceExterior (Λ := Λ) h n)

@[simp]
theorem pureDegreePFieldTranspose_apply
    (h : IsAdjoinRootMonic L ((X : K[X]) ^ p - C a)) (n : ℕ) (ω : (W n)) (b : L) :
    pureDegreePFieldTranspose (Λ := Λ) h n ω b =
      pureDegreePTraceExterior (Λ := Λ) h n (b • ω) :=
  LinearMap.smulTranspose_apply (pureDegreePTraceExterior (Λ := Λ) h n) ω b

private theorem fieldTrace_root_pow_smul [Fact p.Prime]
    (h : IsAdjoinRootMonic L ((X : K[X]) ^ p - C a)) (n : ℕ)
    (v : Fin n → KaehlerDifferential Λ K) {i : ℕ} (hi : i < p) :
    pureDegreePTraceExterior (Λ := Λ) h n
      (h.root ^ i • exteriorPower.ιMulti L (n + 1)
        (Fin.snoc (fun j => map Λ Λ K L (v j)) (D Λ L h.root))) =
      if i = p - 1 then
        exteriorPower.ιMulti K (n + 1) (Fin.snoc v (D Λ K a)) else 0 := by
  have hs := (exteriorPower.ιMulti L (n + 1)).toMultilinearMap.snoc_smul
    (fun j => map Λ Λ K L (v j)) (h.root ^ i) (D Λ L h.root)
  change exteriorPower.ιMulti L (n + 1)
    (Fin.snoc (fun j => map Λ Λ K L (v j)) (h.root ^ i • D Λ L h.root)) =
    h.root ^ i • exteriorPower.ιMulti L (n + 1)
      (Fin.snoc (fun j => map Λ Λ K L (v j)) (D Λ L h.root)) at hs
  exact (congrArg (pureDegreePTraceExterior (Λ := Λ) h n) hs.symm).trans
    (pureDegreePTraceExterior_root_pow h n v hi)

/-- The actual power basis has the antidiagonal differential pairing.
For i+j ≥ p the original relation z^p=a reduces to a lower, killed exponent. -/
theorem pureDegreePFieldTranspose_root_powers [Fact p.Prime]
    (h : IsAdjoinRootMonic L ((X : K[X]) ^ p - C a)) (n : ℕ)
    (v : Fin n → KaehlerDifferential Λ K) {i j : ℕ} (hi : i < p) (hj : j < p) :
    pureDegreePFieldTranspose (Λ := Λ) h n
      (h.root ^ i • exteriorPower.ιMulti L (n + 1)
        (Fin.snoc (fun k => map Λ Λ K L (v k)) (D Λ L h.root))) (h.root ^ j) =
      if i + j = p - 1 then
        exteriorPower.ιMulti K (n + 1) (Fin.snoc v (D Λ K a)) else 0 := by
  rw [pureDegreePFieldTranspose_apply, smul_smul, ← pow_add, Nat.add_comm j i]
  by_cases hij : i + j < p
  · exact fieldTrace_root_pow_smul h n v hij
  · have hp : 1 < p := (Fact.out : p.Prime).one_lt
    have hlow : i + j - p < p := by omega
    have hlowne : i + j - p ≠ p - 1 := by omega
    have hsumne : i + j ≠ p - 1 := by omega
    have hroot : h.root ^ p = algebraMap K L a := by
      simpa only [map_sub, map_pow, aeval_X, aeval_C, sub_eq_zero] using h.aeval_root_self
    have hreduce : h.root ^ (i + j) = algebraMap K L a * h.root ^ (i + j - p) := by
      rw [← hroot, ← pow_add]
      congr 1
      omega
    rw [hreduce, mul_smul, IsScalarTower.algebraMap_smul,
      (pureDegreePTraceExterior (Λ := Λ) h n).map_smul,
      fieldTrace_root_pow_smul h n v hlow]
    simp only [hlowne, hsumne, ite_false, smul_zero]

/-- Reversing the original root-power forms gives the exact dual-basis
normalization, with no unspecified scalar factor. -/
theorem pureDegreePFieldTranspose_dual_root_powers [Fact p.Prime]
    (h : IsAdjoinRootMonic L ((X : K[X]) ^ p - C a)) (n : ℕ)
    (v : Fin n → KaehlerDifferential Λ K) {i j : ℕ} (hi : i < p) (hj : j < p) :
    pureDegreePFieldTranspose (Λ := Λ) h n
      (h.root ^ (p - 1 - i) • exteriorPower.ιMulti L (n + 1)
        (Fin.snoc (fun k => map Λ Λ K L (v k)) (D Λ L h.root))) (h.root ^ j) =
      if i = j then exteriorPower.ιMulti K (n + 1) (Fin.snoc v (D Λ K a)) else 0 := by
  rw [pureDegreePFieldTranspose_root_powers h n v (by omega) hj]
  by_cases hij : i = j
  · subst j
    rw [ite_eq_left (by omega), ite_eq_left rfl]
  · rw [ite_eq_right (by omega), ite_eq_right hij]

/-- Generic duality follows from actual generic line dimensions and a nonzero
original wedge η∧da. No integral generator or unit condition is assumed. -/
theorem pureDegreePFieldTranspose_bijective [Fact p.Prime]
    (h : IsAdjoinRootMonic L ((X : K[X]) ^ p - C a)) (n : ℕ)
    (v : Fin n → KaehlerDifferential Λ K)
    (hv : exteriorPower.ιMulti K (n + 1) (Fin.snoc v (D Λ K a)) ≠ 0)
    (hQ : Module.finrank K ((Q n)) = 1) (hW : Module.finrank L ((W n)) = 1) :
    Function.Bijective (pureDegreePFieldTranspose (Λ := Λ) h n) := by
  let : Module.Finite K L := h.finite
  let β := exteriorPower.ιMulti L (n + 1)
    (Fin.snoc (fun i => map Λ Λ K L (v i)) (D Λ L h.root))
  apply LinearMap.smulTranspose_bijective_of_lines
    (pureDegreePTraceExterior (Λ := Λ) h n) β (h.root ^ (p - 1)) _ hQ hW
  have hnorm := fieldTrace_root_pow_smul (Λ := Λ) h n v
    (Nat.sub_lt (Fact.out : p.Prime).pos Nat.zero_lt_one)
  have he : pureDegreePTraceExterior (Λ := Λ) h n (h.root ^ (p - 1) • β) =
      exteriorPower.ιMulti K (n + 1) (Fin.snoc v (D Λ K a)) := by
    simpa only [ite_true] using hnorm
  rw [he]
  exact hv

end KaehlerDifferential
