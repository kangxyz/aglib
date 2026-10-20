/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Mathlib.Analysis.Normed.Field.Basic
public import Mathlib.Topology.Algebra.InfiniteSum.NatInt
public import Mathlib.Analysis.Normed.Ring.InfiniteSum
public import Mathlib.Analysis.Normed.Field.Ultra
public import Mathlib.Analysis.SpecificLimits.Normed
public import Mathlib.RingTheory.Localization.FractionRing
public import Mathlib.FieldTheory.IntermediateField.Basic
public import Mathlib.Tactic.Ring
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Positivity

/-!
# Bilateral Laurent series convergent at every positive radius

Source: `R5Lab.Aglib.Analysis.LaurentSeries.Global`,
revision `f8a3314ddecffcada2ec721d26d56a937bed9690`. The actual objects, maps, norm choices,
universes, and stated hypotheses are retained.
-/

@[expose] public section

noncomputable section
namespace LaurentSeries.AllRadii

universe u v
variable {F : Type u} [NormedField F]

/-- Absolute convergence on every positive real circle. -/
def Converges (c : ℤ → F) : Prop :=
  ∀ r : ℝ, 0 < r → Summable (fun n : ℤ => ‖c n‖ * r ^ n)

theorem converges_zero : Converges (0 : ℤ → F) := by
  intro r hr
  simp

theorem Converges.add {c d : ℤ → F} (hc : Converges c) (hd : Converges d) :
    Converges (c + d) := by
  intro r hr
  refine ((hc r hr).add (hd r hr)).of_nonneg_of_le (fun n => mul_nonneg (norm_nonneg _)
    (zpow_nonneg hr.le n)) ?_
  intro n
  simpa only [Pi.add_apply, ← add_mul] using
    mul_le_mul_of_nonneg_right (norm_add_le (c n) (d n)) (zpow_nonneg hr.le n)

theorem Converges.smul (a : F) {c : ℤ → F} (hc : Converges c) :
    Converges (a • c) := by
  intro r hr
  simpa only [Pi.smul_apply, smul_eq_mul, norm_mul, mul_assoc] using
    (hc r hr).mul_left ‖a‖

/-- The coefficient-defined space; it has genuine two-sided, unrestricted support. -/
def coefficientSpace (F : Type u) [NormedField F] : Submodule F (ℤ → F) where
  carrier := {c | Converges c}
  zero_mem' := converges_zero
  add_mem' := Converges.add
  smul_mem' := Converges.smul

/-- Bilateral coefficient functions absolutely summable with every positive-radius weight. -/
abbrev Series (F : Type u) [NormedField F] : Type u := ↥(coefficientSpace F)

namespace Series

instance : CoeFun (Series F) (fun _ => ℤ → F) := ⟨fun c => c.val⟩

@[ext] theorem ext {c d : Series F} (h : ∀ n, c n = d n) : c = d :=
  Subtype.ext (funext h)

theorem converges (c : Series F) : Converges (fun n => c n) := c.property

@[simp] theorem zero_apply (n : ℤ) : (0 : Series F) n = 0 := rfl
@[simp] theorem add_apply (c d : Series F) (n : ℤ) : (c + d) n = c n + d n := rfl
@[simp] theorem neg_apply (c : Series F) (n : ℤ) : (-c) n = -c n := rfl
@[simp] theorem smul_apply (a : F) (c : Series F) (n : ℤ) : (a • c) n = a * c n := rfl

theorem summable_norm (c : Series F) : Summable (fun n => ‖c n‖) := by
  simpa using (converges c) 1 zero_lt_one

/-- A single Laurent monomial, including negative powers. -/
def monomial (n : ℤ) (a : F) : Series F :=
  ⟨fun m => if m = n then a else 0, by
    intro r hr
    have := (hasSum_ite_eq n (‖a‖ * r ^ n)).summable
    convert this using 1
    ext m
    split_ifs with h <;> simp_all⟩

@[simp] theorem monomial_apply (n m : ℤ) (a : F) :
    monomial n a m = if m = n then a else 0 := rfl

/-- Actual pullback by multiplication of the Laurent variable by a unit. -/
def translate (v : Fˣ) : Series F →ₗ[F] Series F where
  toFun c := ⟨fun n => c n * (v : F) ^ n, by
    intro r hr
    convert (converges c) (‖(v : F)‖ * r) (mul_pos (norm_pos_iff.mpr v.ne_zero) hr) using 1
    ext n
    simp only [norm_mul, norm_zpow, mul_zpow, mul_assoc]⟩
  map_add' c d := by ext n; simp [add_mul]
  map_smul' a c := by ext n; simp [mul_assoc]

@[simp] theorem translate_apply (v : Fˣ) (c : Series F) (n : ℤ) :
    translate v c n = c n * (v : F) ^ n := rfl

@[simp] theorem translate_one (c : Series F) : translate 1 c = c := by
  ext n
  simp

@[simp] theorem translate_mul (v w : Fˣ) (c : Series F) :
    translate (v * w) c = translate v (translate w c) := by
  ext n
  simp only [translate_apply, Units.val_mul, mul_zpow]
  ring

/-- Translation is an actual coefficient-linear equivalence. -/
def translateEquiv (v : Fˣ) : Series F ≃ₗ[F] Series F where
  __ := translate v
  invFun := translate v⁻¹
  left_inv c := by change translate v⁻¹ (translate v c) = c; rw [← translate_mul]; simp
  right_inv c := by change translate v (translate v⁻¹ c) = c; rw [← translate_mul]; simp

/-- Positive integral substitution: coefficients outside `aℤ` are zero. -/
def powerCoefficients (a : ℕ) (c : ℤ → F) (m : ℤ) : F :=
  if (a : ℤ) ∣ m then c (m / a) else 0

@[simp] theorem powerCoefficients_mul (a : ℕ) (ha : 0 < a) (c : ℤ → F) (n : ℤ) :
    powerCoefficients a c ((a : ℤ) * n) = c n := by
  simp [powerCoefficients, Int.mul_ediv_cancel_left n (by omega : (a : ℤ) ≠ 0)]

theorem converges_powerCoefficients (a : ℕ) (ha : 0 < a) (c : Series F) :
    Converges (powerCoefficients a c) := by
  intro r hr
  let f : ℤ → ℤ := fun n => (a : ℤ) * n
  have hi : Function.Injective f := mul_right_injective₀ (by omega : (a : ℤ) ≠ 0)
  apply (hi.summable_iff ?_).mp
  · change Summable (fun n => ‖powerCoefficients a c ((a : ℤ) * n)‖ * r ^ ((a : ℤ) * n))
    simpa only [powerCoefficients_mul a ha, zpow_mul, zpow_natCast] using
      (converges c) (r ^ a) (pow_pos hr a)
  · intro m hm
    have h : ¬ (a : ℤ) ∣ m := by
      rintro ⟨n, rfl⟩
      exact hm ⟨n, rfl⟩
    simp [powerCoefficients, h]

/-- The actual positive-power substitution on the coefficient-defined space. -/
def power (a : ℕ) (ha : 0 < a) : Series F →ₗ[F] Series F where
  toFun c := ⟨powerCoefficients a c, converges_powerCoefficients a ha c⟩
  map_add' c d := by ext n; simp [powerCoefficients]; split_ifs <;> simp
  map_smul' c d := by ext n; simp [powerCoefficients]

@[simp] theorem power_apply (a : ℕ) (ha : 0 < a) (c : Series F) (n : ℤ) :
    power a ha c n = powerCoefficients a c n := rfl

theorem power_apply_mul (a : ℕ) (ha : 0 < a) (c : Series F) (n : ℤ) :
    power a ha c ((a : ℤ) * n) = c n := powerCoefficients_mul a ha c n

theorem power_injective (a : ℕ) (ha : 0 < a) :
    Function.Injective (power (F := F) a ha) := by
  intro c d h
  ext n
  simpa only [power_apply_mul] using congrArg (fun s : Series F => s ((a : ℤ) * n)) h

/-- Elementary translation/substitution compatibility, before any periodic quotient. -/
theorem translate_power (v : Fˣ) (a : ℕ) (ha : 0 < a) (c : Series F) :
    translate v (power a ha c) = power a ha (translate (v ^ a) c) := by
  ext n
  by_cases h : (a : ℤ) ∣ n
  · obtain ⟨m, rfl⟩ := h
    simp only [translate_apply, power_apply_mul, Units.val_pow_eq_pow_val]
    rw [zpow_mul, zpow_natCast]
  · simp [translate_apply, power_apply, powerCoefficients, h]


section Multiplication
variable [CompleteSpace F]

/-- Bilateral convolution, with actual convergence proved below. -/
def convolution (c d : Series F) (n : ℤ) : F := ∑' k : ℤ, c k * d (n - k)

omit [CompleteSpace F] in
@[nolint unusedArguments]
theorem summable_convolution_norm [CompleteSpace F] (c d : Series F) (n : ℤ) :
    Summable (fun k : ℤ => ‖c k * d (n - k)‖) := by
  exact ((summable_norm c).mul_norm (summable_norm d)).comp_injective
    (i := fun k : ℤ => (k, n - k)) (fun k l h => congrArg Prod.fst h)

theorem summable_convolution (c d : Series F) (n : ℤ) :
    Summable (fun k : ℤ => c k * d (n - k)) :=
  (summable_convolution_norm c d n).of_norm

omit [CompleteSpace F] in
/-- The summable majorant governing the full two-sided Cauchy product. -/
@[nolint unusedArguments]
theorem summable_weighted_pairs [CompleteSpace F] (c d : Series F) (r : ℝ) (hr : 0 < r) :
    Summable (fun z : ℤ × ℤ => ‖c z.2 * d (z.1 - z.2)‖ * r ^ z.1) := by
  have hs := ((converges c r hr).mul_of_nonneg (converges d r hr)
    (fun n => mul_nonneg (norm_nonneg _) (zpow_nonneg hr.le n))
    (fun n => mul_nonneg (norm_nonneg _) (zpow_nonneg hr.le n))).comp_injective
    (show Function.Injective (fun z : ℤ × ℤ => (z.2, z.1 - z.2)) from by
      intro x y h
      have h₁ := congrArg Prod.fst h
      have h₂ := congrArg Prod.snd h
      dsimp at h₁ h₂
      ext <;> omega)
  convert hs using 1
  ext z
  simp only [Function.comp_apply, norm_mul]
  have hp : r ^ z.2 * r ^ (z.1 - z.2) = r ^ z.1 := by
    rw [← zpow_add₀ hr.ne']; congr 1; omega
  calc
    ‖c z.2‖ * ‖d (z.1 - z.2)‖ * r ^ z.1 =
        ‖c z.2‖ * ‖d (z.1 - z.2)‖ * (r ^ z.2 * r ^ (z.1 - z.2)) := by rw [hp]
    _ = _ := by ring

theorem converges_convolution (c d : Series F) : Converges (convolution c d) := by
  intro r hr
  refine (summable_weighted_pairs c d r hr).prod.of_nonneg_of_le
    (fun n => mul_nonneg (norm_nonneg _) (zpow_nonneg hr.le n)) ?_
  intro n
  change ‖∑' k : ℤ, c k * d (n - k)‖ * r ^ n ≤
    ∑' k : ℤ, ‖c k * d (n - k)‖ * r ^ n
  rw [tsum_mul_right]
  exact mul_le_mul_of_nonneg_right
    (norm_tsum_le_tsum_norm (summable_convolution_norm c d n)) (zpow_nonneg hr.le n)

instance : Mul (Series F) := ⟨fun c d => ⟨convolution c d, converges_convolution c d⟩⟩
instance : One (Series F) := ⟨monomial 0 1⟩

@[simp] theorem mul_apply (c d : Series F) (n : ℤ) :
    (c * d) n = ∑' k : ℤ, c k * d (n - k) := rfl

omit [CompleteSpace F] in
@[simp, nolint unusedArguments] theorem one_apply [CompleteSpace F] (n : ℤ) : (1 : Series F) n =
  if n = 0 then 1 else 0
  := rfl

theorem mul_comm (c d : Series F) : c * d = d * c := by
  ext n
  change (∑' k : ℤ, c k * d (n - k)) = ∑' k : ℤ, d k * c (n - k)
  rw [← (Equiv.subLeft n).tsum_eq (fun k : ℤ => d k * c (n - k))]
  apply tsum_congr
  intro k
  simp [_root_.mul_comm]

theorem one_mul (c : Series F) : 1 * c = c := by
  ext n
  change (∑' k : ℤ, (if k = 0 then 1 else 0) * c (n - k)) = c n
  rw [tsum_eq_single 0 (fun k hk => by simp [hk])]
  simp

theorem mul_one (c : Series F) : c * 1 = c := by rw [mul_comm, one_mul]

theorem mul_zero (c : Series F) : c * 0 = 0 := by ext n; simp

theorem zero_mul (c : Series F) : 0 * c = 0 := by ext n; simp

theorem mul_add (c d e : Series F) : c * (d + e) = c * d + c * e := by
  ext n
  simp only [mul_apply, add_apply, _root_.mul_add]
  exact (summable_convolution c d n).tsum_add (summable_convolution c e n)

theorem add_mul (c d e : Series F) : (c + d) * e = c * e + d * e := by
  rw [mul_comm, mul_add, mul_comm e c, mul_comm e d]


omit [CompleteSpace F] in
/-- The absolutely summable triple Cauchy family needed for associativity. -/
@[nolint unusedArguments]
theorem summable_triple_norm [CompleteSpace F] (c d e : Series F) (n : ℤ) :
    Summable (fun z : ℤ × ℤ => ‖c z.1 * d z.2 * e (n - z.1 - z.2)‖) := by
  have hs := ((summable_norm c).mul_of_nonneg (summable_norm d)
    (fun _ => norm_nonneg _) (fun _ => norm_nonneg _)).mul_right (∑' k : ℤ, ‖e k‖)
  refine hs.of_nonneg_of_le (fun _ => norm_nonneg _) (fun z => ?_)
  simp only [norm_mul]
  exact mul_le_mul_of_nonneg_left
    ((summable_norm e).le_tsum (n - z.1 - z.2) (fun _ _ => norm_nonneg _))
    (mul_nonneg (norm_nonneg _) (norm_nonneg _))

theorem mul_assoc (c d e : Series F) : (c * d) * e = c * (d * e) := by
  ext n
  have hs : Summable (fun z : ℤ × ℤ => c z.2 * d (z.1 - z.2) * e (n - z.1)) := by
    have h := (summable_triple_norm c d e n).of_norm.comp_injective
      (i := fun z : ℤ × ℤ => (z.2, z.1 - z.2)) (by
        intro x y h
        have h₁ := congrArg Prod.fst h
        have h₂ := congrArg Prod.snd h
        dsimp at h₁ h₂
        ext <;> omega)
    convert h using 1
    ext z
    dsimp
    rw [show n - z.2 - (z.1 - z.2) = n - z.1 by omega]
  change (∑' k : ℤ, (∑' i : ℤ, c i * d (k - i)) * e (n - k)) =
    ∑' i : ℤ, c i * ∑' j : ℤ, d j * e (n - i - j)
  calc
    (∑' k : ℤ, (∑' i : ℤ, c i * d (k - i)) * e (n - k)) =
        ∑' k : ℤ, ∑' i : ℤ, c i * d (k - i) * e (n - k) := by simp only [tsum_mul_right]
    _ = ∑' i : ℤ, ∑' k : ℤ, c i * d (k - i) * e (n - k) := hs.tsum_comm.symm
    _ = ∑' i : ℤ, ∑' j : ℤ, c i * d j * e (n - i - j) := by
      apply tsum_congr
      intro i
      rw [← (Equiv.addLeft i).tsum_eq (fun k : ℤ => c i * d (k - i) * e (n - k))]
      apply tsum_congr
      intro j
      dsimp
      rw [show i + j - i = j by omega, show n - (i + j) = n - i - j by omega]
    _ = ∑' i : ℤ, c i * ∑' j : ℤ, d j * e (n - i - j) := by
      simp only [tsum_mul_left, _root_.mul_assoc]

instance : CommRing (Series F) where
  __ := (inferInstance : AddCommGroup (Series F))
  mul_assoc := mul_assoc
  one_mul := one_mul
  mul_one := mul_one
  left_distrib := mul_add
  right_distrib := add_mul
  zero_mul := zero_mul
  mul_zero := mul_zero
  mul_comm := mul_comm



instance : Algebra F (Series F) := Algebra.ofModule
  (fun a c d => by
    ext n
    simp only [mul_apply, smul_apply, _root_.mul_assoc, tsum_mul_left])
  (fun a c d => by
    ext n
    simp only [mul_apply, smul_apply]
    rw [← tsum_mul_left]
    apply tsum_congr
    intro k
    ring)

theorem algebraMap_apply (a : F) (n : ℤ) :
    algebraMap F (Series F) a n = if n = 0 then a else 0 := by
  rw [Algebra.algebraMap_eq_smul_one, smul_apply, one_apply]
  split_ifs <;> simp


@[simp] theorem algebraMap_eq_monomial (a : F) :
    algebraMap F (Series F) a = monomial 0 a := by
  ext n
  simp only [algebraMap_apply, monomial_apply]

theorem translate_mul_series (v : Fˣ) (c d : Series F) :
    translate v (c * d) = translate v c * translate v d := by
  ext n
  simp only [translate_apply, mul_apply]
  rw [← tsum_mul_right]
  apply tsum_congr
  intro k
  have hp : (v : F) ^ k * (v : F) ^ (n - k) = (v : F) ^ n := by
    rw [← zpow_add₀ v.ne_zero]
    congr 1
    omega
  calc
    c k * d (n - k) * (v : F) ^ n =
        c k * d (n - k) * ((v : F) ^ k * (v : F) ^ (n - k)) := by rw [hp]
    _ = _ := by ring

/-- Literal translation is an algebra automorphism of the Laurent ring. -/
def translateAlgEquiv (v : Fˣ) : Series F ≃ₐ[F] Series F where
  __ := translateEquiv v
  map_mul' := translate_mul_series v
  commutes' a := by
    ext n
    simp only [translateEquiv, algebraMap_apply]
    split_ifs with h <;> simp [h]

omit [CompleteSpace F] in
@[nolint unusedArguments]
theorem power_one_series [CompleteSpace F] (a : ℕ) (ha : 0 < a) : power (F := F) a ha 1 = 1 := by
  ext n
  by_cases h : (a : ℤ) ∣ n
  · obtain ⟨k, rfl⟩ := h
    simp only [power_apply_mul, one_apply]
    have : (a : ℤ) * k = 0 ↔ k = 0 := by
      simp only [mul_eq_zero, show (a : ℤ) ≠ 0 by omega, false_or]
    simp only [this]
  · have hn : n ≠ 0 := by rintro rfl; exact h (dvd_zero _)
    simp [power_apply, powerCoefficients, h, one_apply, hn]

theorem power_mul_series (a : ℕ) (ha : 0 < a) (c d : Series F) :
    power a ha (c * d) = power a ha c * power a ha d := by
  ext n
  by_cases hn : (a : ℤ) ∣ n
  · obtain ⟨m, rfl⟩ := hn
    simp only [power_apply_mul, mul_apply]
    let f : ℤ → ℤ := fun k => (a : ℤ) * k
    have hi : Function.Injective f := mul_right_injective₀ (by omega : (a : ℤ) ≠ 0)
    rw [← hi.tsum_eq (f := fun k => power a ha c k * power a ha d ((a : ℤ) * m - k)) (by
      intro k hk
      by_contra hkr
      have hknd : ¬ (a : ℤ) ∣ k := by
        rintro ⟨l, rfl⟩
        exact hkr ⟨l, rfl⟩
      exact hk (by simp [power_apply, powerCoefficients, hknd]))]
    apply tsum_congr
    intro k
    dsimp [f]
    rw [show (a : ℤ) * m - (a : ℤ) * k = (a : ℤ) * (m - k) by ring]
    simp only [powerCoefficients_mul a ha]
  · simp only [power_apply, powerCoefficients, ite_eq_right hn, mul_apply]
    symm
    trans ∑' _ : ℤ, (0 : F)
    · apply tsum_congr
      intro k
      by_cases hk : (a : ℤ) ∣ k
      · have hnk : ¬ (a : ℤ) ∣ n - k := by
          intro hnk
          exact hn (by simpa using dvd_add hk hnk)
        simp [hnk]
      · simp [hk]
    · exact tsum_zero

/-- Actual algebra pullback by a positive integral power. -/
def powerAlgHom (a : ℕ) (ha : 0 < a) : Series F →ₐ[F] Series F where
  toFun := power a ha
  map_zero' := map_zero (power a ha)
  map_one' := power_one_series a ha
  map_add' := map_add (power a ha)
  map_mul' := power_mul_series a ha
  commutes' c := by
    rw [Algebra.algebraMap_eq_smul_one, (power a ha).map_smul, power_one_series]

@[simp] theorem powerAlgHom_apply (a : ℕ) (ha : 0 < a) (c : Series F) :
    powerAlgHom a ha c = power a ha c := rfl

instance : Nontrivial (Series F) := by
  refine ⟨⟨0, 1, ?_⟩⟩
  intro h
  have := congrArg (fun c : Series F => c 0) h
  simp at this

omit [CompleteSpace F] in
/-- The last coefficient of maximum norm exists because the norm sequence tends to zero. -/
@[nolint unusedArguments]
theorem exists_last_max_norm [CompleteSpace F] (c : Series F) (hc : c ≠ 0) :
    ∃ i : ℤ, c i ≠ 0 ∧ (∀ k, ‖c k‖ ≤ ‖c i‖) ∧
      (∀ k, i < k → ‖c k‖ < ‖c i‖) := by
  classical
  obtain ⟨k₀, hk₀⟩ : ∃ k : ℤ, c k ≠ 0 := by
    by_contra h
    push Not at h
    exact hc (ext h)
  have hpos : 0 < ‖c k₀‖ := norm_pos_iff.mpr hk₀
  have hfin : {k : ℤ | ‖c k₀‖ ≤ ‖c k‖}.Finite := by
    simpa only [not_lt] using Filter.eventually_cofinite.mp
      ((summable_norm c).tendsto_cofinite_zero.eventually_lt_const hpos)
  let S := hfin.toFinset
  have hkS : k₀ ∈ S := by simp [S]
  obtain ⟨i, hiS, hi⟩ := S.exists_max_image (fun k => ‖c k‖) ⟨k₀, hkS⟩
  have hbound : ∀ k, ‖c k‖ ≤ ‖c i‖ := by
    intro k
    by_cases hk : k ∈ S
    · exact hi k hk
    · have hsmall : ‖c k‖ < ‖c k₀‖ := by simpa [S] using hk
      exact hsmall.le.trans (hi k₀ hkS)
  let T := S.filter (fun k => ‖c k‖ = ‖c i‖)
  have hiT : i ∈ T := by simp [T, hiS]
  obtain ⟨j, hjT, hj⟩ := T.exists_max_image (fun k => k) ⟨i, hiT⟩
  have hjnorm : ‖c j‖ = ‖c i‖ := (Finset.mem_filter.mp hjT).2
  have hjpos : 0 < ‖c j‖ := by rw [hjnorm]; exact hpos.trans_le (hi k₀ hkS)
  refine ⟨j, norm_pos_iff.mp hjpos, (fun k => by rw [hjnorm]; exact hbound k), ?_⟩
  intro k hjk
  apply lt_of_le_of_ne (by rw [hjnorm]; exact hbound k)
  intro heq
  have hkS : k ∈ S := by
    simp only [S, Set.Finite.mem_toFinset, Set.mem_ofPred_eq]
    rw [heq, hjnorm]
    exact hi k₀ hkS
  have hkT : k ∈ T := Finset.mem_filter.mpr ⟨hkS, heq.trans hjnorm⟩
  exact (not_le_of_gt hjk) (hj k hkT)

omit [CompleteSpace F] in
/-- A single strictly dominant term in an ultrametric convergent sum cannot cancel.
The open ball is also a closed additive subgroup, so no uniform gap premise is needed. -/
@[nolint unusedArguments]
theorem tsum_ne_zero_of_strict_dominant [CompleteSpace F] [IsUltrametricDist F]
    {f : ℤ → F} (hf : Summable f) (i : ℤ) (hi : f i ≠ 0)
    (hdom : ∀ k, k ≠ i → ‖f k‖ < ‖f i‖) : (∑' k, f k) ≠ 0 := by
  classical
  let B := IsUltrametricDist.ball_openAddSubgroup F (norm_pos_iff.mpr hi)
  have hmem : ∀ k : ℤ, (if k = i then 0 else f k) ∈ B := by
    intro k
    by_cases hk : k = i
    · simp only [ite_eq_left hk]; exact B.zero_mem
    · simp only [ite_eq_right hk]
      change dist (f k) 0 < ‖f i‖
      simpa only [dist_zero_right] using hdom k hk
  have hsum : (∑' k, f k) - f i ∈ B := by
    apply B.isClosed.mem_of_tendsto (hasSum_ite_sub_hasSum hf.hasSum i)
    apply Filter.Eventually.of_forall
    intro s
    exact sum_mem (fun k _ => hmem k)
  intro hz
  have hlt : ‖(∑' k, f k) - f i‖ < ‖f i‖ := by
    change dist ((∑' k, f k) - f i) 0 < ‖f i‖ at hsum
    simpa only [dist_zero_right] using hsum
  simp [hz] at hlt

/-- No-zero-divisors is proved directly from actual coefficients and convolution. -/
theorem mul_ne_zero [IsUltrametricDist F] {c d : Series F} (hc : c ≠ 0) (hd : d ≠ 0) :
    c * d ≠ 0 := by
  obtain ⟨i, hi0, hi, hi'⟩ := exists_last_max_norm c hc
  obtain ⟨j, hj0, hj, hj'⟩ := exists_last_max_norm d hd
  have hposc : 0 < ‖c i‖ := norm_pos_iff.mpr hi0
  have hposd : 0 < ‖d j‖ := norm_pos_iff.mpr hj0
  have hterm : c i * d (i + j - i) ≠ 0 := by
    simpa using _root_.mul_ne_zero hi0 hj0
  have hconv : (c * d) (i + j) ≠ 0 := by
    apply tsum_ne_zero_of_strict_dominant (summable_convolution c d (i + j)) i hterm
    intro k hki
    simp only [norm_mul, add_sub_cancel_left]
    rcases lt_or_gt_of_ne hki with hki | hik
    · have hlt : ‖d (i + j - k)‖ < ‖d j‖ := hj' _ (by omega)
      exact (mul_le_mul_of_nonneg_right (hi k) (norm_nonneg _)).trans_lt
        (mul_lt_mul_of_pos_left hlt hposc)
    · exact (mul_le_mul_of_nonneg_left (hj (i + j - k)) (norm_nonneg _)).trans_lt
        (mul_lt_mul_of_pos_right (hi' k hik) hposd)
  intro h
  apply hconv
  rw [h, zero_apply]

instance [IsUltrametricDist F] : NoZeroDivisors (Series F) :=
  ⟨fun {c d} h => by
    by_cases hc : c = 0
    · exact Or.inl hc
    · exact Or.inr (by by_contra hd; exact mul_ne_zero hc hd h)⟩

instance [IsUltrametricDist F] : IsDomain (Series F) := NoZeroDivisors.to_isDomain _

end Multiplication


section Evaluation
variable {K : Type v} [NormedField K] [CompleteSpace K]
variable (f : F →+* K) [RingHomIsometric f]

/-- Actual convergent evaluation on a norm-compatible complete extension.
This is only evaluation of Laurent series; no evaluation of the entire fraction field is
  asserted. -/
def evaluate (u : Kˣ) (c : Series F) : K := ∑' n : ℤ, f (c n) * (u : K) ^ n

omit [CompleteSpace K] in
@[nolint unusedArguments]
theorem summable_evaluate_norm [CompleteSpace K] (u : Kˣ) (c : Series F) :
    Summable (fun n : ℤ => ‖f (c n) * (u : K) ^ n‖) := by
  simpa only [norm_mul, norm_zpow, RingHomIsometric.norm_map] using
    converges c ‖(u : K)‖ (norm_pos_iff.mpr u.ne_zero)

theorem summable_evaluate (u : Kˣ) (c : Series F) :
    Summable (fun n : ℤ => f (c n) * (u : K) ^ n) :=
  (summable_evaluate_norm f u c).of_norm

omit [CompleteSpace K] [RingHomIsometric f] in
@[simp, nolint unusedArguments] theorem evaluate_zero [CompleteSpace K] [RingHomIsometric f] (u
  : Kˣ) : evaluate f u (0
  : Series F) = 0 := by
  simp [evaluate]

@[simp] theorem evaluate_add (u : Kˣ) (c d : Series F) :
    evaluate f u (c + d) = evaluate f u c + evaluate f u d := by
  simp only [evaluate, add_apply, map_add, _root_.add_mul]
  exact (summable_evaluate f u c).tsum_add (summable_evaluate f u d)

omit [CompleteSpace K] [RingHomIsometric f] in
@[simp, nolint unusedArguments] theorem evaluate_monomial [CompleteSpace K] [RingHomIsometric f]
  (u : Kˣ) (n : ℤ) (a : F) :
    evaluate f u (monomial n a) = f a * (u : K) ^ n := by
  unfold evaluate
  rw [tsum_eq_single n (fun k hk => by simp [hk])]
  simp

omit [CompleteSpace K] [RingHomIsometric f] in
/-- Coefficient power insertion is genuinely precomposition by `u ↦ u^a`. -/
@[nolint unusedArguments]
theorem evaluate_power [CompleteSpace K] [RingHomIsometric f] (u : Kˣ) (a : ℕ) (ha : 0 < a) (c :
  Series F) :
    evaluate f u (power a ha c) = evaluate f (u ^ a) c := by
  let g : ℤ → ℤ := fun n => (a : ℤ) * n
  have hi : Function.Injective g := mul_right_injective₀ (by omega : (a : ℤ) ≠ 0)
  unfold evaluate
  rw [← hi.tsum_eq (f := fun n : ℤ => f (power a ha c n) * (u : K) ^ n) (by
    intro k hk
    by_contra hkr
    have hknd : ¬ (a : ℤ) ∣ k := by
      rintro ⟨l, rfl⟩
      exact hkr ⟨l, rfl⟩
    exact hk (by simp [power_apply, powerCoefficients, hknd]))]
  apply tsum_congr
  intro n
  change f (power a ha c ((a : ℤ) * n)) * (u : K) ^ ((a : ℤ) * n) = _
  simp only [power_apply_mul, zpow_mul, zpow_natCast, Units.val_pow_eq_pow_val]

omit [CompleteSpace K] [RingHomIsometric f] in
/-- Translation is genuinely precomposition by multiplication in the extension. -/
@[nolint unusedArguments]
theorem evaluate_translate [CompleteSpace K] [RingHomIsometric f] (u : Kˣ) (v : Fˣ) (c : Series F) :
    evaluate f u (translate v c) = evaluate f (u * Units.map f.toMonoidHom v) c := by
  unfold evaluate
  apply tsum_congr
  intro n
  simp only [translate_apply, map_mul, map_zpow₀, Units.val_mul, Units.coe_map, mul_zpow]
  change f (c n) * f (v : F) ^ n * (u : K) ^ n =
    f (c n) * ((u : K) ^ n * f (v : F) ^ n)
  ring

variable [CompleteSpace F]

/-- Explicit reindexing for the two-sided Cauchy product. -/
def sumPairEquiv : (ℤ × ℤ) ≃ (ℤ × ℤ) where
  toFun z := (z.1 + z.2, z.1)
  invFun z := (z.2, z.1 - z.2)
  left_inv z := by (ext <;> dsimp); omega
  right_inv z := by (ext <;> dsimp); omega

@[simp] theorem evaluate_mul (u : Kˣ) (c d : Series F) :
    evaluate f u (c * d) = evaluate f u c * evaluate f u d := by
  let g : ℤ × ℤ → K := fun z =>
    (f (c z.1) * (u : K) ^ z.1) * (f (d z.2) * (u : K) ^ z.2)
  have hs : Summable g := summable_mul_of_summable_norm
    (f := fun n : ℤ => f (c n) * (u : K) ^ n)
    (g := fun n : ℤ => f (d n) * (u : K) ^ n)
    (summable_evaluate_norm f u c) (summable_evaluate_norm f u d)
  have hs' := hs.comp_injective sumPairEquiv.symm.injective
  change (∑' n : ℤ, f ((c * d) n) * (u : K) ^ n) = _
  calc
    (∑' n : ℤ, f ((c * d) n) * (u : K) ^ n) =
        ∑' n : ℤ, ∑' k : ℤ, g (k, n - k) := by
      apply tsum_congr
      intro n
      rw [mul_apply, (summable_convolution c d n).map_tsum f f.isometry.continuous,
        ← tsum_mul_right]
      apply tsum_congr
      intro k
      dsimp [g]
      rw [map_mul]
      have hp : (u : K) ^ k * (u : K) ^ (n - k) = (u : K) ^ n := by
        rw [← zpow_add₀ u.ne_zero]
        congr 1
        omega
      rw [← hp]
      ring
    _ = ∑' z : ℤ × ℤ, g (sumPairEquiv.symm z) := hs'.tsum_prod.symm
    _ = ∑' z : ℤ × ℤ, g z := sumPairEquiv.symm.tsum_eq g
    _ = evaluate f u c * evaluate f u d :=
      (tsum_mul_tsum_of_summable_norm
        (summable_evaluate_norm f u c) (summable_evaluate_norm f u d)).symm

/-- The actual series evaluation homomorphism. -/
def evaluationHom (u : Kˣ) : Series F →+* K where
  toFun := evaluate f u
  map_zero' := evaluate_zero f u
  map_one' := by
    change evaluate f u (monomial 0 1) = 1
    simpa only [map_one, zpow_zero, _root_.mul_one] using evaluate_monomial f u 0 1
  map_add' := evaluate_add f u
  map_mul' := evaluate_mul f u


/-- Evaluation as an algebra homomorphism for a norm-compatible extension. -/
def evaluationAlgHom [Algebra F K] [RingHomIsometric (algebraMap F K)] (u : Kˣ) :
    Series F →ₐ[F] K where
  __ := evaluationHom (algebraMap F K) u
  commutes' a := by
    change evaluate (algebraMap F K) u (algebraMap F (Series F) a) = algebraMap F K a
    rw [algebraMap_eq_monomial, evaluate_monomial]
    simp

end Evaluation

end Series

section Fractions
variable [CompleteSpace F] [IsUltrametricDist F]

/-- The fraction field of the constructed bilateral Laurent domain. -/
abbrev Meromorphic (F : Type u) [NormedField F] [CompleteSpace F] := FractionRing (Series F)

/-- The extension of literal variable translation to the fraction field. -/
def meromorphicTranslate (v : Fˣ) : Meromorphic F ≃ₐ[F] Meromorphic F :=
  IsFractionRing.algEquivOfAlgEquiv (Series.translateAlgEquiv v)

omit [IsUltrametricDist F] in
@[simp, nolint unusedArguments] theorem meromorphicTranslate_algebraMap [IsUltrametricDist F] (v
  : Fˣ) (c : Series F) :
    meromorphicTranslate v (algebraMap (Series F) (Meromorphic F) c) =
      algebraMap (Series F) (Meromorphic F) (Series.translate v c) :=
  IsFractionRing.algEquivOfAlgEquiv_algebraMap (Series.translateAlgEquiv v) c

/-- Positive-power pullback extended using its proved coefficient injectivity. -/
def meromorphicPower (a : ℕ) (ha : 0 < a) : Meromorphic F →ₐ[F] Meromorphic F :=
  IsFractionRing.liftAlgHom (g :=
    (IsScalarTower.toAlgHom F (Series F) (Meromorphic F)).comp (Series.powerAlgHom a ha))
    ((IsFractionRing.injective (Series F) (Meromorphic F)).comp (Series.power_injective a ha))

@[simp] theorem meromorphicPower_algebraMap (a : ℕ) (ha : 0 < a) (c : Series F) :
    meromorphicPower a ha (algebraMap (Series F) (Meromorphic F) c) =
      algebraMap (Series F) (Meromorphic F) (Series.power a ha c) := by
  exact IsFractionRing.lift_algebraMap
    (g := ((IsScalarTower.toAlgHom F (Series F) (Meromorphic F)).comp
      (Series.powerAlgHom a ha)).toRingHom)
    ((IsFractionRing.injective (Series F) (Meromorphic F)).comp (Series.power_injective a ha)) c

@[simp] theorem meromorphicTranslate_one (m : Meromorphic F) : meromorphicTranslate 1 m = m := by
  obtain ⟨x, y, hy, rfl⟩ := IsFractionRing.div_surjective (Series F) m
  simp [map_div₀]

theorem meromorphicTranslate_mul (v w : Fˣ) (m : Meromorphic F) :
    meromorphicTranslate (v * w) m = meromorphicTranslate v (meromorphicTranslate w m) := by
  obtain ⟨x, y, hy, rfl⟩ := IsFractionRing.div_surjective (Series F) m
  simp only [map_div₀, meromorphicTranslate_algebraMap, Series.translate_mul]

theorem meromorphicTranslate_power (v : Fˣ) (a : ℕ) (ha : 0 < a) (m : Meromorphic F) :
    meromorphicTranslate v (meromorphicPower a ha m) =
      meromorphicPower a ha (meromorphicTranslate (v ^ a) m) := by
  obtain ⟨x, y, hy, rfl⟩ := IsFractionRing.div_surjective (Series F) m
  simp only [map_div₀, meromorphicPower_algebraMap, meromorphicTranslate_algebraMap,
    Series.translate_power]

/-- Literal fixed functions of the period translation, with their inherited field operations. -/
def periodicField (q : Fˣ) : IntermediateField F (Meromorphic F) where
  __ := (meromorphicTranslate q).toRingHom.eqLocusField (RingHom.id _)
  algebraMap_mem' a := (meromorphicTranslate q).commutes a

@[simp] theorem mem_periodicField (q : Fˣ) (m : Meromorphic F) :
    m ∈ periodicField q ↔ meromorphicTranslate q m = m := Iff.rfl

theorem periodic_pow (q : Fˣ) (b : ℕ) {m : Meromorphic F} (hm : m ∈ periodicField q) :
    m ∈ periodicField (q ^ b) := by
  change meromorphicTranslate (q ^ b) m = m
  induction b with
  | zero => simp
  | succ b hb => rw [pow_succ, meromorphicTranslate_mul, show meromorphicTranslate q m = m from
    hm, hb]

theorem meromorphicPower_mem_periodicField (p q : Fˣ) (a b : ℕ) (ha : 0 < a)
    (h : p ^ a = q ^ b) {m : Meromorphic F} (hm : m ∈ periodicField q) :
    meromorphicPower a ha m ∈ periodicField p := by
  change meromorphicTranslate p (meromorphicPower a ha m) = meromorphicPower a ha m
  rw [meromorphicTranslate_power, h, show meromorphicTranslate (q ^ b) m = m from periodic_pow q
    b hm]

/-- The actual pullback on periodic meromorphic fields from a literal period relation. -/
def periodicPower (p q : Fˣ) (a b : ℕ) (ha : 0 < a) (h : p ^ a = q ^ b) :
    periodicField q →ₐ[F] periodicField p where
  toFun m := ⟨meromorphicPower a ha m, meromorphicPower_mem_periodicField p q a b ha h m.property⟩
  map_zero' := Subtype.ext (map_zero _)
  map_one' := Subtype.ext (map_one _)
  map_add' _ _ := Subtype.ext (map_add _ _ _)
  map_mul' _ _ := Subtype.ext (map_mul _ _ _)
  commutes' a := Subtype.ext ((meromorphicPower _ _).commutes a)

@[simp] theorem periodicPower_coe (p q : Fˣ) (a b : ℕ) (ha : 0 < a)
    (h : p ^ a = q ^ b) (m : periodicField q) :
    (periodicPower p q a b ha h m : Meromorphic F) = meromorphicPower a ha m := rfl


theorem periodicPower_injective (p q : Fˣ) (a b : ℕ) (ha : 0 < a) (h : p ^ a = q ^ b) :
    Function.Injective (periodicPower p q a b ha h) := (periodicPower p q a b ha h).injective

end Fractions

end LaurentSeries.AllRadii

end


noncomputable section
noncomputable section
noncomputable section
noncomputable section
noncomputable section
/-! ## ConvergenceEquivalence -/

noncomputable section
namespace LaurentSeries.AllRadii
universe u
variable {F : Type u} [NormedField F]

/-- The intrinsic coefficient-decay condition for an everywhere-convergent
nonarchimedean Laurent series, at all positive real radii. -/
def AllRadiiDecay (c : ℤ → F) : Prop :=
  ∀ r : ℝ, 0 < r → Filter.Tendsto (fun n : ℤ => ‖c n‖ * r ^ n)
    Filter.cofinite (nhds 0)

theorem Converges.allRadiiDecay {c : ℤ → F} (hc : Converges c) : AllRadiiDecay c :=
  fun r hr => (hc r hr).tendsto_cofinite_zero

/-- A bound at a larger radius gives real absolute summability at the smaller
radius by a genuine geometric majorant. -/
theorem summable_weighted_nat_of_bound (c : ℕ → F) (r R B : ℝ)
    (hr : 0 < r) (hR : r < R) (hB : ∀ n : ℕ, ‖c n‖ * R ^ n ≤ B) :
    Summable (fun n : ℕ => ‖c n‖ * r ^ n) := by
  have hR0 : 0 < R := hr.trans hR
  have hs : Summable (fun n : ℕ => B * (r / R) ^ n) :=
    (summable_geometric_of_lt_one (div_nonneg hr.le hR0.le)
      ((div_lt_one hR0).mpr hR)).mul_left B
  apply Summable.of_nonneg_of_le (fun n => mul_nonneg (norm_nonneg _) (pow_nonneg hr.le n)) _ hs
  intro n
  calc
    ‖c n‖ * r ^ n = (‖c n‖ * R ^ n) * (r / R) ^ n := by
      rw [div_pow]
      field_simp
    _ ≤ B * (r / R) ^ n := mul_le_mul_of_nonneg_right (hB n)
      (pow_nonneg (div_nonneg hr.le hR0.le) n)

/-- Decay at every radius gives the stronger weighted real summability used by
our constructed ring. Both tails are controlled at a strictly different radius. -/
theorem AllRadiiDecay.converges {c : ℤ → F} (hc : AllRadiiDecay c) : Converges c := by
  intro r hr
  rw [summable_int_iff_summable_nat_and_neg]
  constructor
  · obtain ⟨B, hB⟩ := (hc (2 * r) (by positivity)).bddAbove_range_of_cofinite
    simpa only [zpow_natCast] using
      summable_weighted_nat_of_bound (fun n : ℕ => c (n : ℤ)) r (2 * r) B hr
        (by linarith) (fun n => by simpa using hB (Set.mem_range_self (n : ℤ)))
  · obtain ⟨B, hB⟩ := (hc (r / 2) (by positivity)).bddAbove_range_of_cofinite
    have hn : ∀ n : ℕ, ‖c (-(n : ℤ))‖ * (2 / r) ^ n ≤ B := by
      intro n
      have h := hB (Set.mem_range_self (-(n : ℤ)))
      simpa only [zpow_neg, zpow_natCast, ← inv_pow, inv_div] using h
    have hs := summable_weighted_nat_of_bound (fun n : ℕ => c (-(n : ℤ))) r⁻¹ (2 / r) B
      (inv_pos.mpr hr) (by rw [inv_eq_one_div]; exact div_lt_div_of_pos_right (by norm_num) hr) hn
    simpa only [zpow_neg, zpow_natCast, inv_pow] using hs

/-- Exact source-ring identification, not merely an implication tested on
rational units of the original base field. -/
theorem converges_iff_allRadiiDecay (c : ℤ → F) : Converges c ↔ AllRadiiDecay c :=
  ⟨Converges.allRadiiDecay, AllRadiiDecay.converges⟩

end LaurentSeries.AllRadii

end

/-! ## EverywhereConvergence -/

noncomputable section
namespace LaurentSeries.AllRadii
universe u
variable {F K : Type u} [NormedField F] [CompleteSpace F] [CharZero F]
  [IsUltrametricDist F] [NormedField K] [CompleteSpace K] [CharZero K]
  [IsUltrametricDist K]

/-- Literal convergence of the bilateral Laurent series at every nonzero point
of a specified norm-compatible complete extension. This is a convergence
predicate, not the false claim that vanishing on base-field points is faithful. -/
def EverywhereConvergent (f : F →+* K) (c : ℤ → F) : Prop :=
  ∀ w : Kˣ, Summable (fun n : ℤ => f (c n) * (w : K) ^ n)

omit [CompleteSpace F] [CharZero F] [IsUltrametricDist F] [CompleteSpace K] [CharZero K] in
/-- Convergence at all extension units forces weighted coefficient bounds;
this uses convergence of the literal series, not cancellation of its value. -/
@[nolint unusedArguments]
theorem EverywhereConvergent.weight_bound [CompleteSpace F] [CharZero F] [IsUltrametricDist F]
  [CompleteSpace K] [CharZero K] (f : F →+* K) [RingHomIsometric f]
    {c : ℤ → F} (hc : EverywhereConvergent f c) (w : Kˣ) :
    ∃ B : ℝ, ∀ n : ℤ, ‖c n‖ * ‖(w : K)‖ ^ n ≤ B := by
  have ht : Filter.Tendsto (fun n : ℤ => ‖f (c n) * (w : K) ^ n‖)
      Filter.cofinite (nhds 0) := by
    simpa only [norm_zero] using (hc w).tendsto_cofinite_zero.norm
  obtain ⟨B, hB⟩ := ht.bddAbove_range_of_cofinite
  refine ⟨B, fun n => ?_⟩
  simpa only [norm_mul, norm_zpow, RingHomIsometric.norm_map] using hB (Set.mem_range_self n)

end LaurentSeries.AllRadii

end

end
end
end
end
end
