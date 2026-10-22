/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.RingTheory.Blowup.WeakTransform
public import Aglib.RingTheory.Blowup.RegularPair.Reciprocal
public import Aglib.RingTheory.Localization.MinimalQuotientLength
public import Mathlib.Algebra.Module.Submodule.Equiv
public import Mathlib.Algebra.Polynomial.Eval.Degree
public import Mathlib.Algebra.Polynomial.Lifts
public import Mathlib.LinearAlgebra.Isomorphisms
public import Mathlib.RingTheory.Artinian.Ring
public import Mathlib.RingTheory.Polynomial.Basic
public import Mathlib.RingTheory.Regular.IsSMulRegular
public import Mathlib.RingTheory.Spectrum.Prime.RingHom
public import Mathlib.RingTheory.TensorProduct.Quotient
public import Mathlib.Tactic.LinearCombination

/-!
# Parameter powers and contraction from a saturated chart

For a regular pair `a, b`, multiplication by `a` cancels one power of the
actual ideal `(a,b)`. A denominator normal form in the original saturated
chart then proves contraction of every exceptional power. In particular,
finite-colength ideals have an actual finite order, detected by extension to
the same chart. The numerical colength decrease requires further arguments.
-/

@[expose] public section

noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

namespace Ideal

variable {A : Type u} [CommRing A]

private theorem sup_pow_succ_decomposition (I J : Ideal A) (n : ℕ) :
    (I ⊔ J) ^ (n + 1) = I * (I ⊔ J) ^ n ⊔ J ^ (n + 1) := by
  induction n with
  | zero => simp
  | succ n ih =>
    have h : J ^ (n + 1) * I ≤ I * (I ⊔ J) ^ (n + 1) := by
      rw [mul_comm]
      exact Ideal.mul_mono_right (Ideal.pow_right_mono le_sup_right (n + 1))
    calc
      (I ⊔ J) ^ (n + 1 + 1) =
          (I * (I ⊔ J) ^ n ⊔ J ^ (n + 1)) * (I ⊔ J) := by
            rw [pow_succ, ih]
      _ = (I * (I ⊔ J) ^ (n + 1) ⊔ J ^ (n + 1) * I) ⊔
          J ^ (n + 1 + 1) := by
            rw [Ideal.sup_mul, mul_assoc, ← pow_succ, Ideal.mul_sup,
              ← pow_succ, ← sup_assoc]
      _ = I * (I ⊔ J) ^ (n + 1) ⊔ J ^ (n + 1 + 1) := by
        rw [sup_eq_left.mpr h]

/-- Separating the pure second-parameter term from a power of a two-generated ideal. -/
theorem span_pair_pow_succ_decomposition (a b : A) (n : ℕ) :
    (Ideal.span {a, b}) ^ (n + 1) =
      Ideal.span {a} * (Ideal.span {a, b}) ^ n ⊔ Ideal.span {b ^ (n + 1)} := by
  simpa only [Ideal.span_insert, Ideal.span_singleton_pow] using
    sup_pow_succ_decomposition (Ideal.span {a}) (Ideal.span {b}) n

/-- A regular first parameter cancels exactly one power of the parameter ideal. -/
theorem mul_mem_span_pair_pow_succ_iff (a b : A)
    (ha : IsSMulRegular A a) (hb : IsSMulRegular (A ⧸ Ideal.span {a}) b)
    (n : ℕ) (x : A) :
    a * x ∈ (Ideal.span {a, b}) ^ (n + 1) ↔
      x ∈ (Ideal.span {a, b}) ^ n := by
  constructor
  · intro hx
    rw [span_pair_pow_succ_decomposition] at hx
    obtain ⟨u, hu, v, hv, huv⟩ := Submodule.mem_sup.mp hx
    obtain ⟨y, hy, rfl⟩ := Ideal.mem_span_singleton_mul.mp hu
    obtain ⟨c, hc⟩ := Ideal.mem_span_singleton.mp hv
    have hbc : b ^ (n + 1) * c ∈ Ideal.span {a} := by
      apply Ideal.mem_span_singleton.mpr
      refine ⟨x - y, ?_⟩
      rw [← hc]
      linear_combination huv
    have hc' : c ∈ Ideal.span {a} :=
      (isSMulRegular_quotient_iff_mem_of_smul_mem (Ideal.span {a}) (b ^ (n + 1))).mp
        (hb.pow (n + 1)) c hbc
    obtain ⟨d, hd⟩ := Ideal.mem_span_singleton.mp hc'
    have hxy : x = y + b ^ (n + 1) * d := by
      apply ha
      change a * x = a * (y + b ^ (n + 1) * d)
      rw [hc, hd] at huv
      linear_combination -huv
    rw [hxy]
    apply (Ideal.span {a, b} ^ n).add_mem hy
    apply (Ideal.span {a, b} ^ n).mul_mem_right
    exact Ideal.pow_le_pow_right (Nat.le_succ n)
      (Ideal.pow_mem_pow (Ideal.subset_span (by simp)) (n + 1))
  · intro hx
    rw [pow_succ']
    exact Ideal.mul_mem_mul (Ideal.subset_span (by simp)) hx

/-- The principal colon form of parameter-power cancellation. -/
theorem span_pair_pow_succ_colon (a b : A)
    (ha : IsSMulRegular A a) (hb : IsSMulRegular (A ⧸ Ideal.span {a}) b)
    (n : ℕ) :
    ((Ideal.span {a, b}) ^ (n + 1)).colon {a} = (Ideal.span {a, b}) ^ n := by
  ext x
  simpa only [Submodule.mem_colon_singleton, smul_eq_mul, mul_comm] using
    mul_mem_span_pair_pow_succ_iff a b ha hb n x

/-- Iterated cancellation retains the exact exponent of the original parameter ideal. -/
theorem pow_mul_mem_span_pair_pow_add_iff (a b : A)
    (ha : IsSMulRegular A a) (hb : IsSMulRegular (A ⧸ Ideal.span {a}) b)
    (n r : ℕ) (x : A) :
    a ^ n * x ∈ (Ideal.span {a, b}) ^ (n + r) ↔
      x ∈ (Ideal.span {a, b}) ^ r := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [pow_succ', mul_assoc, Nat.succ_add, Nat.succ_eq_add_one,
      mul_mem_span_pair_pow_succ_iff a b ha hb]
    exact ih

/-- A proper regular parameter ideal has strictly nonzero graded parameter powers. -/
theorem parameter_pow_not_mem_span_pair_pow_succ (a b : A)
    (ha : IsSMulRegular A a) (hb : IsSMulRegular (A ⧸ Ideal.span {a}) b)
    (hproper : Ideal.span {a, b} ≠ ⊤) (n : ℕ) :
    a ^ n ∉ (Ideal.span {a, b}) ^ (n + 1) := by
  intro hn
  have h : (1 : A) ∈ (Ideal.span {a, b}) ^ 1 :=
    (pow_mul_mem_span_pair_pow_add_iff a b ha hb n 1 1).mp (by simpa using hn)
  exact hproper ((Ideal.eq_top_iff_one (Ideal.span {a, b})).mpr (by simpa using h))

private theorem exists_order_of_not_le_pow_succ (I J : Ideal A) (N : ℕ)
    (hN : ¬ J ≤ I ^ (N + 1)) :
    ∃ r ≤ N, J ≤ I ^ r ∧ ¬ J ≤ I ^ (r + 1) := by
  induction N with
  | zero => exact ⟨0, le_rfl, by simp, hN⟩
  | succ N ih =>
    by_cases h : J ≤ I ^ (N + 1)
    · exact ⟨N + 1, le_rfl, h, hN⟩
    · obtain ⟨r, hr, hJr, hJr'⟩ := ih h
      exact ⟨r, hr.trans (Nat.le_succ N), hJr, hJr'⟩

/-- A finite-colength ideal has a unique actual order for a proper regular
parameter ideal. The upper bound is the supplied centre-power containment. -/
theorem exists_unique_parameter_order (a b : A)
    (ha : IsSMulRegular A a) (hb : IsSMulRegular (A ⧸ Ideal.span {a}) b)
    (hproper : Ideal.span {a, b} ≠ ⊤) (J : Ideal A) {N : ℕ}
    (hN : (Ideal.span {a, b}) ^ N ≤ J) :
    ∃! r : ℕ, ∀ n : ℕ, J ≤ (Ideal.span {a, b}) ^ n ↔ n ≤ r := by
  have hbound : ¬ J ≤ (Ideal.span {a, b}) ^ (N + 1) := by
    intro h
    exact parameter_pow_not_mem_span_pair_pow_succ a b ha hb hproper N
      (h (hN (Ideal.pow_mem_pow (Ideal.subset_span (by simp)) N)))
  obtain ⟨r, hr, hJr, hJr'⟩ :=
    exists_order_of_not_le_pow_succ (Ideal.span {a, b}) J N hbound
  have hspec : ∀ n, J ≤ (Ideal.span {a, b}) ^ n ↔ n ≤ r := by
    intro n
    constructor
    · intro hn
      by_contra hnr
      exact hJr' (hn.trans (Ideal.pow_le_pow_right (Nat.succ_le_of_lt
        (Nat.lt_of_not_ge hnr))))
    · intro hn
      exact hJr.trans (Ideal.pow_le_pow_right hn)
  refine ⟨r, hspec, ?_⟩
  intro s hs
  exact le_antisymm ((hspec s).mp ((hs s).mpr le_rfl)) ((hs r).mp hJr)

/-- A proper finite-colength ideal contained in the parameter ideal has a
positive actual order, with both the upper bound and maximality proved. -/
theorem exists_positive_parameter_order (a b : A)
    (ha : IsSMulRegular A a) (hb : IsSMulRegular (A ⧸ Ideal.span {a}) b)
    (hproper : Ideal.span {a, b} ≠ ⊤) (J : Ideal A) {N : ℕ}
    (hN : (Ideal.span {a, b}) ^ N ≤ J) (hJ : J ≤ Ideal.span {a, b}) :
    ∃ r : ℕ, 0 < r ∧ r ≤ N ∧ J ≤ (Ideal.span {a, b}) ^ r ∧
      ¬ J ≤ (Ideal.span {a, b}) ^ (r + 1) := by
  obtain ⟨r, hspec, _⟩ := exists_unique_parameter_order a b ha hb hproper J hN
  have hJr := (hspec r).mpr le_rfl
  have hr : 0 < r := (hspec 1).mp (by simpa using hJ)
  have hrN : r ≤ N := by
    by_contra h
    exact parameter_pow_not_mem_span_pair_pow_succ a b ha hb hproper N
      (Ideal.pow_le_pow_right (Nat.succ_le_of_lt (Nat.lt_of_not_ge h))
        (hJr (hN (Ideal.pow_mem_pow (Ideal.subset_span (by simp)) N))))
  exact ⟨r, hr, hrN, hJr, fun h => Nat.not_succ_le_self r ((hspec (r + 1)).mp h)⟩

end Ideal

namespace Localization.Away

variable {A : Type u} [CommRing A]

/-- Every element of the literal saturated chart has a numerator in the
matching power of the original centre ideal. -/
theorem saturatedChart_exists_power_numerator (I : Ideal A) (a : A) (ha : a ∈ I)
    (z : saturatedChart A I a) :
    ∃ (n : ℕ) (g : A), g ∈ I ^ n ∧
      (z : Localization.Away a) * (algebraMap A (Localization.Away a) a) ^ n =
        algebraMap A (Localization.Away a) g := by
  rcases z with ⟨z, hz⟩
  change z ∈ Algebra.adjoin A _ at hz
  induction hz using Algebra.adjoin_induction with
  | mem x hx =>
    obtain ⟨g, hg, rfl⟩ := hx
    exact ⟨1, g, by simpa using hg,
      by simpa only [pow_one, fraction] using fraction_mul_self a g⟩
  | algebraMap g => exact ⟨0, g, by simp, by simp⟩
  | add x y hx hy ihx ihy =>
    obtain ⟨n, g, hg, hgn⟩ := ihx
    obtain ⟨m, h, hh, hhm⟩ := ihy
    refine ⟨n + m, g * a ^ m + h * a ^ n, ?_, ?_⟩
    · rw [pow_add]
      apply (I ^ n * I ^ m).add_mem
      · exact Ideal.mul_mem_mul hg (Ideal.pow_mem_pow ha m)
      · exact Ideal.mul_mem_mul_rev (Ideal.pow_mem_pow ha n) hh
    · calc
        (x + y) * (algebraMap A (Localization.Away a) a) ^ (n + m) =
            (x * (algebraMap A (Localization.Away a) a) ^ n) *
              (algebraMap A (Localization.Away a) a) ^ m +
            (y * (algebraMap A (Localization.Away a) a) ^ m) *
              (algebraMap A (Localization.Away a) a) ^ n := by rw [pow_add]; ring
        _ = algebraMap A (Localization.Away a) (g * a ^ m + h * a ^ n) := by
          rw [hgn, hhm]
          simp only [map_add, map_mul, map_pow]
  | mul x y hx hy ihx ihy =>
    obtain ⟨n, g, hg, hgn⟩ := ihx
    obtain ⟨m, h, hh, hhm⟩ := ihy
    refine ⟨n + m, g * h, ?_, ?_⟩
    · rw [pow_add]
      exact Ideal.mul_mem_mul hg hh
    · calc
        (x * y) * (algebraMap A (Localization.Away a) a) ^ (n + m) =
            (x * (algebraMap A (Localization.Away a) a) ^ n) *
            (y * (algebraMap A (Localization.Away a) a) ^ m) := by rw [pow_add]; ring
        _ = algebraMap A (Localization.Away a) (g * h) := by rw [hgn, hhm, map_mul]

/-- The original parameter-ideal power is exactly the contraction of the
exceptional power in the literal saturated chart. -/
theorem comap_exceptional_pow_eq_span_pair_pow (a b : A)
    (ha : IsSMulRegular A a) (hb : IsSMulRegular (A ⧸ Ideal.span {a}) b) (r : ℕ) :
    (Ideal.span {(algebraMap A (saturatedChart A (Ideal.span {a, b}) a) a) ^ r}).comap
        (algebraMap A (saturatedChart A (Ideal.span {a, b}) a)) =
      (Ideal.span {a, b}) ^ r := by
  let I : Ideal A := Ideal.span {a, b}
  let C := saturatedChart A I a
  let L := Localization.Away a
  have haI : a ∈ I := Ideal.subset_span (by simp)
  have hleft : IsLeftRegular a := ha
  have hreg : IsRegular a := ⟨hleft, hleft.right_of_commute (fun _ => mul_comm _ _)⟩
  have hinj : Function.Injective (algebraMap A L) :=
    IsLocalization.injectiveₛ (S := L) (M := Submonoid.powers a)
      (by rintro _ ⟨n, rfl⟩; exact hreg.pow n)
  apply le_antisymm
  · intro x hx
    change algebraMap A C x ∈ Ideal.span {(algebraMap A C a) ^ r} at hx
    obtain ⟨z, hz⟩ := Ideal.mem_span_singleton.mp hx
    obtain ⟨n, g, hg, hgn⟩ := saturatedChart_exists_power_numerator I a haI z
    have hz' : algebraMap A L x = (algebraMap A L a) ^ r * (z : L) := by
      simpa only [Subalgebra.coe_mul, Subalgebra.coe_pow, Subalgebra.coe_algebraMap] using
        congrArg (fun z : C => (z : L)) hz
    have hnum : a ^ n * x = a ^ r * g := by
      apply hinj
      calc
        algebraMap A L (a ^ n * x) =
            (algebraMap A L a) ^ r * ((z : L) * (algebraMap A L a) ^ n) := by
              rw [map_mul, map_pow, hz']
              ring
        _ = algebraMap A L (a ^ r * g) := by rw [hgn, map_mul, map_pow]
    apply (Ideal.pow_mul_mem_span_pair_pow_add_iff a b ha hb n r x).mp
    rw [hnum, add_comm, pow_add]
    exact Ideal.mul_mem_mul (Ideal.pow_mem_pow haI r) hg
  · intro x hx
    change algebraMap A C x ∈ Ideal.span {(algebraMap A C a) ^ r}
    rw [← map_center_pow_eq_span I a r haI]
    exact Ideal.mem_map_of_mem _ hx

/-- Extension to the actual chart detects every original parameter-ideal order. -/
theorem map_le_exceptional_pow_iff (a b : A)
    (ha : IsSMulRegular A a) (hb : IsSMulRegular (A ⧸ Ideal.span {a}) b)
    (J : Ideal A) (r : ℕ) :
    J.map (algebraMap A (saturatedChart A (Ideal.span {a, b}) a)) ≤
        Ideal.span {(algebraMap A (saturatedChart A (Ideal.span {a, b}) a) a) ^ r} ↔
      J ≤ (Ideal.span {a, b}) ^ r := by
  rw [Ideal.map_le_iff_le_comap, comap_exceptional_pow_eq_span_pair_pow a b ha hb r]

/-- At the actual order the weak transform is not contained in the exceptional
ideal. Thus its image in the original exceptional fibre is nonzero. -/
theorem weakTransform_not_le_exceptional (a b : A)
    (ha : IsSMulRegular A a) (hb : IsSMulRegular (A ⧸ Ideal.span {a}) b)
    (J : Ideal A) (r : ℕ) (hJ : J ≤ (Ideal.span {a, b}) ^ r)
    (hnext : ¬ J ≤ (Ideal.span {a, b}) ^ (r + 1)) :
    ¬ weakTransform (Ideal.span {a, b}) J a r ≤
      Ideal.span {algebraMap A (saturatedChart A (Ideal.span {a, b}) a) a} := by
  intro hK
  apply hnext
  apply (map_le_exceptional_pow_iff a b ha hb J (r + 1)).mp
  rw [← exceptional_pow_mul_weakTransform (Ideal.span {a, b}) J a r
    (Ideal.subset_span (by simp)) hJ]
  calc
    _ ≤ Ideal.span {(algebraMap A (saturatedChart A (Ideal.span {a, b}) a) a) ^ r} *
        Ideal.span {algebraMap A (saturatedChart A (Ideal.span {a, b}) a) a} :=
      Ideal.mul_mono_right hK
    _ = _ := by rw [Ideal.span_singleton_mul_span_singleton, ← pow_succ]

end Localization.Away

namespace Ideal

variable {R : Type*} [CommRing R]

/-- An Artinian quotient has finite support in the original prime spectrum. -/
theorem zeroLocus_finite_of_quotient_artinian (K : Ideal R)
    [IsArtinianRing (R ⧸ K)] : (PrimeSpectrum.zeroLocus (K : Set R)).Finite := by
  have h := Set.finite_range (PrimeSpectrum.comap (Ideal.Quotient.mk K))
  rw [_root_.range_comap_of_surjective (R ⧸ K) (Ideal.Quotient.mk K)
    Ideal.Quotient.mk_surjective] at h
  simpa only [Ideal.mk_ker] using h

private theorem prime_isMaximal_of_artinian_quotient (K P : Ideal R)
    [IsArtinianRing (R ⧸ K)] [P.IsPrime] (hKP : K ≤ P) : P.IsMaximal := by
  let Q : Ideal (R ⧸ K) := P.map (Ideal.Quotient.mk K)
  let : Q.IsPrime := Ideal.isPrime_map_quotientMk_of_isPrime hKP
  have hmax : (Q.comap (Ideal.Quotient.mk K)).IsMaximal :=
    Ideal.comap_isMaximal_of_surjective _ Ideal.Quotient.mk_surjective
  simpa only [Q, Ideal.comap_map_mk hKP] using hmax

/-- The original quotient by the extended ideal in the actual prime localization. -/
abbrev quotientAtPrime (K P : Ideal R) [P.IsPrime] :=
  Localization.AtPrime P ⧸ K.map (algebraMap R (Localization.AtPrime P))

/-- Every actual local quotient of an Artinian quotient has finite length. -/
theorem finiteLength_localized_quotient_of_artinian (K P : Ideal R)
    [IsArtinianRing (R ⧸ K)] [P.IsPrime] (hKP : K ≤ P) :
    IsFiniteLength (Localization.AtPrime P)
      (Localization.AtPrime P ⧸ K.map (algebraMap R (Localization.AtPrime P))) := by
  have hmin : P ∈ K.minimalPrimes := by
    refine ⟨⟨inferInstance, hKP⟩, ?_⟩
    intro Q hQ hQP
    let : Q.IsPrime := hQ.1
    have hmax := prime_isMaximal_of_artinian_quotient K Q hQ.2
    exact (hmax.eq_of_le (inferInstance : P.IsPrime).ne_top hQP).ge
  apply Module.length_ne_top_iff.mp
  have hlen := (Algebra.TensorProduct.quotIdealMapEquivTensorQuot
    (Localization.AtPrime P) K).toLinearEquiv.length_eq
  rw [hlen]
  exact Module.length_localized_quotient_ne_top K P hmin

end Ideal

namespace Ideal

variable {R : Type*} [CommRing R]

/-- A prime above an exceptional-power-torsion ideal is maximal if the
exceptional quotient is a domain and a principal ideal ring and the ideal
has a nonzero image in that quotient. -/
theorem isMaximal_of_exceptional_power (e : R) (K P : Ideal R) [P.IsPrime]
    [IsDomain (R ⧸ Ideal.span {e})]
    [IsPrincipalIdealRing (R ⧸ Ideal.span {e})]
    {N : ℕ} (hN : e ^ N ∈ K) (hKP : K ≤ P)
    (hK : ¬ K ≤ Ideal.span {e}) : P.IsMaximal := by
  let E : Ideal R := Ideal.span {e}
  have heP : e ∈ P := (inferInstance : P.IsPrime).mem_of_pow_mem N (hKP hN)
  have hEP : E ≤ P := (Ideal.span_singleton_le_iff_mem P).mpr heP
  let Q : Ideal (R ⧸ E) := P.map (Ideal.Quotient.mk E)
  let : Q.IsPrime := Ideal.isPrime_map_quotientMk_of_isPrime hEP
  have hQ : Q ≠ ⊥ := by
    intro hzero
    have hPE : P ≤ E := by
      simpa only [Ideal.mk_ker] using
        (Ideal.map_eq_bot_iff_le_ker (Ideal.Quotient.mk E)).mp hzero
    exact hK (hKP.trans hPE)
  let : Q.IsMaximal := _root_.IsPrime.to_maximal_ideal hQ
  have hmax : (Q.comap (Ideal.Quotient.mk E)).IsMaximal :=
    Ideal.comap_isMaximal_of_surjective _ Ideal.Quotient.mk_surjective
  simpa only [Q, Ideal.comap_map_mk hEP] using hmax

/-- Noetherianity upgrades the exceptional-fibre calculation to an actual
Artinian quotient, not merely a finite set of selected primes. -/
theorem isArtinian_quotient_of_exceptional_power [IsNoetherianRing R]
    (e : R) (K : Ideal R)
    [IsDomain (R ⧸ Ideal.span {e})]
    [IsPrincipalIdealRing (R ⧸ Ideal.span {e})]
    {N : ℕ} (hN : e ^ N ∈ K) (hK : ¬ K ≤ Ideal.span {e}) :
    IsArtinianRing (R ⧸ K) := by
  let : Ring.KrullDimLE 0 (R ⧸ K) := Ring.KrullDimLE.mk₀ fun p hp => by
    let : p.IsPrime := hp
    let P : Ideal R := p.comap (Ideal.Quotient.mk K)
    have hKP : K ≤ P := by
      intro x hx
      change Ideal.Quotient.mk K x ∈ p
      rw [Ideal.Quotient.eq_zero_iff_mem.mpr hx]
      exact p.zero_mem
    let : P.IsMaximal := isMaximal_of_exceptional_power e K P hN hKP hK
    have hker : RingHom.ker (Ideal.Quotient.mk K) ≤ P := by
      simpa only [Ideal.mk_ker] using hKP
    have hmax : (P.map (Ideal.Quotient.mk K)).IsMaximal :=
      Ideal.IsMaximal.map_of_surjective_of_ker_le Ideal.Quotient.mk_surjective hker
    simpa only [P, Ideal.map_comap_of_surjective _ Ideal.Quotient.mk_surjective] using hmax
  exact IsNoetherianRing.isArtinianRing_of_krullDimLE_zero

end Ideal

namespace Localization.Away

variable {A : Type*} [CommRing A]

/-- The actual saturated regular-pair chart is Noetherian over a Noetherian base. -/
theorem pairChart_isNoetherian [IsNoetherianRing A] (a b : A)
    (ha : IsSMulRegular A a) (hb : IsSMulRegular (A ⧸ Ideal.span {a}) b) :
    IsNoetherianRing (saturatedChart A (Ideal.span {a, b}) a) :=
  isNoetherianRing_of_ringEquiv (pairQuotient a b) (pairChartEquiv a b ha hb).toRingEquiv

/-- At the actual parameter-ideal order the chart quotient by the genuine
weak transform is Artinian. The parameter ideal is required to be maximal. -/
theorem weakTransform_quotient_isArtinian [IsNoetherianRing A] (a b : A)
    (ha : IsSMulRegular A a) (hb : IsSMulRegular (A ⧸ Ideal.span {a}) b)
    (hmax : (Ideal.span {a, b}).IsMaximal) (J : Ideal A) (r N : ℕ)
    (hJ : J ≤ (Ideal.span {a, b}) ^ r)
    (hnext : ¬ J ≤ (Ideal.span {a, b}) ^ (r + 1))
    (hN : (Ideal.span {a, b}) ^ N ≤ J) (hrN : r ≤ N) :
    IsArtinianRing (saturatedChart A (Ideal.span {a, b}) a ⧸
      weakTransform (Ideal.span {a, b}) J a r) := by
  let I : Ideal A := Ideal.span {a, b}
  let C := saturatedChart A I a
  let e : C := algebraMap A C a
  let K : Ideal C := weakTransform I J a r
  let : I.IsMaximal := hmax
  let := Ideal.Quotient.field I
  let : IsNoetherianRing C := pairChart_isNoetherian a b ha hb
  let ef : (C ⧸ Ideal.span {e}) ≃+* Polynomial (A ⧸ I) :=
    (Ideal.quotEquivOfEq (map_center_eq_span I a (Ideal.subset_span (by simp))).symm).trans
      (pairChartFibreEquiv a b ha hb).toRingEquiv
  let : IsDomain (C ⧸ Ideal.span {e}) := ef.toMulEquiv.isDomain _
  let : IsPrincipalIdealRing (C ⧸ Ideal.span {e}) :=
    IsPrincipalIdealRing.of_surjective ef.symm.toRingHom ef.symm.surjective
  exact Ideal.isArtinian_quotient_of_exceptional_power e K
    (exceptional_pow_mem_weakTransform I J a r (Ideal.subset_span (by simp)) hN hrN)
    (weakTransform_not_le_exceptional a b ha hb J r hJ hnext)

/-- The support in the actual saturated chart is finite. -/
theorem weakTransform_zeroLocus_finite [IsNoetherianRing A] (a b : A)
    (ha : IsSMulRegular A a) (hb : IsSMulRegular (A ⧸ Ideal.span {a}) b)
    (hmax : (Ideal.span {a, b}).IsMaximal) (J : Ideal A) (r N : ℕ)
    (hJ : J ≤ (Ideal.span {a, b}) ^ r)
    (hnext : ¬ J ≤ (Ideal.span {a, b}) ^ (r + 1))
    (hN : (Ideal.span {a, b}) ^ N ≤ J) (hrN : r ≤ N) :
    (PrimeSpectrum.zeroLocus (weakTransform (Ideal.span {a, b}) J a r :
      Set (saturatedChart A (Ideal.span {a, b}) a))).Finite := by
  let K := weakTransform (Ideal.span {a, b}) J a r
  let := weakTransform_quotient_isArtinian a b ha hb hmax J r N hJ hnext hN hrN
  exact Ideal.zeroLocus_finite_of_quotient_artinian K

/-- Every point in the support of the actual chart transform is closed. -/
theorem weakTransform_support_isMaximal [IsNoetherianRing A] (a b : A)
    (ha : IsSMulRegular A a) (hb : IsSMulRegular (A ⧸ Ideal.span {a}) b)
    (hmax : (Ideal.span {a, b}).IsMaximal) (J : Ideal A) (r N : ℕ)
    (hJ : J ≤ (Ideal.span {a, b}) ^ r)
    (hnext : ¬ J ≤ (Ideal.span {a, b}) ^ (r + 1))
    (hN : (Ideal.span {a, b}) ^ N ≤ J) (hrN : r ≤ N)
    (P : Ideal (saturatedChart A (Ideal.span {a, b}) a)) [P.IsPrime]
    (hKP : weakTransform (Ideal.span {a, b}) J a r ≤ P) : P.IsMaximal := by
  let := weakTransform_quotient_isArtinian a b ha hb hmax J r N hJ hnext hN hrN
  exact Ideal.prime_isMaximal_of_artinian_quotient _ P hKP

/-- The genuine weak transform has finite colength in each actual local chart
ring at a point of its support. -/
theorem weakTransform_localized_finiteLength [IsNoetherianRing A] (a b : A)
    (ha : IsSMulRegular A a) (hb : IsSMulRegular (A ⧸ Ideal.span {a}) b)
    (hmax : (Ideal.span {a, b}).IsMaximal) (J : Ideal A) (r N : ℕ)
    (hJ : J ≤ (Ideal.span {a, b}) ^ r)
    (hnext : ¬ J ≤ (Ideal.span {a, b}) ^ (r + 1))
    (hN : (Ideal.span {a, b}) ^ N ≤ J) (hrN : r ≤ N)
    (P : Ideal (saturatedChart A (Ideal.span {a, b}) a)) [P.IsPrime]
    (hKP : weakTransform (Ideal.span {a, b}) J a r ≤ P) :
    IsFiniteLength (Localization.AtPrime P)
      (Ideal.quotientAtPrime (weakTransform (Ideal.span {a, b}) J a r) P) := by
  let := weakTransform_quotient_isArtinian a b ha hb hmax J r N hJ hnext hN hrN
  exact Ideal.finiteLength_localized_quotient_of_artinian _ P hKP

end Localization.Away

namespace Submodule

variable {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M]

/-- Surjectivity modulo a nilpotent scalar lifts without a finite-generation premise. -/
theorem eq_top_of_nilpotent_lifting (P : Submodule R M) (a : R) (N : ℕ)
    (hN : ∀ x : M, a ^ N • x = 0)
    (hlift : ∀ x : M, ∃ y : M, x - a • y ∈ P) : P = ⊤ := by
  have H : ∀ n : ℕ, ∀ x : M, ∃ y : M, x - a ^ n • y ∈ P := by
    intro n
    induction n with
    | zero => intro x; exact ⟨x, by simp⟩
    | succ n ih =>
      intro x
      obtain ⟨y, hy⟩ := ih x
      obtain ⟨z, hz⟩ := hlift y
      refine ⟨z, ?_⟩
      have h := P.add_mem hy (P.smul_mem (a ^ n) hz)
      simpa only [smul_sub, sub_add_sub_cancel, pow_succ, mul_smul] using h
  apply eq_top_iff.mpr
  intro x hx
  obtain ⟨y, hy⟩ := H N x
  simpa only [hN, sub_zero] using hy

end Submodule

namespace Localization.Away

variable {A : Type*} [CommRing A]

/-- The literal second-to-first parameter ratio in its original saturated chart. -/
abbrev parameterChartRatio (a b : A) : saturatedChart A (Ideal.span {a, b}) a :=
  ⟨fraction a b, fraction_mem (Ideal.span {a, b}) a b (Ideal.subset_span (by simp))⟩

theorem parameterChartRatio_relation (a b : A) :
    algebraMap A (saturatedChart A (Ideal.span {a, b}) a) a * parameterChartRatio a b =
      algebraMap A (saturatedChart A (Ideal.span {a, b}) a) b := by
  apply Subtype.ext
  change algebraMap A (Localization.Away a) a * fraction a b =
    algebraMap A (Localization.Away a) b
  simpa only [mul_comm] using fraction_mul_self a b

/-- Actual division by an exceptional power, as an A-linear map on the
corresponding original centre-ideal power. -/
def chartPowerDivision (I : Ideal A) (a : A) (r : ℕ) (ha : a ∈ I) :
    ↥(I ^ r) →ₗ[A] saturatedChart A I a :=
  LinearMap.codRestrictOfInjective
    ((Algebra.linearMap A (saturatedChart A I a)).domRestrict (I ^ r))
    (LinearMap.mul A (saturatedChart A I a)
      ((algebraMap A (saturatedChart A I a) a) ^ r))
    (exceptional_pow_mul_injective I a r) (by
      intro x
      have hx : algebraMap A (saturatedChart A I a) x ∈
          Ideal.span {(algebraMap A (saturatedChart A I a) a) ^ r} := by
        rw [← map_center_pow_eq_span I a r ha]
        exact Ideal.mem_map_of_mem _ x.property
      obtain ⟨y, hy⟩ := Ideal.mem_span_singleton.mp hx
      exact ⟨y, hy.symm⟩)

theorem exceptional_pow_mul_chartPowerDivision (I : Ideal A) (a : A) (r : ℕ)
    (ha : a ∈ I) (x : ↥(I ^ r)) :
    (algebraMap A (saturatedChart A I a) a) ^ r * chartPowerDivision I a r ha x =
      algebraMap A (saturatedChart A I a) (x : A) := by
  change (LinearMap.mul A (saturatedChart A I a)
      ((algebraMap A (saturatedChart A I a) a) ^ r))
      (chartPowerDivision I a r ha x) =
    ((Algebra.linearMap A (saturatedChart A I a)).domRestrict (I ^ r)) x
  unfold chartPowerDivision
  exact LinearMap.codRestrictOfInjective_comp_apply _ _ _ _ x

/-- Multiplication by the actual exceptional power characterizes the division map. -/
theorem chartPowerDivision_eq_of_mul_eq (I : Ideal A) (a : A) (r : ℕ)
    (ha : a ∈ I) (x : ↥(I ^ r)) (z : saturatedChart A I a)
    (hz : (algebraMap A (saturatedChart A I a) a) ^ r * z =
      algebraMap A (saturatedChart A I a) (x : A)) :
    chartPowerDivision I a r ha x = z :=
  exceptional_pow_mul_injective I a r
    ((exceptional_pow_mul_chartPowerDivision I a r ha x).trans hz.symm)

/-- The division map into the actual quotient by the weak transform. -/
def weakTransformDivision (I J : Ideal A) (a : A) (r : ℕ) (ha : a ∈ I) :
    ↥(I ^ r) →ₗ[A] (saturatedChart A I a ⧸ weakTransform I J a r) :=
  ((weakTransform I J a r).mkQ.restrictScalars A).comp (chartPowerDivision I a r ha)

theorem weakTransformDivision_eq_zero (I J : Ideal A) (a : A) (r : ℕ)
    (ha : a ∈ I) (x : ↥(I ^ r)) (hx : (x : A) ∈ J) :
    weakTransformDivision I J a r ha x = 0 := by
  change Ideal.Quotient.mk (weakTransform I J a r) (chartPowerDivision I a r ha x) = 0
  apply Ideal.Quotient.eq_zero_iff_mem.mpr
  apply (mem_weakTransform I J a r).mpr
  rw [exceptional_pow_mul_chartPowerDivision]
  exact Ideal.mem_map_of_mem _ hx

/-- Dividing a parameter-ideal power produces a polynomial of at most the
original degree in the literal chart ratio. -/
theorem exists_bounded_polynomial_division (a b : A) (r : ℕ) (x : A)
    (hx : x ∈ (Ideal.span {a, b}) ^ r) :
    ∃ p : Polynomial A, p.natDegree ≤ r ∧
      algebraMap A (saturatedChart A (Ideal.span {a, b}) a) x =
        (algebraMap A (saturatedChart A (Ideal.span {a, b}) a) a) ^ r *
          p.eval₂ (algebraMap A (saturatedChart A (Ideal.span {a, b}) a))
            (parameterChartRatio a b) := by
  induction r generalizing x with
  | zero => exact ⟨Polynomial.C x, by simp, by simp⟩
  | succ r ih =>
    rw [Ideal.span_pair_pow_succ_decomposition] at hx
    obtain ⟨u, hu, v, hv, huv⟩ := Submodule.mem_sup.mp hx
    obtain ⟨y, hy, rfl⟩ := Ideal.mem_span_singleton_mul.mp hu
    obtain ⟨c, hc⟩ := Ideal.mem_span_singleton.mp hv
    obtain ⟨p, hp, hpy⟩ := ih y hy
    refine ⟨p + Polynomial.C c * Polynomial.X ^ (r + 1), ?_, ?_⟩
    · apply Polynomial.natDegree_add_le_of_degree_le (hp.trans (Nat.le_succ r))
      exact (Polynomial.natDegree_C_mul_le _ _).trans (Polynomial.natDegree_X_pow_le _)
    · rw [← huv, hc]
      simp only [map_add, map_mul, map_pow, Polynomial.eval₂_add, Polynomial.eval₂_mul,
        Polynomial.eval₂_C, Polynomial.eval₂_pow, Polynomial.eval₂_X]
      rw [hpy, ← parameterChartRatio_relation a b, mul_pow]
      ring

end Localization.Away

namespace Localization.Away

variable {A : Type*} [CommRing A]

/-- The original saturated chart map to its polynomial exceptional fibre. -/
def parameterChartFibreMap (a b : A)
    (ha : IsSMulRegular A a) (hb : IsSMulRegular (A ⧸ Ideal.span {a}) b) :
    saturatedChart A (Ideal.span {a, b}) a →ₐ[A] Polynomial (A ⧸ Ideal.span {a, b}) :=
  (pairChartFibreEquiv a b ha hb).toAlgHom.comp
    (Ideal.Quotient.mkₐ A ((Ideal.span {a, b}).map
      (algebraMap A (saturatedChart A (Ideal.span {a, b}) a))))

theorem parameterChartFibreMap_surjective (a b : A)
    (ha : IsSMulRegular A a) (hb : IsSMulRegular (A ⧸ Ideal.span {a}) b) :
    Function.Surjective (parameterChartFibreMap a b ha hb) :=
  (pairChartFibreEquiv a b ha hb).surjective.comp (Ideal.Quotient.mkₐ_surjective A _)

theorem parameterChartFibreMap_eq_zero_iff (a b : A)
    (ha : IsSMulRegular A a) (hb : IsSMulRegular (A ⧸ Ideal.span {a}) b)
    (z : saturatedChart A (Ideal.span {a, b}) a) :
    parameterChartFibreMap a b ha hb z = 0 ↔
      z ∈ Ideal.span {algebraMap A (saturatedChart A (Ideal.span {a, b}) a) a} := by
  change pairChartFibreEquiv a b ha hb (Ideal.Quotient.mk _ z) = 0 ↔ _
  rw [← map_center_eq_span (Ideal.span {a, b}) a (Ideal.subset_span (by simp))]
  constructor
  · intro h
    apply Ideal.Quotient.eq_zero_iff_mem.mp
    apply (pairChartFibreEquiv a b ha hb).injective
    simpa only [map_zero] using h
  · intro h
    rw [Ideal.Quotient.eq_zero_iff_mem.mpr h, map_zero]

theorem parameterChartFibreMap_ratio (a b : A)
    (ha : IsSMulRegular A a) (hb : IsSMulRegular (A ⧸ Ideal.span {a}) b) :
    parameterChartFibreMap a b ha hb (parameterChartRatio a b) = Polynomial.X := by
  have heq : pairChartEquiv a b ha hb (pairCoordinate a b) = parameterChartRatio a b := by
    apply Subtype.ext
    exact pairChartEquiv_coordinate a b ha hb
  rw [← heq]
  exact pairChartFibreEquiv_coordinate a b ha hb

theorem parameterChartFibreMap_base (a b : A)
    (ha : IsSMulRegular A a) (hb : IsSMulRegular (A ⧸ Ideal.span {a}) b) (x : A) :
    parameterChartFibreMap a b ha hb
        (algebraMap A (saturatedChart A (Ideal.span {a, b}) a) x) =
      Polynomial.C (Ideal.Quotient.mk (Ideal.span {a, b}) x) :=
  (parameterChartFibreMap a b ha hb).commutes x

/-- Evaluation in the original chart becomes coefficient reduction in the
actual polynomial exceptional fibre. -/
theorem parameterChartFibreMap_eval (a b : A)
    (ha : IsSMulRegular A a) (hb : IsSMulRegular (A ⧸ Ideal.span {a}) b)
    (p : Polynomial A) :
    parameterChartFibreMap a b ha hb
        (p.eval₂ (algebraMap A (saturatedChart A (Ideal.span {a, b}) a))
          (parameterChartRatio a b)) =
      p.map (Ideal.Quotient.mk (Ideal.span {a, b})) := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq => simp only [Polynomial.eval₂_add, map_add, Polynomial.map_add, hp, hq]
  | monomial n c =>
    simp only [Polynomial.eval₂_monomial, map_mul, map_pow,
      parameterChartFibreMap_base, parameterChartFibreMap_ratio, Polynomial.map_monomial,
      Polynomial.C_mul_X_pow_eq_monomial]

/-- The actual transform has a nonzero initial polynomial of degree at most
the original ideal order. -/
theorem exists_bounded_initial_polynomial (a b : A)
    (ha : IsSMulRegular A a) (hb : IsSMulRegular (A ⧸ Ideal.span {a}) b)
    (J : Ideal A) (r : ℕ) (hJ : J ≤ (Ideal.span {a, b}) ^ r)
    (hnext : ¬ J ≤ (Ideal.span {a, b}) ^ (r + 1)) :
    ∃ h : Polynomial (A ⧸ Ideal.span {a, b}), h ≠ 0 ∧ h.natDegree ≤ r ∧
      h ∈ (weakTransform (Ideal.span {a, b}) J a r).map
        (parameterChartFibreMap a b ha hb).toRingHom := by
  obtain ⟨x, hxJ, hxnext⟩ := SetLike.not_le_iff_exists.mp hnext
  obtain ⟨p, hp, hpx⟩ := exists_bounded_polynomial_division a b r x (hJ hxJ)
  let z := p.eval₂ (algebraMap A (saturatedChart A (Ideal.span {a, b}) a))
    (parameterChartRatio a b)
  have hzK : z ∈ weakTransform (Ideal.span {a, b}) J a r := by
    apply (mem_weakTransform (Ideal.span {a, b}) J a r).mpr
    rw [← hpx]
    exact Ideal.mem_map_of_mem _ hxJ
  have hzE : z ∉ Ideal.span
      {algebraMap A (saturatedChart A (Ideal.span {a, b}) a) a} := by
    intro hz
    apply hxnext
    rw [← comap_exceptional_pow_eq_span_pair_pow a b ha hb (r + 1)]
    change algebraMap A (saturatedChart A (Ideal.span {a, b}) a) x ∈
      Ideal.span {(algebraMap A (saturatedChart A (Ideal.span {a, b}) a) a) ^ (r + 1)}
    rw [pow_succ, ← Ideal.span_singleton_mul_span_singleton]
    exact Ideal.mem_span_singleton_mul.mpr ⟨z, hz, hpx.symm⟩
  refine ⟨p.map (Ideal.Quotient.mk (Ideal.span {a, b})), ?_,
    Polynomial.natDegree_map_le.trans hp, ?_⟩
  · rw [← parameterChartFibreMap_eval a b ha hb p]
    exact mt (parameterChartFibreMap_eq_zero_iff a b ha hb z).mp hzE
  · rw [← parameterChartFibreMap_eval a b ha hb p]
    exact Ideal.mem_map_of_mem _ hzK

end Localization.Away

namespace Localization.Away

variable {A : Type*} [CommRing A]

/-- Every power up to the division order is in the image of actual division. -/
theorem ratio_pow_mem_range_weakTransformDivision (a b : A) (J : Ideal A) (r i : ℕ)
    (hi : i ≤ r) :
    (Ideal.Quotient.mk (weakTransform (Ideal.span {a, b}) J a r)
        (parameterChartRatio a b)) ^ i ∈
      (weakTransformDivision (Ideal.span {a, b}) J a r
        (Ideal.subset_span (by simp))).range := by
  let I : Ideal A := Ideal.span {a, b}
  let C := saturatedChart A I a
  let e : C := algebraMap A C a
  let t : C := parameterChartRatio a b
  let K : Ideal C := weakTransform I J a r
  have hx : a ^ (r - i) * b ^ i ∈ I ^ r := by
    have hmem : a ^ (r - i) * b ^ i ∈ I ^ (r - i) * I ^ i :=
      Ideal.mul_mem_mul (Ideal.pow_mem_pow (Ideal.subset_span (by simp)) _)
        (Ideal.pow_mem_pow (Ideal.subset_span (by simp)) _)
    simpa only [← pow_add, Nat.sub_add_cancel hi] using hmem
  let x : ↥(I ^ r) := ⟨a ^ (r - i) * b ^ i, hx⟩
  have hxdiv : chartPowerDivision I a r (Ideal.subset_span (by simp)) x = t ^ i := by
    apply chartPowerDivision_eq_of_mul_eq
    change e ^ r * t ^ i = algebraMap A C (a ^ (r - i) * b ^ i)
    rw [map_mul, map_pow, map_pow, ← parameterChartRatio_relation a b, mul_pow]
    change e ^ r * t ^ i = e ^ (r - i) * (e ^ i * t ^ i)
    rw [← mul_assoc, ← pow_add, Nat.sub_add_cancel hi]
  refine ⟨x, ?_⟩
  change Ideal.Quotient.mk K (chartPowerDivision I a r (Ideal.subset_span (by simp)) x) = _
  rw [hxdiv, map_pow]

private theorem quotient_scalar_mul {C : Type*} [CommRing C] [Algebra A C]
    (K : Ideal C) (s : A) (q : C ⧸ K) :
    s • q = Ideal.Quotient.mk K (algebraMap A C s) * q := by
  obtain ⟨c, rfl⟩ := Ideal.Quotient.mk_surjective q
  calc
    s • Ideal.Quotient.mk K c = Ideal.Quotient.mk K (s • c) :=
      (Submodule.Quotient.mk_smul K s c).symm
    _ = Ideal.Quotient.mk K (algebraMap A C s * c) :=
      congrArg (Ideal.Quotient.mk K) (Algebra.smul_def s c)
    _ = _ := map_mul _ _ _

/-- The image of division contains every polynomial of degree at most the
division order in the actual quotient ratio. -/
theorem bounded_eval_mem_range_weakTransformDivision (a b : A) (J : Ideal A) (r : ℕ)
    (p : Polynomial A) (hp : p.natDegree ≤ r) :
    Ideal.Quotient.mk (weakTransform (Ideal.span {a, b}) J a r)
        (p.eval₂ (algebraMap A (saturatedChart A (Ideal.span {a, b}) a))
          (parameterChartRatio a b)) ∈
      (weakTransformDivision (Ideal.span {a, b}) J a r
        (Ideal.subset_span (by simp))).range := by
  rw [Polynomial.eval₂_eq_sum_range]
  simp only [map_sum, map_mul, map_pow]
  apply Submodule.sum_mem
  intro i hi
  have hir : i ≤ r := (Nat.le_of_lt_succ (Finset.mem_range.mp hi)).trans hp
  have h := (weakTransformDivision (Ideal.span {a, b}) J a r
    (Ideal.subset_span (by simp))).range.smul_mem (p.coeff i)
      (ratio_pow_mem_range_weakTransformDivision a b J r i hir)
  rw [quotient_scalar_mul (A := A)
    (weakTransform (Ideal.span {a, b}) J a r) (p.coeff i) _] at h
  exact h

/-- The actual division map is surjective. The initial polynomial controls
the quotient modulo the exceptional parameter, and nilpotence lifts this
surjectivity without a separate finite-generation hypothesis. -/
theorem weakTransformDivision_surjective (a b : A)
    (ha : IsSMulRegular A a) (hb : IsSMulRegular (A ⧸ Ideal.span {a}) b)
    (hmax : (Ideal.span {a, b}).IsMaximal) (J : Ideal A) (r N : ℕ)
    (hJ : J ≤ (Ideal.span {a, b}) ^ r)
    (hnext : ¬ J ≤ (Ideal.span {a, b}) ^ (r + 1))
    (hN : (Ideal.span {a, b}) ^ N ≤ J) (hrN : r ≤ N) :
    Function.Surjective (weakTransformDivision (Ideal.span {a, b}) J a r
      (Ideal.subset_span (by simp))) := by
  let I : Ideal A := Ideal.span {a, b}
  let C := saturatedChart A I a
  let e : C := algebraMap A C a
  let t : C := parameterChartRatio a b
  let K : Ideal C := weakTransform I J a r
  let Q := C ⧸ K
  let F := parameterChartFibreMap a b ha hb
  let D := weakTransformDivision I J a r (Ideal.subset_span (by simp))
  let : I.IsMaximal := hmax
  let := Ideal.Quotient.field I
  have hnil : ∀ q : Q, a ^ (N - r) • q = 0 := by
    intro q
    obtain ⟨c, rfl⟩ := Ideal.Quotient.mk_surjective q
    have he := exceptional_pow_mem_weakTransform I J a r
      (Ideal.subset_span (by simp)) hN hrN
    rw [quotient_scalar_mul K (a ^ (N - r)) (Ideal.Quotient.mk K c)]
    rw [← map_mul]
    apply Ideal.Quotient.eq_zero_iff_mem.mpr
    rw [map_pow]
    exact K.mul_mem_right c he
  have hker : RingHom.ker F.toRingHom = Ideal.span {e} := by
    ext c
    exact parameterChartFibreMap_eq_zero_iff a b ha hb c
  obtain ⟨h, hh0, hdegree, hhK⟩ := exists_bounded_initial_polynomial a b ha hb J r hJ hnext
  have hlift : ∀ q : Q, ∃ y : Q, q - a • y ∈ D.range := by
    intro q
    obtain ⟨c, rfl⟩ := Ideal.Quotient.mk_surjective q
    let rem := F c % h
    have hrem : rem.natDegree ≤ r :=
      (Polynomial.natDegree_le_natDegree (Polynomial.degree_mod_lt (F c) hh0).le).trans hdegree
    obtain ⟨p, hpmap, hpdegree⟩ := Polynomial.exists_natDegree_eq_of_mem_lifts
      (Polynomial.map_surjective (Ideal.Quotient.mk I) Ideal.Quotient.mk_surjective rem)
    have hp : p.natDegree ≤ r := hpdegree.trans_le hrem
    let z : C := p.eval₂ (algebraMap A C) t
    have hzF : F z = rem := (parameterChartFibreMap_eval a b ha hb p).trans hpmap
    have hdiff : F c - rem ∈ K.map F.toRingHom := by
      have heq := EuclideanDomain.mod_add_div (F c) h
      have hmul : h * (F c / h) ∈ K.map F.toRingHom :=
        (K.map F.toRingHom).mul_mem_right _ hhK
      convert hmul using 1
      linear_combination -heq
    have hcz : c - z ∈ K ⊔ Ideal.span {e} := by
      rw [← hker, ← Ideal.comap_map_of_surjective' F.toRingHom
        (parameterChartFibreMap_surjective a b ha hb) K]
      change F (c - z) ∈ K.map F.toRingHom
      rw [map_sub, hzF]
      exact hdiff
    obtain ⟨k, hk, v, hv, hkv⟩ := Submodule.mem_sup.mp hcz
    obtain ⟨y, hy⟩ := Ideal.mem_span_singleton.mp hv
    refine ⟨Ideal.Quotient.mk K y, ?_⟩
    have hzrange : Ideal.Quotient.mk K z ∈ D.range :=
      bounded_eval_mem_range_weakTransformDivision a b J r p hp
    have hrel := congrArg (Ideal.Quotient.mk K) hkv
    rw [hy, map_add, map_mul, map_sub, Ideal.Quotient.eq_zero_iff_mem.mpr hk,
      zero_add] at hrel
    have heq : Ideal.Quotient.mk K c - a • Ideal.Quotient.mk K y =
        Ideal.Quotient.mk K z := by
      rw [quotient_scalar_mul K a (Ideal.Quotient.mk K y)]
      change Ideal.Quotient.mk K c - Ideal.Quotient.mk K e * Ideal.Quotient.mk K y = _
      linear_combination -hrel
    rwa [heq]
  exact LinearMap.range_eq_top.mp
    (Submodule.eq_top_of_nilpotent_lifting D.range a (N - r) hnil hlift)

end Localization.Away

namespace Module

variable {R M V Q : Type*} [CommRing R] [AddCommGroup M] [Module R M]
  [AddCommGroup V] [Module R V] [AddCommGroup Q] [Module R Q]

/-- A surjection that factors through a proper finite-length image has
strictly smaller length than the ambient module. -/
theorem length_lt_of_surjective_of_ker_le (f : M →ₗ[R] V) (g : M →ₗ[R] Q)
    (hker : f.ker ≤ g.ker) (hg : Function.Surjective g)
    (hV : IsFiniteLength R V) (hf : f.range ≠ ⊤) :
    Module.length R Q < Module.length R V := by
  obtain ⟨hno, hart⟩ := isFiniteLength_iff_isNoetherian_isArtinian.mp hV
  let : IsNoetherian R V := hno
  let : IsArtinian R V := hart
  let lift : f.range →ₗ[R] Q :=
    (f.ker.liftQ g hker).comp f.quotKerEquivRange.symm.toLinearMap
  have hsurj : Function.Surjective lift := by
    intro q
    obtain ⟨x, rfl⟩ := hg q
    refine ⟨f.quotKerEquivRange (f.ker.mkQ x), ?_⟩
    simp only [lift, LinearMap.comp_apply, LinearEquiv.coe_coe,
      LinearEquiv.symm_apply_apply, Submodule.mkQ_apply, Submodule.liftQ_apply]
  exact (Module.length_le_of_surjective lift hsurj).trans_lt (Submodule.length_lt hf)

end Module

namespace Ideal

variable {R : Type*} [CommRing R]

/-- The local quotient is an actual quotient of the Artinian global quotient;
restriction of scalars bounds its local-ring length. -/
theorem length_quotientAtPrime_le (K P : Ideal R) [P.IsPrime]
    [IsArtinianRing (R ⧸ K)] :
    Module.length (Localization.AtPrime P) (quotientAtPrime K P) ≤
      Module.length R (R ⧸ K) := by
  let B := Localization.AtPrime P
  let Q := R ⧸ K
  let Qp := quotientAtPrime K P
  let S := Algebra.algebraMapSubmonoid Q P.primeCompl
  have hsurj : Function.Surjective (algebraMap Q Qp) :=
    IsArtinianRing.localization_surjective S Qp
  let f : Q →ₗ[R] Qp := (IsScalarTower.toAlgHom R Q Qp).toLinearMap
  have hle := (⊤ : Submodule B Qp).length_le_length_restrictScalars R
  have hle' : Module.length B Qp ≤ Module.length R Qp := by
    simpa only [Submodule.restrictScalars_top, Module.length_top] using hle
  exact hle'.trans (Module.length_le_of_surjective f hsurj)

end Ideal

namespace Localization.Away

variable {A : Type*} [CommRing A]

/-- Strict colength decrease for the actual quotient in one saturated chart.
The finite-colength hypothesis is on the original ideal quotient. -/
theorem weakTransform_colength_lt (a b : A)
    (ha : IsSMulRegular A a) (hb : IsSMulRegular (A ⧸ Ideal.span {a}) b)
    (hmax : (Ideal.span {a, b}).IsMaximal) (J : Ideal A) (r N : ℕ)
    (hr : 0 < r) (hJ : J ≤ (Ideal.span {a, b}) ^ r)
    (hnext : ¬ J ≤ (Ideal.span {a, b}) ^ (r + 1))
    (hN : (Ideal.span {a, b}) ^ N ≤ J) (hrN : r ≤ N)
    (hfin : IsFiniteLength A (A ⧸ J)) :
    Module.length A (saturatedChart A (Ideal.span {a, b}) a ⧸
      weakTransform (Ideal.span {a, b}) J a r) < Module.length A (A ⧸ J) := by
  let I : Ideal A := Ideal.span {a, b}
  let f : ↥(I ^ r) →ₗ[A] (A ⧸ J) := J.mkQ.comp (I ^ r).subtype
  let g := weakTransformDivision I J a r (Ideal.subset_span (by simp))
  have hker : f.ker ≤ g.ker := by
    intro x hx
    change g x = 0
    apply weakTransformDivision_eq_zero
    apply Ideal.Quotient.eq_zero_iff_mem.mp
    exact hx
  have hf : f.range ≠ ⊤ := by
    intro htop
    obtain ⟨x, hx⟩ := LinearMap.range_eq_top.mp htop (Ideal.Quotient.mk J 1)
    have hdiff : (x : A) - 1 ∈ J := Ideal.Quotient.eq.mp hx
    have hone : (1 : A) ∈ I ^ r := by
      convert (I ^ r).sub_mem x.property (hJ hdiff) using 1
      ring
    exact hmax.ne_top ((Ideal.eq_top_iff_one I).mpr
      (Ideal.pow_le_self (Nat.ne_of_gt hr) hone))
  exact Module.length_lt_of_surjective_of_ker_le f g hker
    (weakTransformDivision_surjective a b ha hb hmax J r N hJ hnext hN hrN) hfin hf

/-- Strict decrease at an actual point localization of the original chart. -/
theorem weakTransform_local_colength_lt [IsNoetherianRing A] (a b : A)
    (ha : IsSMulRegular A a) (hb : IsSMulRegular (A ⧸ Ideal.span {a}) b)
    (hmax : (Ideal.span {a, b}).IsMaximal) (J : Ideal A) (r N : ℕ)
    (hr : 0 < r) (hJ : J ≤ (Ideal.span {a, b}) ^ r)
    (hnext : ¬ J ≤ (Ideal.span {a, b}) ^ (r + 1))
    (hN : (Ideal.span {a, b}) ^ N ≤ J) (hrN : r ≤ N)
    (hfin : IsFiniteLength A (A ⧸ J))
    (P : Ideal (saturatedChart A (Ideal.span {a, b}) a)) [P.IsPrime] :
    Module.length (Localization.AtPrime P)
        (Ideal.quotientAtPrime (weakTransform (Ideal.span {a, b}) J a r) P) <
      Module.length A (A ⧸ J) := by
  let C := saturatedChart A (Ideal.span {a, b}) a
  let K : Ideal C := weakTransform (Ideal.span {a, b}) J a r
  let Q := C ⧸ K
  let := weakTransform_quotient_isArtinian a b ha hb hmax J r N hJ hnext hN hrN
  have hle := (⊤ : Submodule C Q).length_le_length_restrictScalars A
  have hle' : Module.length C Q ≤ Module.length A Q := by
    simpa only [Submodule.restrictScalars_top, Module.length_top] using hle
  exact ((Ideal.length_quotientAtPrime_le K P).trans hle').trans_lt
    (weakTransform_colength_lt a b ha hb hmax J r N hr hJ hnext hN hrN hfin)

/-- The strict local decrease as an actual natural-number measure. Finiteness
of the original length and the proved strict inequality justify both conversions. -/
theorem weakTransform_local_colength_toNat_lt [IsNoetherianRing A] (a b : A)
    (ha : IsSMulRegular A a) (hb : IsSMulRegular (A ⧸ Ideal.span {a}) b)
    (hmax : (Ideal.span {a, b}).IsMaximal) (J : Ideal A) (r N : ℕ)
    (hr : 0 < r) (hJ : J ≤ (Ideal.span {a, b}) ^ r)
    (hnext : ¬ J ≤ (Ideal.span {a, b}) ^ (r + 1))
    (hN : (Ideal.span {a, b}) ^ N ≤ J) (hrN : r ≤ N)
    (hfin : IsFiniteLength A (A ⧸ J))
    (P : Ideal (saturatedChart A (Ideal.span {a, b}) a)) [P.IsPrime] :
    (Module.length (Localization.AtPrime P)
        (Ideal.quotientAtPrime (weakTransform (Ideal.span {a, b}) J a r) P)).toNat <
      (Module.length A (A ⧸ J)).toNat := by
  have h := weakTransform_local_colength_lt a b ha hb hmax J r N
    hr hJ hnext hN hrN hfin P
  have hleft := ne_top_of_lt h
  have hright := Module.length_ne_top_iff.mpr hfin
  apply ENat.natCast_lt_natCast.mp
  rwa [ENat.natCast_toNat hleft, ENat.natCast_toNat hright]

end Localization.Away
