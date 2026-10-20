/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.GroupTheory.Torsion.Levels
public import Mathlib.GroupTheory.QuotientGroup.Finite

/-!
# Finiteness of torsion levels from prime levels

All detector maps and their injectivity inputs remain explicit.

Source: `R5Lab.Aglib.GroupTheory.Torsion.Finite`.
Packet SHA-256:
`e2046bd0fd3e73da88e1137cd31981941b02d9ab290219ab5b4ad3756b3634e1`.
Actual hypotheses, universes and forward maps are retained; source identity is
separate from compilation and mathematical-adoption evidence.
-/

@[expose] public section

noncomputable section
namespace AddSubgroup
variable {T : Type*} [AddCommGroup T]
theorem primary_power_exists (p : ℕ) (x : Ideal.primaryComponent T (Ideal.span {(p : ℤ)})) :
    ∃ r : ℕ, p ^ r • (x : T) = 0 := by
  obtain ⟨r, hr⟩ := (Ideal.primaryComponent_mem T
    (Ideal.span {(p : ℤ)}) (x : T)).mp x.property
  have hp : (p : ℤ) ∈ Ideal.span {(p : ℤ)} := Ideal.subset_span (by simp)
  have hz : (p : ℤ) ^ r • (x : T) = 0 :=
    (Submodule.mem_torsionBySet_iff _ _).mp hr ⟨(p : ℤ) ^ r, Ideal.pow_mem_pow hp r⟩
  exact ⟨r, by simpa only [← Int.natCast_pow, natCast_zsmul] using hz⟩

variable (T : Type*) [AddCommGroup T]
/-- Multiplication by `a` from the `(a * b)`-torsion subgroup to the `b`-torsion subgroup. -/
def torsionByMulMap (a b : ℕ) : torsionBy T ((a * b : ℕ) : ℤ) →+ torsionBy T b where
  toFun x := ⟨a • (x : T), by
    apply torsionBy.nsmul_iff.mpr
    rw [← mul_nsmul]
    exact torsionBy.nsmul_iff.mp x.property⟩
  map_zero' := by
    apply Subtype.ext
    exact nsmul_zero a
  map_add' x y := by
    apply Subtype.ext
    exact (nsmulAddMonoidHom a : T →+ T).map_add (x : T) (y : T)

/-- Finiteness at two levels implies finiteness at their product. The kernel
of multiplication by `a` injects into the `a`-torsion subgroup. -/
theorem finite_torsionBy_mul (a b : ℕ)
    [Finite (torsionBy T a)] [Finite (torsionBy T b)] :
    Finite (torsionBy T ((a * b : ℕ) : ℤ)) := by
  let f := torsionByMulMap T a b
  let kernelInclusion : f.ker → torsionBy T a := fun x =>
    ⟨((x : torsionBy T ((a * b : ℕ) : ℤ)) : T),
      torsionBy.nsmul_iff.mpr
        (congrArg (fun y : torsionBy T b => (y : T)) x.property)⟩
  have hinj : Function.Injective kernelInclusion := by
    intro x y h
    apply Subtype.ext
    apply Subtype.ext
    exact congrArg (fun z : torsionBy T a => (z : T)) h
  let : Finite f.ker := Finite.of_injective kernelInclusion hinj
  let : Fintype f.ker := Fintype.ofFinite f.ker
  let : Fintype (torsionBy T b) := Fintype.ofFinite (torsionBy T b)
  let : Fintype (torsionBy T ((a * b : ℕ) : ℤ)) := AddGroup.fintypeOfKerOfCodom f
  infer_instance

/-- The level `1` subgroup is trivial, independently of any prime hypothesis. -/
theorem finite_torsionBy_one : Finite (torsionBy T 1) := by
  let : Subsingleton (torsionBy T 1) := ⟨by
    intro x y
    apply Subtype.ext
    have hx : (x : T) = 0 := by
      simpa only [one_nsmul] using (torsionBy.nsmul_iff (n := 1)).mp x.property
    have hy : (y : T) = 0 := by
      simpa only [one_nsmul] using (torsionBy.nsmul_iff (n := 1)).mp y.property
    exact hx.trans hy.symm⟩
  infer_instance

/-- The level `0` subgroup is the whole group. Prime-level finiteness alone
therefore gives no finiteness conclusion at level `0`. -/
theorem finite_torsionBy_zero_iff : Finite (torsionBy T 0) ↔ Finite T := by
  constructor
  · intro h
    let : Finite (torsionBy T 0) := h
    exact Finite.of_injective
      (fun x : T => (⟨x, torsionBy.nsmul_iff.mpr (zero_nsmul x)⟩ : torsionBy T 0))
      (fun x y hxy => congrArg Subtype.val hxy)
  · intro h
    let : Finite T := h
    infer_instance

/-- Finiteness at a single level gives finiteness at all its powers. Exponent
`r = 0` is the trivial level `1`, without a prime or positivity requirement. -/
theorem finite_torsionBy_pow (n r : ℕ) [Finite (torsionBy T n)] :
    Finite (torsionBy T ((n ^ r : ℕ) : ℤ)) := by
  induction r with
  | zero => simpa using finite_torsionBy_one T
  | succ r ih =>
    let : Finite (torsionBy T ((n ^ r : ℕ) : ℤ)) := ih
    simpa [pow_succ] using finite_torsionBy_mul T (n ^ r) n

/-- Only prime levels whose primes divide `n` are needed for the finiteness of
the `n`-torsion subgroup, when `n` is positive. -/
theorem finite_torsionBy_of_prime_dvd (n : ℕ) (hn : 0 < n)
    (primeFinite : ∀ p : ℕ, p.Prime → p ∣ n → Finite (torsionBy T p)) :
    Finite (torsionBy T n) := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
    by_cases h1 : n = 1
    · subst n
      exact finite_torsionBy_one T
    obtain ⟨p, hp, hpn⟩ := Nat.exists_prime_and_dvd h1
    obtain ⟨m, rfl⟩ := hpn
    have hm : 0 < m := Nat.pos_of_mul_pos_left hn
    have hlt : m < p * m := lt_mul_of_one_lt_left hm hp.one_lt
    let : Finite (torsionBy T p) := primeFinite p hp (dvd_mul_right p m)
    let : Finite (torsionBy T m) := ih m hlt hm (fun q hq hqm =>
      primeFinite q hq (hqm.trans (dvd_mul_left m p)))
    exact finite_torsionBy_mul T p m

/-- Prime-level finiteness implies finiteness at every positive level. -/
theorem finite_torsionBy_of_prime_levels
    (primeFinite : ∀ p : ℕ, p.Prime → Finite (torsionBy T p))
    (n : ℕ) (hn : 0 < n) : Finite (torsionBy T n) :=
  finite_torsionBy_of_prime_dvd T n hn (fun p hp _ => primeFinite p hp)

/-- A positive annihilating level and prime-level torsion finiteness imply
finiteness of the entire group. Only primes dividing the annihilating level
are needed. -/
theorem finite_of_annihilated_of_prime_dvd (n : ℕ) (hn : 0 < n)
    (annihilated : ∀ x : T, n • x = 0)
    (primeFinite : ∀ p : ℕ, p.Prime → p ∣ n → Finite (torsionBy T p)) :
    Finite T := by
  let : Finite (torsionBy T n) := finite_torsionBy_of_prime_dvd T n hn primeFinite
  exact Finite.of_injective
    (fun x : T => (⟨x, torsionBy.nsmul_iff.mpr (annihilated x)⟩ : torsionBy T n))
    (fun x y h => congrArg Subtype.val h)

/-- The global prime-level form of the finite-exponent criterion. -/
theorem finite_of_annihilated_of_prime_levels (n : ℕ) (hn : 0 < n)
    (annihilated : ∀ x : T, n • x = 0)
    (primeFinite : ∀ p : ℕ, p.Prime → Finite (torsionBy T p)) : Finite T :=
  finite_of_annihilated_of_prime_dvd T n hn annihilated (fun p hp _ => primeFinite p hp)

/-- The literal inclusion of the torsion level of a subgroup into its ambient level. -/
def torsionBySubtypeMap (S : AddSubgroup T) (n : ℕ) :
    torsionBy S n →+ torsionBy T n where
  toFun x := ⟨((x : S) : T), congrArg (fun y : S => (y : T)) x.property⟩
  map_zero' := rfl
  map_add' _ _ := rfl

theorem torsionBySubtypeMap_injective (S : AddSubgroup T) (n : ℕ) :
    Function.Injective (torsionBySubtypeMap T S n) := by
  intro x y h
  apply Subtype.ext
  apply Subtype.ext
  exact congrArg (fun z : torsionBy T n => (z : T)) h

/-- Subgroup level finiteness follows from ambient level finiteness through
the literal subgroup inclusion. -/
theorem finite_torsionBy_subgroup (S : AddSubgroup T) (n : ℕ)
    [Finite (torsionBy T n)] : Finite (torsionBy S n) :=
  Finite.of_injective (torsionBySubtypeMap T S n)
    (torsionBySubtypeMap_injective T S n)

end AddSubgroup
