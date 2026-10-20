/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Aglib.RingTheory.RootsOfUnity.FiniteData
public import Mathlib.Algebra.Ring.Subring.Basic

/-!
# Prime roots with supplied units

Source: `R5Lab.Aglib.RingTheory.RootsOfUnity.PrimeUnits`,
revision `f8a3314ddecffcada2ec721d26d56a937bed9690`. Exact field, action, embedding and
explicit-data hypotheses are retained. Native objects and maps are reused.
-/

@[expose] public noncomputable section

namespace RootsOfUnity
universe u
/-- Lift a unit through an injective ring map using the original value and
inverse value, with no assumption about surjectivity of the map. -/
def liftUnitOfRange
    {A K : Type u} [CommRing A] [Field K] (ι : A →+* K) (hι : Function.Injective ι)
    (z : Kˣ) (hz : (z : K) ∈ ι.range) (hzi : ((z⁻¹ : Kˣ) : K) ∈ ι.range) : Aˣ where
  val := Classical.choose hz
  inv := Classical.choose hzi
  val_inv := hι (by rw [map_mul, Classical.choose_spec hz, Classical.choose_spec hzi,
    ← Units.val_mul, mul_inv_cancel, Units.val_one, map_one])
  inv_val := hι (by rw [map_mul, Classical.choose_spec hzi, Classical.choose_spec hz,
    ← Units.val_mul, inv_mul_cancel, Units.val_one, map_one])

@[simp] theorem map_liftUnitOfRange
    {A K : Type u} [CommRing A] [Field K] (ι : A →+* K) (hι : Function.Injective ι)
    (z : Kˣ) (hz : (z : K) ∈ ι.range) (hzi : ((z⁻¹ : Kˣ) : K) ∈ ι.range) :
    Units.map ι.toMonoidHom (liftUnitOfRange ι hι z hz hzi) = z := by
  apply Units.ext
  exact Classical.choose_spec hz

/-- Independently specified algebraic root data on the actual constant base.
It contains the units that exclude collapse to one and characteristic q. -/
structure PrimeRootUnits (q : ℕ) (A : Type u) [CommRing A] where
  prime : q.Prime
  root : Aˣ
  root_pow_eq_one : root ^ q = 1
  rootMinusOne : Aˣ
  rootMinusOne_val : (rootMinusOne : A) = (root : A) - 1
  primeUnit : Aˣ
  primeUnit_val : (primeUnit : A) = q

/-- Membership of the explicitly prescribed constant data constructs all
root units on the actual base, preserving the original root in K. -/
theorem exists_primeRootUnits
    {A K : Type u} [CommRing A] [Field K] (ι : A →+* K) (hι : Function.Injective ι)
    (q : ℕ) (hq : q.Prime) (ζ : Kˣ) (hζ : IsPrimitiveRoot ζ q) (extra : Finset K)
    (hdata : ∀ x ∈ primeRootExtraData q ζ extra, x ∈ ι.range) :
    ∃ w : PrimeRootUnits q A, Units.map ι.toMonoidHom w.root = ζ := by
  classical
  let : NeZero q := ⟨hq.ne_zero⟩
  have hζval : IsPrimitiveRoot (ζ : K) q := IsPrimitiveRoot.coe_units_iff.mpr hζ
  let : NeZero (q : K) := hζval.neZero'
  have hζne : (ζ : K) ≠ 1 := by
    intro h
    exact hζ.ne_one hq.one_lt (Units.ext h)
  let d : Kˣ := Units.mk0 ((ζ : K) - 1) (sub_ne_zero.mpr hζne)
  let c : Kˣ := Units.mk0 (q : K) (NeZero.ne _)
  let root := liftUnitOfRange ι hι ζ
    (hdata _ (by simp [primeRootExtraData])) (hdata _ (by simp [primeRootExtraData]))
  let minus := liftUnitOfRange ι hι d
    (hdata _ (by simp [primeRootExtraData, d])) (hdata _ (by simp [primeRootExtraData, d]))
  let prime := liftUnitOfRange ι hι c
    (hdata _ (by simp [primeRootExtraData, c])) (hdata _ (by simp [primeRootExtraData, c]))
  have hroot : Units.map ι.toMonoidHom root = ζ := map_liftUnitOfRange _ _ _ _ _
  have hminus : Units.map ι.toMonoidHom minus = d := map_liftUnitOfRange _ _ _ _ _
  have hprime : Units.map ι.toMonoidHom prime = c := map_liftUnitOfRange _ _ _ _ _
  refine ⟨⟨hq, root, ?_, minus, ?_, prime, ?_⟩, hroot⟩
  · apply Units.map_injective hι
    rw [map_pow, hroot, hζ.pow_eq_one, map_one]
  · apply hι
    rw [map_sub, map_one]
    exact congrArg (fun u : Kˣ => (u : K)) hminus |>.trans
      (congrArg (fun u : Kˣ => (u : K) - 1) hroot).symm
  · apply hι
    rw [map_natCast]
    exact congrArg (fun u : Kˣ => (u : K)) hprime

/-- Every field fibre of the actual constant base preserves exact primitive
prime order and q invertibility, derived from the stored units. -/
theorem PrimeRootUnits.specialize
    {A F : Type u} [CommRing A] [Field F] {q : ℕ}
    (w : PrimeRootUnits q A) (f : A →+* F) :
    IsPrimitiveRoot (Units.map f.toMonoidHom w.root) q ∧ (q : F) ≠ 0 := by
  have hpow : (Units.map f.toMonoidHom w.root) ^ q = 1 := by
    rw [← map_pow, w.root_pow_eq_one, map_one]
  have hne : Units.map f.toMonoidHom w.root ≠ 1 := by
    intro hroot
    have hminus : ((Units.map f.toMonoidHom w.rootMinusOne : Fˣ) : F) = 0 := by
      change f (w.rootMinusOne : A) = 0
      rw [w.rootMinusOne_val, map_sub, map_one]
      exact sub_eq_zero.mpr (congrArg (fun u : Fˣ => (u : F)) hroot)
    exact (Units.map f.toMonoidHom w.rootMinusOne).ne_zero hminus
  have hq : (q : F) ≠ 0 := by
    intro hzero
    have hval : ((Units.map f.toMonoidHom w.primeUnit : Fˣ) : F) = (q : F) := by
      change f (w.primeUnit : A) = q
      rw [w.primeUnit_val, map_natCast]
    exact (Units.map f.toMonoidHom w.primeUnit).ne_zero (hval.trans hzero)
  let : Fact q.Prime := ⟨w.prime⟩
  exact ⟨IsPrimitiveRoot.iff_orderOf.mpr (orderOf_eq_prime hpow hne), hq⟩

section

local instance (L : Type u) : DecidableEq L := Classical.decEq L

/-- The same prescribed unit data can be mapped to a non-field fibre ring. -/
def PrimeRootUnits.map
    {A C : Type u} [CommRing A] [CommRing C] {q : ℕ}
    (w : PrimeRootUnits q A) (f : A →+* C) : PrimeRootUnits q C where
  prime := w.prime
  root := Units.map f.toMonoidHom w.root
  root_pow_eq_one := by rw [← map_pow, w.root_pow_eq_one, map_one]
  rootMinusOne := Units.map f.toMonoidHom w.rootMinusOne
  rootMinusOne_val := by
    change f (w.rootMinusOne : A) = f (w.root : A) - 1
    rw [w.rootMinusOne_val, map_sub, map_one]
  primeUnit := Units.map f.toMonoidHom w.primeUnit
  primeUnit_val := by
    change f (w.primeUnit : A) = q
    rw [w.primeUnit_val, map_natCast]

/-- The root has exact prime order already in every nonzero ring receiving the
stored unit data, and q is a unit there. -/
theorem PrimeRootUnits.primitive_and_prime_unit
    {A : Type u} [CommRing A] [Nontrivial A] {q : ℕ} (w : PrimeRootUnits q A) :
    IsPrimitiveRoot w.root q ∧ IsUnit (q : A) := by
  have hne : w.root ≠ 1 := by
    intro hroot
    have hzero : (w.rootMinusOne : A) = 0 := by
      rw [w.rootMinusOne_val, hroot, Units.val_one, sub_self]
    exact w.rootMinusOne.ne_zero hzero
  let : Fact q.Prime := ⟨w.prime⟩
  exact ⟨IsPrimitiveRoot.iff_orderOf.mpr (orderOf_eq_prime w.root_pow_eq_one hne),
    w.primeUnit_val ▸ w.primeUnit.isUnit⟩

end


end RootsOfUnity
