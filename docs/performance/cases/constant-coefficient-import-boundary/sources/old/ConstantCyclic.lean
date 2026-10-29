/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.Algebra.Category.Grp.ZModSequence
public import Aglib.CategoryTheory.Sites.SheafCohomology.Vanishing.ExactSequence
public import Mathlib.Algebra.Category.Grp.Zero
public import Mathlib.Data.Nat.Prime.Basic

/-!
# Cohomology of cyclic coefficients under an exact additive functor

The native cyclic extension is sent to a short exact sequence of abelian sheaves.
At a fixed degree, vanishing passes from prime coefficients to their powers and
to any positive order with vanishing prime divisors. Finiteness passes from a
prime coefficient to its powers by the same-degree cohomology exact sequence.
The coefficient functor and the Ext universe remain fixed throughout.
-/

@[expose] public noncomputable section

universe c v a e

open CategoryTheory CategoryTheory.Limits

namespace CategoryTheory.Sheaf

variable {C : Type c} [Category.{v} C] {J : GrothendieckTopology C}
  [HasSheafify J AddCommGrpCat.{a}]
  (F : AddCommGrpCat.{0} ⥤ Sheaf J AddCommGrpCat.{a})
  [F.Additive] [PreservesFiniteLimits F] [PreservesFiniteColimits F]

/-- The native cyclic extension remains short exact under the coefficient functor. -/
theorem cyclicCoefficient_shortExact (m n : ℕ) (hn : 0 < n) :
    ((ZMod.mulSequence m n).map F).ShortExact :=
  (ZMod.mulSequence_shortExact m n hn).map_of_exact F

variable [HasExt.{e} (Sheaf J AddCommGrpCat.{a})]

/-- At a fixed degree, vanishing for a cyclic coefficient implies vanishing for its powers. -/
theorem cyclicPrimePower_vanishing (p : ℕ) (hp : 0 < p) (q : ℕ)
    [Subsingleton (H.{e} (F.obj (AddCommGrpCat.of (ZMod p))) q)] (r : ℕ) :
    Subsingleton (H.{e} (F.obj (AddCommGrpCat.of (ZMod (p ^ r)))) q) := by
  induction r with
  | zero =>
      change Subsingleton (H.{e} (F.obj (AddCommGrpCat.of (ZMod 1))) q)
      apply subsingleton_H_of_isZero
      exact F.map_isZero (AddCommGrpCat.isZero_of_subsingleton (AddCommGrpCat.of (ZMod 1)))
  | succ r ih =>
      let S := (ZMod.mulSequence (p ^ r) p).map F
      let : Subsingleton (H.{e} S.X₁ q) := ih
      let : Subsingleton (H.{e} S.X₃ q) := inferInstanceAs
        (Subsingleton (H.{e} (F.obj (AddCommGrpCat.of (ZMod p))) q))
      have h := H.subsingleton_middle_of_shortExact
        (cyclicCoefficient_shortExact F (p ^ r) p hp) q
      change Subsingleton (H.{e} (F.obj (AddCommGrpCat.of (ZMod (p ^ r * p)))) q) at h
      exact Eq.mpr (congrArg (fun n : ℕ => Subsingleton
        (H.{e} (F.obj (AddCommGrpCat.of (ZMod n))) q)) (pow_succ p r)) h

/-- Vanishing for every prime divisor implies vanishing for any positive cyclic order. -/
theorem cyclic_vanishing_of_prime_divisors (q n : ℕ) (hn : 0 < n)
    (hprime : ∀ p : ℕ, p.Prime → p ∣ n →
      Subsingleton (H.{e} (F.obj (AddCommGrpCat.of (ZMod p))) q)) :
    Subsingleton (H.{e} (F.obj (AddCommGrpCat.of (ZMod n))) q) := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
    by_cases h1 : n = 1
    · subst n
      apply subsingleton_H_of_isZero
      exact F.map_isZero (AddCommGrpCat.isZero_of_subsingleton (AddCommGrpCat.of (ZMod 1)))
    · obtain ⟨p, hp, hpn⟩ := Nat.exists_prime_and_dvd h1
      have hm : 0 < n / p := Nat.div_pos (Nat.le_of_dvd hn hpn) hp.pos
      have hlt : n / p < n := Nat.div_lt_self hn hp.one_lt
      have hmn : n / p ∣ n := Nat.div_dvd_of_dvd hpn
      let S := (ZMod.mulSequence (n / p) p).map F
      let : Subsingleton (H.{e} S.X₁ q) :=
        ih (n / p) hlt hm (fun l hl hld => hprime l hl (hld.trans hmn))
      let : Subsingleton (H.{e} S.X₃ q) := hprime p hp hpn
      have h := H.subsingleton_middle_of_shortExact
        (cyclicCoefficient_shortExact F (n / p) p hp.pos) q
      change Subsingleton (H.{e} (F.obj (AddCommGrpCat.of (ZMod (n / p * p)))) q) at h
      exact Eq.mp (congrArg (fun m : ℕ => Subsingleton
        (H.{e} (F.obj (AddCommGrpCat.of (ZMod m))) q)) (Nat.div_mul_cancel hpn)) h

/-- At a fixed degree, finiteness for a cyclic coefficient implies finiteness for its powers. -/
theorem cyclicPrimePower_cohomology_finite (p : ℕ) (hp : 0 < p) (q : ℕ)
    [Finite (H.{e} (F.obj (AddCommGrpCat.of (ZMod p))) q)] (r : ℕ) :
    Finite (H.{e} (F.obj (AddCommGrpCat.of (ZMod (p ^ r)))) q) := by
  induction r with
  | zero =>
      change Finite (H.{e} (F.obj (AddCommGrpCat.of (ZMod 1))) q)
      let : Subsingleton (H.{e} (F.obj (AddCommGrpCat.of (ZMod 1))) q) := by
        apply subsingleton_H_of_isZero
        exact F.map_isZero (AddCommGrpCat.isZero_of_subsingleton (AddCommGrpCat.of (ZMod 1)))
      infer_instance
  | succ r ih =>
      let S := (ZMod.mulSequence (p ^ r) p).map F
      let : Finite (H.{e} S.X₁ q) := ih
      let : Finite (H.{e} S.X₃ q) := inferInstanceAs
        (Finite (H.{e} (F.obj (AddCommGrpCat.of (ZMod p))) q))
      have h := (H.longSequence_exact₂'
        (cyclicCoefficient_shortExact F (p ^ r) p hp) q).ab_finite
      change Finite (H.{e} (F.obj (AddCommGrpCat.of (ZMod (p ^ r * p)))) q) at h
      exact Eq.mpr (congrArg (fun n : ℕ => Finite
        (H.{e} (F.obj (AddCommGrpCat.of (ZMod n))) q)) (pow_succ p r)) h

end CategoryTheory.Sheaf
