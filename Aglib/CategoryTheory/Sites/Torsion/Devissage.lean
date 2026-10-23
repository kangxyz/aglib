/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.CategoryTheory.Sites.Torsion.Annihilator
public import Mathlib.Algebra.Homology.ShortComplex.ShortExact
public import Mathlib.Data.Nat.Prime.Basic

/-!
# Prime-annihilator devissage for abelian sheaves

For an actual sheaf killed by `n*m`, quotienting by its native `n`-annihilator
kernel gives a sheaf killed by `m`. The original kernel inclusion and native
cokernel projection form a short exact sequence. Thus extension-stable
properties can be reduced from bounded positive torsion to prime torsion.
-/

@[expose] public noncomputable section

open CategoryTheory.Limits

namespace CategoryTheory.Sheaf

universe u v w

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
  [HasSheafify J AddCommGrpCat.{w}]

/-- The actual native cokernel of the original annihilator inclusion. -/
abbrev annihilatorQuotient (F : Sheaf J AddCommGrpCat.{w}) (n : ℕ) :
    Sheaf J AddCommGrpCat.{w} :=
  cokernel (annihilatorι F n)

/-- The original kernel inclusion and its native cokernel projection. -/
def annihilatorQuotientSequence (F : Sheaf J AddCommGrpCat.{w}) (n : ℕ) :
    ShortComplex (Sheaf J AddCommGrpCat.{w}) :=
  ShortComplex.cokernelSequence (annihilatorι F n)

/-- The original annihilator-to-quotient sequence is short exact. -/
theorem annihilatorQuotientSequence_shortExact (F : Sheaf J AddCommGrpCat.{w}) (n : ℕ) :
    (annihilatorQuotientSequence F n).ShortExact := by
  exact ShortComplex.ShortExact.mk' (ShortComplex.cokernelSequence_exact _)
    (annihilatorι_mono F n) (by
      change Epi (cokernel.π (annihilatorι F n))
      infer_instance)

/-- Killing the original sheaf by `n*m` kills its native `n`-kernel quotient by `m`. -/
theorem nsmul_id_annihilatorQuotient (F : Sheaf J AddCommGrpCat.{w}) (n m : ℕ)
    (hF : (n * m) • 𝟙 F = 0) : m • 𝟙 (annihilatorQuotient F n) = 0 := by
  have hcomp : (m • 𝟙 F) ≫ (n • 𝟙 F) = 0 := by
    simpa only [Preadditive.nsmul_comp, Category.id_comp, ← mul_smul,
      Nat.mul_comm m n] using hF
  let t : F ⟶ annihilator F n := kernel.lift (n • 𝟙 F) (m • 𝟙 F) hcomp
  have ht : t ≫ annihilatorι F n = m • 𝟙 F := kernel.lift_ι _ _ _
  apply (cancel_epi (cokernel.π (annihilatorι F n))).1
  rw [Preadditive.comp_nsmul, Category.comp_id, comp_zero]
  calc
    m • cokernel.π (annihilatorι F n) =
        (m • 𝟙 F) ≫ cokernel.π (annihilatorι F n) := by
      rw [Preadditive.nsmul_comp, Category.id_comp]
    _ = (t ≫ annihilatorι F n) ≫ cokernel.π (annihilatorι F n) := by rw [ht]
    _ = 0 := by rw [Category.assoc, cokernel.condition, comp_zero]

/-- Extension-stable properties of positive bounded-torsion sheaves reduce to prime torsion. -/
theorem property_of_prime_annihilators (P : Sheaf J AddCommGrpCat.{w} → Prop)
    (hzero : ∀ F, IsZero F → P F)
    (hprime : ∀ F (p : ℕ), p.Prime → p • 𝟙 F = 0 → P F)
    (hext : ∀ (S : ShortComplex (Sheaf J AddCommGrpCat.{w})), S.ShortExact →
      P S.X₁ → P S.X₃ → P S.X₂)
    (F : Sheaf J AddCommGrpCat.{w}) (n : ℕ) (hn : 0 < n)
    (hF : n • 𝟙 F = 0) : P F := by
  induction n using Nat.strong_induction_on generalizing F with
  | h n ih =>
    by_cases h₁ : n = 1
    · apply hzero F
      apply (IsZero.iff_id_eq_zero F).mpr
      simpa only [h₁, one_nsmul] using hF
    obtain ⟨p, hp, hpn⟩ := Nat.exists_prime_and_dvd h₁
    obtain ⟨m, hm⟩ := hpn
    have hmpos : 0 < m := by
      apply Nat.pos_of_ne_zero
      intro hmzero
      exact (Nat.ne_of_gt hn) (by simpa only [hmzero, Nat.mul_zero] using hm)
    have hmlt : m < n := by
      rw [hm]
      simpa only [one_mul] using Nat.mul_lt_mul_of_pos_right hp.one_lt hmpos
    let S := annihilatorQuotientSequence F p
    apply hext S (annihilatorQuotientSequence_shortExact F p)
    · exact hprime (annihilator F p) p hp (nsmul_id_annihilator F p)
    · apply ih m hmlt (annihilatorQuotient F p) hmpos
      apply nsmul_id_annihilatorQuotient F p m
      simpa only [← hm] using hF

end CategoryTheory.Sheaf
