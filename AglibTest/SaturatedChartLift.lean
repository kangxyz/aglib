module

import Aglib.RingTheory.Localization.Away.SaturatedChartLift
import Mathlib.RingTheory.Ideal.Span
import Mathlib.Algebra.Ring.Regular
import Mathlib.Tactic.NormNum

/-! Actual quotient values and degenerate targets for the saturated-chart lift. -/

noncomputable section
open Localization.Away.SaturatedChart
universe u v

namespace AglibTest.SaturatedChartLift

/-- The ideal of even integers used for the saturated-chart quotient examples. -/
def evenIdeal : Ideal ℤ := Ideal.span ({2} : Set ℤ)

/-- The element `2` of the ideal of even integers. -/
def two : evenIdeal := ⟨2, Ideal.mem_span_singleton_self 2⟩

/-- The element `6` of the ideal of even integers. -/
def six : evenIdeal := ⟨6, Ideal.mem_span_singleton.mpr ⟨3, by norm_num⟩⟩

theorem two_regular : IsRegular ((RingHom.id ℤ) (two : ℤ)) := by
  change IsRegular (2 : ℤ)
  exact isRegular_iff_ne_zero'.mpr (by norm_num)

theorem even_divisibility (b : evenIdeal) :
    (RingHom.id ℤ) (two : ℤ) ∣ (RingHom.id ℤ) (b : ℤ) := by
  change (2 : ℤ) ∣ (b : ℤ)
  exact Ideal.mem_span_singleton.mp b.property

/-- The value is forced on the original fraction inside the actual localization. -/
example : liftOfHom evenIdeal two (RingHom.id ℤ) two_regular even_divisibility
    (fractionElement evenIdeal two six) = 3 :=
  liftOfHom_fraction_eq evenIdeal two (RingHom.id ℤ) two_regular even_divisibility
    six 3 (by norm_num [two, six])

/-- Zero ideal and zero pivot remain valid when the target ring is trivial. -/
example {A : Type u} [CommRing A] {S : Type v} [CommRing S] [Subsingleton S]
    (f : A →+* S) :
    letI : Algebra A S := f.toAlgebra
    ∃! g : Localization.Away.saturatedChart A (⊥ : Ideal A) (0 : A) →ₐ[A] S,
      ∀ b : (⊥ : Ideal A), f 0 * g (fractionElement (⊥ : Ideal A) 0 b) = f b := by
  let : Algebra A S := f.toAlgebra
  apply existsUnique_algHomOfHom (⊥ : Ideal A) (0 : (⊥ : Ideal A)) f
  · exact ⟨fun _ _ _ => Subsingleton.elim _ _, fun _ _ _ => Subsingleton.elim _ _⟩
  · intro b
    exact ⟨0, Subsingleton.elim _ _⟩

/-- Nilpotence plus actual regularity forces precisely the permitted trivial target case. -/
example {S : Type v} [CommRing S] (s : S) (hs : IsNilpotent s)
    (hreg : IsRegular s) : Subsingleton S := by
  obtain ⟨n, hn⟩ := hs
  have hz : IsRegular (0 : S) := by
    simpa only [hn] using IsRegular.pow n hreg
  exact ⟨fun _ _ => hz.left (by simp)⟩

end AglibTest.SaturatedChartLift
