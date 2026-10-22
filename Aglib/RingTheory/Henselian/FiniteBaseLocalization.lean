/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Mathlib.RingTheory.Localization.Finiteness
public import Mathlib.RingTheory.Localization.LocalizationLocalization

/-!
# Finite base localization and a selected prime

Localizing a finite algebra at the image of a base prime's complement gives a
finite algebra over the localized base. A prime with the specified contraction
extends to this localization, and localizing again at that extended prime is
canonically equivalent to the original prime localization, over the original
algebra. The prime and equivalence constructions do not require finiteness.
-/

@[expose] public section

noncomputable section

universe u v

namespace FiniteBaseLocalization

variable {R : Type u} [CommRing R] {B : Type v} [CommRing B] [Algebra R B]
variable (p : Ideal R) [p.IsPrime]

/-- The actual base-localized algebra. -/
abbrev BaseLocalized := Localization (Algebra.algebraMapSubmonoid B p.primeCompl)

/-- The inherited action is the native localization of the original algebra map. -/
instance baseLocalizedAlgebra :
    Algebra (Localization.AtPrime p) (BaseLocalized (B := B) p) := inferInstance

instance baseLocalizedTower :
    IsScalarTower R (Localization.AtPrime p) (BaseLocalized (B := B) p) := inferInstance

/-- Module finiteness is preserved by this actual localization of the base. -/
theorem finite [Module.Finite R B] :
    Module.Finite (Localization.AtPrime p) (BaseLocalized (B := B) p) := inferInstance

/-- The selected prime is extended along the actual localization map. -/
def selectedPrime (q : Ideal B) : Ideal (BaseLocalized (B := B) p) :=
  q.map (algebraMap B (BaseLocalized (B := B) p))

theorem disjoint_complement (q : Ideal B)
    (hq : q.comap (algebraMap R B) = p) :
    Disjoint (Algebra.algebraMapSubmonoid B p.primeCompl : Set B) (q : Set B) := by
  apply Set.disjoint_left.mpr
  rintro _ ⟨r, hr, rfl⟩ hmem
  change r ∈ q.comap (algebraMap R B) at hmem
  rw [hq] at hmem
  exact hr hmem

theorem selectedPrime_isPrime (q : Ideal B) [q.IsPrime]
    (hq : q.comap (algebraMap R B) = p) : (selectedPrime p q).IsPrime :=
  IsLocalization.isPrime_of_isPrime_disjoint
    (Algebra.algebraMapSubmonoid B p.primeCompl) (BaseLocalized (B := B) p)
    q inferInstance (disjoint_complement p q hq)

theorem selectedPrime_comap (q : Ideal B) [q.IsPrime]
    (hq : q.comap (algebraMap R B) = p) :
    (selectedPrime p q).comap (algebraMap B (BaseLocalized (B := B) p)) = q :=
  IsLocalization.under_map_of_isPrime_disjoint
    (Algebra.algebraMapSubmonoid B p.primeCompl) (BaseLocalized (B := B) p)
    inferInstance (disjoint_complement p q hq)

/-- The canonical equivalence retains compatibility with the original algebra B. -/
def localEquiv (q : Ideal B) [q.IsPrime]
    (hq : q.comap (algebraMap R B) = p) :
    letI := selectedPrime_isPrime p q hq
    Localization.AtPrime (selectedPrime p q) ≃ₐ[B] Localization.AtPrime q := by
  letI := selectedPrime_isPrime p q hq
  letI : IsLocalization.AtPrime (Localization.AtPrime (selectedPrime p q)) q := by
    have h : IsLocalization.AtPrime (Localization.AtPrime (selectedPrime p q))
        ((selectedPrime p q).comap (algebraMap B (BaseLocalized (B := B) p))) :=
      inferInstance
    have hM :
        ((selectedPrime p q).comap (algebraMap B (BaseLocalized (B := B) p))).primeCompl =
          q.primeCompl := by
      ext b
      change b ∉ (selectedPrime p q).comap (algebraMap B (BaseLocalized (B := B) p)) ↔
        b ∉ q
      rw [selectedPrime_comap p q hq]
    exact Eq.mp (congrArg
      (fun M : Submonoid B => IsLocalization M (Localization.AtPrime (selectedPrime p q)))
      hM) h
  exact IsLocalization.algEquiv q.primeCompl _ _

theorem localEquiv_algebraMap (q : Ideal B) [q.IsPrime]
    (hq : q.comap (algebraMap R B) = p) (b : B) :
    letI := selectedPrime_isPrime p q hq
    localEquiv p q hq (algebraMap B (Localization.AtPrime (selectedPrime p q)) b) =
      algebraMap B (Localization.AtPrime q) b := by
  let := selectedPrime_isPrime p q hq
  exact (localEquiv p q hq).commutes b

end FiniteBaseLocalization
