/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.RingTheory.Henselian.FiniteAlgebraLocalFactor
public import Aglib.RingTheory.Henselian.FiniteAlgebraHenselian

/-!
# Finite domains over a Henselian local ring

The original finite algebra is local: an isolating idempotent for a maximal
ideal must be one in a domain. No localization, completion, or replacement
factor is chosen. The existing finite-local-algebra theorem then supplies
Henselianity on this same ring.
-/

@[expose] public noncomputable section

universe u v

namespace HenselianLocalRing

/-- A finite domain algebra over a Henselian local ring is itself local. -/
theorem isLocalRing_of_finite_domain
    (R : Type u) [CommRing R] [HenselianLocalRing R]
    (S : Type v) [CommRing S] [IsDomain S] [Algebra R S] [Module.Finite R S] :
    IsLocalRing S := by
  obtain ⟨q, hq⟩ := Ideal.exists_maximal (α := S)
  let : q.IsMaximal := hq
  obtain ⟨e, he, heq, huniq⟩ := exists_idempotent_isolating_maximal R S q
  have hzero : e ≠ 0 := fun h => heq (h ▸ q.zero_mem)
  have hone : e = 1 := mul_left_cancel₀ hzero (he.trans (mul_one e).symm)
  apply IsLocalRing.of_unique_max_ideal
  refine ⟨q, hq, fun P hP => huniq P hP ?_⟩
  rw [hone]
  exact P.ne_top_iff_one.mp hP.ne_top

/-- The same finite domain algebra is Henselian, without a completeness hypothesis. -/
theorem of_finite_domain
    (R : Type u) [CommRing R] [HenselianLocalRing R]
    (S : Type v) [CommRing S] [IsDomain S] [Algebra R S] [Module.Finite R S] :
    HenselianLocalRing S := by
  let := isLocalRing_of_finite_domain R S
  exact of_finite_local_algebra R S

end HenselianLocalRing
