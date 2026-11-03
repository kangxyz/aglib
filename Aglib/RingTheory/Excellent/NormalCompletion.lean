/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.RingTheory.Excellent.Normalization
public import Aglib.RingTheory.Excellent.ReducedFiber
public import Aglib.RingTheory.AdicCompletion.NormalSurface

/-!
# Normal surface completion under the actual regular-map hypothesis

A regular original completion map supplies reduced prime-base quotients and
regular localizations over the generic point. The original punctured-spectrum
and regular-parameter-pair arguments then prove integral closedness. The
Artinian genuine total quotient ring supplies domainhood separately.
-/

@[expose] public noncomputable section

open IsLocalRing

universe u

namespace AdicCompletion

/-- A normal Noetherian local domain of dimension two with regular original
completion map has a normal-domain actual completion. There is no chosen
complete source or Nagata premise, and generic formal fibres need not have
dimension zero. -/
theorem normalDomain_of_regularMap_of_dim_eq_two
    (R : Type u) [CommRing R] [IsDomain R] [IsLocalRing R]
    [IsNoetherianRing R] [IsIntegrallyClosed R]
    (hdim : ringKrullDim R = 2)
    (h : Algebra.IsRegularMap R (AdicCompletion (maximalIdeal R) R)) :
    IsDomain (AdicCompletion (maximalIdeal R) R) ∧
      IsIntegrallyClosed (AdicCompletion (maximalIdeal R) R) := by
  let C := AdicCompletion (maximalIdeal R) R
  let : IsNoetherianRing C := AdicCompletion.isNoetherianRing R (maximalIdeal R)
  let : IsReduced C := h.isReduced_of_isDomain R C
  let : IsIntegrallyClosed C := by
    apply isIntegrallyClosed_completion_of_regular_nonmaximal R hdim
    intro P hP hPm
    apply isRegularLocalRing_atPrime_of_normal_surface_completion R hdim ?_ ?_ P hPm
    · intro Q hQ hQ0
      exact h.isRegularLocalRing_atPrime_of_comap_eq_bot R C Q hQ0
    · intro p hp
      exact h.isReduced_quotient_prime R C p
  exact ⟨IsIntegrallyClosed.isDomain_of_isLocalRing_of_isReduced C, inferInstance⟩

end AdicCompletion
