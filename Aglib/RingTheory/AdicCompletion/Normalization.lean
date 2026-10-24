/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.RingTheory.AdicCompletion.RegularLocalRing
public import Aglib.RingTheory.IntegralClosure.FlatBaseChange
public import Aglib.RingTheory.Nagata.CompleteLocalSurface

/-!
# Finite normalization from reduced completion in dimension at most two

For the original maximal-adic completion, the reduced complete-surface
normalization theorem supplies finiteness of the upper normalization.
The native completion maps supply flatness, locality, completeness, and
the dimension bound. Faithfully flat descent then proves finiteness of
the original normalization in its supplied total quotient ring.
-/

@[expose] public noncomputable section

open IsLocalRing

universe u w

namespace integralClosure

/-- A Noetherian local ring of dimension at most two with reduced actual
maximal-adic completion has finite literal normalization in its supplied
total quotient ring. In particular an analytically unramified domain
in this dimension range is N-1. -/
theorem finite_of_isReduced_completion_of_dimLE_two
    (R : Type u) [CommRing R] [IsLocalRing R] [IsNoetherianRing R]
    [Ring.KrullDimLE 2 R]
    (hred : IsReduced (AdicCompletion (maximalIdeal R) R))
    (K : Type w) [CommRing K] [Algebra R K] [IsFractionRing R K] :
    Module.Finite R (integralClosure R K) := by
  let S := AdicCompletion (maximalIdeal R) R
  let : IsNoetherianRing S := AdicCompletion.isNoetherianRing R (maximalIdeal R)
  let : IsReduced S := hred
  let : Ring.KrullDimLE 2 S := Ring.krullDimLE_iff.mpr
    ((AdicCompletion.ringKrullDim_maximalIdeal_eq R).le.trans
      (Ring.krullDimLE_iff.mp (inferInstance : Ring.KrullDimLE 2 R)))
  let : Module.FaithfullyFlat R S := Module.FaithfullyFlat.of_flat_of_isLocalHom
  let : Module.Finite S (integralClosure S (FractionRing S)) :=
    finite_of_complete_local_reduced_dimLE_two S (FractionRing S)
  exact finite_of_faithfullyFlat R S K (FractionRing S)

end integralClosure
