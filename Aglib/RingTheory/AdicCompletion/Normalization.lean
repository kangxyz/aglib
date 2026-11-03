/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.RingTheory.AdicCompletion.RegularLocalRing
public import Aglib.RingTheory.IntegralClosure.FlatBaseChange
public import Aglib.RingTheory.Nagata.CompleteLocal

/-!
# Finite normalization from reduced maximal-adic completion

The complete reduced normalization theorem supplies finiteness over the
original completion, without a dimension bound. Its native faithfully flat
map descends finiteness to the original normalization in the supplied total
quotient ring. The previous dimension-two interface is a thin specialization.
-/

@[expose] public noncomputable section

open IsLocalRing

universe u w

namespace integralClosure

/-- A Noetherian local ring with reduced actual maximal-adic completion has
finite literal normalization in its supplied total quotient ring. In particular,
every analytically unramified local domain is N-1, without a dimension bound. -/
theorem finite_of_isReduced_completion
    (R : Type u) [CommRing R] [IsLocalRing R] [IsNoetherianRing R]
    (hred : IsReduced (AdicCompletion (maximalIdeal R) R))
    (K : Type w) [CommRing K] [Algebra R K] [IsFractionRing R K] :
    Module.Finite R (integralClosure R K) := by
  let S := AdicCompletion (maximalIdeal R) R
  let : IsNoetherianRing S := AdicCompletion.isNoetherianRing R (maximalIdeal R)
  let : IsReduced S := hred
  let : Module.FaithfullyFlat R S := Module.FaithfullyFlat.of_flat_of_isLocalHom
  let : Module.Finite S (integralClosure S (FractionRing S)) :=
    finite_of_complete_local_reduced S (FractionRing S)
  exact finite_of_faithfullyFlat R S K (FractionRing S)

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
  exact finite_of_isReduced_completion R hred K

end integralClosure
