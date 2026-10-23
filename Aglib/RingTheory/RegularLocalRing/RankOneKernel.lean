/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.RingTheory.Ideal.RegularPrincipal
public import Aglib.RingTheory.RegularLocalRing.QuotientLift

/-!
# Regular locality across a surjection with a rank-one kernel

`Aglib.RingTheory.RegularLocalRing.RankOneKernel` applies the existing regular-generator
and regular-principal-quotient theorems to the actual kernel of a surjective ring map.
-/

@[expose] public section

noncomputable section

namespace IsRegularLocalRing

universe u v

/-- A Noetherian local ring is regular when it surjects onto a regular local ring and
the actual kernel has a rank-one free presentation. The quotient comparison is the
canonical equivalence induced by this same surjection. -/
theorem of_surjective_ker_freeRankOne
    {R : Type u} {S : Type v} [CommRing R] [CommRing S]
    [IsLocalRing R] [IsNoetherianRing R] [IsRegularLocalRing S]
    (f : R →+* S) (hf : Function.Surjective f) (e : RingHom.ker f ≃ₗ[R] R) :
    IsRegularLocalRing R := by
  obtain ⟨a, ha, hker⟩ := Ideal.ideal_exists_regular_generator (RingHom.ker f) e
  let : IsRegularLocalRing (R ⧸ RingHom.ker f) :=
    of_ringEquiv (f.quotientKerEquivOfSurjective hf).symm
  have hquot : IsRegularLocalRing (R ⧸ Ideal.span {a}) := by
    rw [← hker]
    infer_instance
  let := hquot
  exact of_quotient_span_singleton R a ha

end IsRegularLocalRing
