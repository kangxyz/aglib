/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Aglib.RingTheory.Reflexive.BidualEndomorphism
public import Aglib.RingTheory.RegularLocalRing.PuncturedDualComparison

/-! Duals of the actual double-transpose action across punctured reflexivity. -/

@[expose] public section

noncomputable section

universe u

namespace Module.Dual

/-- In regular local dimension at least two, punctured reflexivity identifies the
actual dual of the endomorphism action on a bidual. -/
def doubleTransposeDualEquiv
    (R M : Type u) [CommRing R] [IsRegularLocalRing R]
    [AddCommGroup M] [Module R M] [Module.Finite R M]
    (hlocal : ∀ p : PrimeSpectrum R, p.asIdeal ≠ IsLocalRing.maximalIdeal R →
      Module.IsReflexive (Localization.AtPrime p.asIdeal)
        (LocalizedModule p.asIdeal.primeCompl M))
    (d : ℕ) (hd : ringKrullDim R = (d : ℕ)) (h2 : 2 ≤ d) :
    Dual R (Module.End R (Dual R (Dual R M))) ≃ₗ[R] Dual R (Module.End R M) := by
  let E := Module.End R M
  let F := Module.End R (Dual R (Dual R M))
  let g : E →ₗ[R] F := doubleTranspose R M
  have hg (p : PrimeSpectrum R) (hp : p.asIdeal ≠ IsLocalRing.maximalIdeal R) :
      Function.Bijective (LocalizedModule.map p.asIdeal.primeCompl g) :=
    localized_doubleTranspose_bijective_punctured R M hlocal p hp
  exact LinearMap.dualEquivOfBijectivePunctured (R := R) (M := E) (N := F)
    g hg d hd h2

end Module.Dual
