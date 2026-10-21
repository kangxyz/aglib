/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Aglib.RingTheory.RegularLocalRing.FiniteLengthDualComparison
public import Aglib.RingTheory.Support.FiniteDefect

/-! The actual dual of a map bijective off the closed point of a regular local ring. -/

@[expose] public section

noncomputable section

universe u

namespace LinearMap

variable {R M N : Type u} [CommRing R] [IsRegularLocalRing R]
  [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
  [Module.Finite R M] [Module.Finite R N]

/-- The original dual map is an equivalence for finite modules whenever the map is
bijective off the closed point of a regular local ring of dimension at least two. -/
def dualEquivOfBijectivePunctured (f : M →ₗ[R] N)
    (hlocal : ∀ p : PrimeSpectrum R, p.asIdeal ≠ IsLocalRing.maximalIdeal R →
      Function.Bijective (LocalizedModule.map p.asIdeal.primeCompl f))
    (d : ℕ) (hd : ringKrullDim R = (d : ℕ)) (h2 : 2 ≤ d) :
    Module.Dual R N ≃ₗ[R] Module.Dual R M :=
  LinearEquiv.ofBijective f.dualMap
    (IsRegularLocalRing.bijective_dualMap_of_isFiniteLength R f
      (f.isFiniteLength_ker_of_injective_punctured (fun p hp ↦ (hlocal p hp).injective))
      (f.isFiniteLength_coker_of_surjective_punctured (fun p hp ↦ (hlocal p hp).surjective))
      d hd h2)

@[simp]
theorem dualEquivOfBijectivePunctured_apply (f : M →ₗ[R] N)
    (hlocal : ∀ p : PrimeSpectrum R, p.asIdeal ≠ IsLocalRing.maximalIdeal R →
      Function.Bijective (LocalizedModule.map p.asIdeal.primeCompl f))
    (d : ℕ) (hd : ringKrullDim R = (d : ℕ)) (h2 : 2 ≤ d) (l : Module.Dual R N) :
    f.dualEquivOfBijectivePunctured hlocal d hd h2 l = f.dualMap l := rfl

end LinearMap
