/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Aglib.RingTheory.Reflexive.HeightOneReconstruction
public import Aglib.RingTheory.Reflexive.Pi

/-! Native reflexive reconstruction with canonical generic and height-one localization maps. -/

@[expose] public section

noncomputable section

example {R M N : Type*} [CommRing R] [IsDomain R] [IsNoetherianRing R]
    [IsIntegrallyClosed R] [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
    [Module.Finite R M] [Module.IsReflexive R M] [Module.IsTorsionFree R N]
    (f : M →ₗ[R] N)
    (hgen : Function.Bijective (LocalizedModule.map (nonZeroDivisors R) f))
    (hloc : ∀ (p : Ideal R) [p.IsPrime], p.height = 1 →
      Function.Surjective (LocalizedModule.map p.primeCompl f)) : Function.Surjective f := by
  let := Module.finitePresentation_of_finite R M
  let := Module.finitePresentation_of_finite R (Module.Dual R M)
  exact f.surjective_of_generic_bijective_of_localized_height_one (K := FractionRing R)
    (LocalizedModule.mkLinearMap (nonZeroDivisors R) M)
    (LocalizedModule.mkLinearMap (nonZeroDivisors R) N) hgen hloc

example {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M]
    [Module.IsReflexive R M] {ι : Type*} [Finite ι] : Module.IsReflexive R (ι → M) :=
  inferInstance
