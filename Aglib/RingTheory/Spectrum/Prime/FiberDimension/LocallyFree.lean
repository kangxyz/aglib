/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.RingTheory.Spectrum.Prime.FiberDimension.BaseChange
public import Aglib.RingTheory.Spectrum.Prime.FiberDimension.Reduced
public import Aglib.RingTheory.Spectrum.Prime.FiberDimension.Flat
public import Mathlib.RingTheory.LocalProperties.Reduced

/-!
# Finite projectivity from locally constant fibre rank over a reduced ring

A finitely presented module over a reduced ring is projective exactly
when its original residue-field fibre dimensions are locally constant.
For the converse, the original arbitrary scalar-extension dimension
formula transports local constancy to every prime localization. The
reduced local criterion gives freeness there, and the native free-locus
criterion gives projectivity. No Noetherianity is assumed.
-/

@[expose] public section

noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open TensorProduct Module

namespace Module

variable (R M : Type*) [CommRing R] [IsReduced R]
    [AddCommGroup M] [Module R M] [Module.FinitePresentation R M]

/-- Over a reduced ring, a finitely presented module with locally constant original
fibre dimensions is finite projective. Ring and module universes remain independent. -/
theorem projective_of_isLocallyConstant_finrank_fiber_of_isReduced
    (h : IsLocallyConstant (fun p : PrimeSpectrum R =>
      finrank p.asIdeal.ResidueField (p.asIdeal.Fiber M))) : Module.Projective R M := by
  apply (Module.freeLocus_eq_univ_iff (R := R) (M := M)).mp
  apply Set.eq_univ_iff_forall.mpr
  intro p
  let A := Localization.AtPrime p.asIdeal
  apply (Module.mem_freeLocus_iff_tensor p A).mpr
  apply Module.free_of_isLocallyConstant_finrank_fiber_of_isReduced A (A ⊗[R] M)
  have he : (fun q : PrimeSpectrum A =>
      finrank q.asIdeal.ResidueField (q.asIdeal.Fiber (A ⊗[R] M))) =
      fun q => finrank (PrimeSpectrum.comap (algebraMap R A) q).asIdeal.ResidueField
        ((PrimeSpectrum.comap (algebraMap R A) q).asIdeal.Fiber M) :=
    funext (Module.finrank_fiber_baseChange R A M)
  rw [he]
  exact h.comp_continuous (PrimeSpectrum.continuous_comap (algebraMap R A))

/-- The usual finite-projective/locally-constant-fibre-rank criterion over a reduced
ring, with finite presentation retained explicitly. -/
theorem projective_iff_isLocallyConstant_finrank_fiber_of_isReduced :
    Module.Projective R M ↔ IsLocallyConstant (fun p : PrimeSpectrum R =>
      finrank p.asIdeal.ResidueField (p.asIdeal.Fiber M)) := by
  constructor
  · intro h
    let : Module.Projective R M := h
    exact Module.isLocallyConstant_finrank_fiber R M
  · exact Module.projective_of_isLocallyConstant_finrank_fiber_of_isReduced R M

end Module
