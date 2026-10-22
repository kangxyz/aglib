/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Cohomology.GrothendieckExistence.ClosedImmersionReduction.Annihilation
public import Aglib.AlgebraicGeometry.Modules.Coherent.AdicSystem.AmbientExact

/-! # Proper completion reflects bounds on ordinary coherent cokernels

The argument uses right exactness of actual quotient functors and proper
completion faithfulness, not faithful flatness of an affine chart completion.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry.Scheme.Modules
open AlgebraicGeometry.Scheme.Modules.Coherent

namespace AlgebraicGeometry.Scheme.Cohomology

universe u

variable {A : Type u} [CommRing A] [IsNoetherianRing A]
  (I : Ideal A) [IsAdicComplete I A] {X : Scheme.{u}}
  [IsLocallyNoetherian X] (f : X ⟶ Spec (CommRingCat.of A)) [IsProper f]

/-- A uniform ideal bound on all ordinary reduced cokernels is a bound
on the actual algebraic coherent cokernel. -/
theorem killedByIdealSheaf_cokernel_of_completion (K : X.IdealSheafData)
    {M N : X.CoherentSheaf} (φ : M ⟶ N)
    (h : ∀ n : ℕ, killedByIdealSheaf K
      (cokernel ((idealSheafQuotientFunctor X (idealThickeningIdealSheaf f I ^ n)).map
        φ.hom))) :
    killedByIdealSheaf K (cokernel φ.hom) := by
  let C : X.CoherentSheaf := ⟨cokernel φ.hom,
    (QuasiCoherent.affineLocallyFiniteType X).prop_cokernel φ.hom M.property N.property⟩
  have hc := killedByIdealSheaf_of_completion I K.subschemeι f C (fun n => by
    rw [K.ker_subschemeι]
    exact killedByIdealSheaf_of_iso K
      (PreservesCokernel.iso
        (idealSheafQuotientFunctor X (idealThickeningIdealSheaf f I ^ n)) φ.hom).symm
      (h n))
  simpa only [IdealSheafData.ker_subschemeι] using hc

end AlgebraicGeometry.Scheme.Cohomology
