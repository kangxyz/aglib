/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Cohomology.Projective.HilbertPolynomial.HyperplaneSupport

/-! The support formula applies to the original twist multiplication, including the zero section. -/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.ProjectiveSpace
open AlgebraicGeometry.Scheme.Modules AlgebraicGeometry.Scheme.Modules.QuasiCoherent
open AlgebraicGeometry.Scheme.Modules.Invertible

universe u

example (R : Type u) [CommRing R] (ι : Type u) (a : ℤ)
    (s : Γ(twistingSheaf R ι a, ⊤)) (F : (ProjectiveSpace R ι).Modules)
    (hF : affineLocallyFiniteType (ProjectiveSpace R ι) F) :
    support (cokernel ((twistingTensorZeroIso R ι).inv.app F ≫
      (twistingTensorMultiply R ι a 0 s).app F)) =
      support F ∩ (nonvanishingOpen (twistingLineBundle R ι a) s : Set (ProjectiveSpace R ι))ᶜ :=
  support_cokernel_twistingTensorMultiply R ι a s F hF

end
