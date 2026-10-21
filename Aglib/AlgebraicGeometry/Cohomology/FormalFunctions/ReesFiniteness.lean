/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Modules.Rees.Geometry
public import Aglib.AlgebraicGeometry.Cohomology.Proper.Finiteness

/-!
# Finiteness of the original cohomology of the geometric Rees image

This is the proper-cohomology step, before comparison with the direct sum of
ideal-power cohomology. It asserts finiteness with the actual structural Rees
action and requires no relative flatness or assumed formal-functions theorem.
-/

@[expose] public noncomputable section

universe u
open CategoryTheory

namespace AlgebraicGeometry.Scheme.Cohomology

/-- Proper finiteness applied to the actual geometric Rees image coefficient. -/
theorem reesCoefficient_cohomology_finite
    {A : Type u} [CommRing A] [IsNoetherianRing A] (I : Ideal A)
    {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of A)) [IsProper f]
    (F : X.Modules) (hF : Modules.QuasiCoherent.affineLocallyFiniteType X F) (q : ℕ) :
    let Y := Modules.Rees.space I f
    let G := Modules.Rees.coefficient I f F
    let α := (Modules.Rees.structureMap I f).appTop.hom.comp
      (Scheme.ΓSpecIso (.of (reesAlgebra I))).inv.hom
    letI := moduleCohomologyModuleOfHom Y α G q
    Module.Finite (reesAlgebra I) (Sheaf.H.{u + 1} (moduleAddSheaf Y G) q) :=
  moduleCohomology_finite_of_proper (reesAlgebra I) (Modules.Rees.structureMap I f)
    (Modules.Rees.coefficient I f F)
    (Modules.Rees.affineLocallyFiniteType_coefficient I f F hF) q

end AlgebraicGeometry.Scheme.Cohomology
