/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Cohomology.GrothendieckExistence.AffineHomRecovery

/-! # Recover original coherent affine isomorphisms from their section equivalences -/

@[expose] public noncomputable section
open CategoryTheory

namespace AlgebraicGeometry.Scheme.Modules.Coherent

universe u
variable {B : CommRingCat.{u}} [IsNoetherianRing B]

/-- Lift an actual section equivalence through the native finite-type equivalence. -/
def affineIsoOfSections (M N : (Spec B).CoherentSheaf)
    (e : moduleSpecΓFunctor.obj M.obj ≃ₗ[B] moduleSpecΓFunctor.obj N.obj) : M ≅ N :=
  (QuasiCoherent.finiteTypeSheavesSpecModuleEquivalence B).functor.preimageIso
    (ObjectProperty.isoMk _ e.toModuleIso)

/-- The recovered isomorphism has exactly the given original section map. -/
theorem affineIsoOfSections_map (M N : (Spec B).CoherentSheaf)
    (e : moduleSpecΓFunctor.obj M.obj ≃ₗ[B] moduleSpecΓFunctor.obj N.obj) :
    moduleSpecΓFunctor.map (affineIsoOfSections M N e).hom.hom = e.toModuleIso.hom :=
  affineHomOfSections_map M N e.toModuleIso.hom

end AlgebraicGeometry.Scheme.Modules.Coherent
