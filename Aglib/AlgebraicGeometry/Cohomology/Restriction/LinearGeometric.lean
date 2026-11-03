/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Cohomology.Restriction.LinearCoefficients

/-! # The original geometric open restriction as a complete linear equality -/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

universe u
open CategoryTheory AlgebraicGeometry TopologicalSpace Opposite

namespace AlgebraicGeometry.Scheme.Cohomology

/-- The original restriction unit, preimage transport and top comparison
compose to the original open linear equivalence. -/
theorem moduleHPrimeOpenLinearEquiv_geometric_hom
    (X : Scheme.{u}) {R : Type u} [CommRing R] (α : R →+* Γ(X, ⊤))
    (U : X.Opens) (M : X.Modules) (n : ℕ) :
    let αU := U.ι.appTop.hom.comp α
    let L := M.restrict U.ι
    let φ := (Scheme.Modules.restrictAdjunction U.ι).unit.app M
    let C := moduleHPrimePresheaf U.toScheme αU L n
    let κ := (eqToHom U.ι_preimage_self.symm).op
    letI := moduleHPrimeModuleOfHom X α M n U
    letI := moduleHPrimeModuleOfHom U.toScheme αU L n ⊤
    letI := moduleCohomologyModuleOfHom U.toScheme αU L n
    (moduleHPrimeRestrictionMap U.ι (RingHom.id R) α αU (by rfl) φ n).app (op U) ≫
        (ModuleCat.restrictScalars (RingHom.id R)).map (C.map κ) ≫
        (ModuleCat.restrictScalars (RingHom.id R)).map
          (moduleHPrimeTopLinearEquivOfHom U.toScheme αU L n).toModuleIso.hom =
      (moduleHPrimeOpenLinearEquiv X α M U n).toModuleIso.hom := by
  let : Module R (Sheaf.H'.{u + 1} (moduleAddSheaf X M) n U) :=
    moduleHPrimeModuleOfHom X α M n U
  let : Module R (Sheaf.H.{u + 1} (moduleAddSheaf U.toScheme (M.restrict U.ι)) n) :=
    moduleCohomologyModuleOfHom U.toScheme (U.ι.appTop.hom.comp α) (M.restrict U.ι) n
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  change Sheaf.H'.{u + 1} (moduleAddSheaf X M) n U at x
  exact (moduleHPrimeOpenLinearEquiv_geometric X α M U n x).symm

end AlgebraicGeometry.Scheme.Cohomology
