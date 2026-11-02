/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Cohomology.Restriction.LinearCoefficients

/-! # Original linear compatibility of open restriction and coefficient maps

The four original coefficient-restriction edges are compared before any
cartesian pullback specialization. The whole accepted additive coefficient
square supplies its law; scalar actions and linear maps remain the originals.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

universe u
open CategoryTheory AlgebraicGeometry TopologicalSpace Opposite

namespace AlgebraicGeometry.Scheme.Cohomology

/-- The inverse coefficient map is the original linear cohomology iso map. -/
theorem moduleCohomologyMapOfHom_iso_inv (X : Scheme.{u}) {R : Type u} [CommRing R]
    (α : R →+* Γ(X, ⊤)) {M N : X.Modules} (e : N ≅ M) (n : ℕ) :
    letI := moduleCohomologyModuleOfHom X α M n
    letI := moduleCohomologyModuleOfHom X α N n
    ModuleCat.ofHom (moduleCohomologyMapOfHom X α e.inv n) =
      (moduleCohomologyIsoOfHom X α e.symm n).hom := rfl

/-- Postcomposing the original restriction unit agrees with the original
coefficient map after the original open linear equivalence. -/
theorem moduleHPrimeOpenLinearEquiv_postcomp_iso
    (X : Scheme.{u}) {R : Type u} [CommRing R] (α : R →+* Γ(X, ⊤))
    (U : X.Opens) (M : X.Modules) {N : U.toScheme.Modules}
    (e : N ≅ M.restrict U.ι) (n : ℕ) :
    let αU := U.ι.appTop.hom.comp α
    let η := (Scheme.Modules.restrictAdjunction U.ι).unit.app M
    let C := moduleHPrimePresheaf U.toScheme αU N n
    let κ := (eqToHom U.ι_preimage_self.symm).op
    letI := moduleHPrimeModuleOfHom X α M n U
    letI := moduleHPrimeModuleOfHom U.toScheme αU N n ⊤
    letI := moduleCohomologyModuleOfHom U.toScheme αU (M.restrict U.ι) n
    letI := moduleCohomologyModuleOfHom U.toScheme αU N n
    (moduleHPrimeRestrictionMap U.ι (RingHom.id R) α αU (by rfl)
      (η ≫ (Scheme.Modules.pushforward U.ι).map e.inv) n).app (op U) ≫
        (ModuleCat.restrictScalars (RingHom.id R)).map (C.map κ) ≫
        (ModuleCat.restrictScalars (RingHom.id R)).map
          (moduleHPrimeTopLinearEquivOfHom U.toScheme αU N n).toModuleIso.hom =
      (moduleHPrimeOpenLinearEquiv X α M U n).toModuleIso.hom ≫
        (moduleCohomologyIsoOfHom U.toScheme αU e.symm n).hom := by
  exact (moduleHPrimeOpenLinearEquiv_postcomp X α U M e.inv n).trans
    (congrArg (fun f => (moduleHPrimeOpenLinearEquiv X α M U n).toModuleIso.hom ≫ f)
      (moduleCohomologyMapOfHom_iso_inv U.toScheme (U.ι.appTop.hom.comp α) e n))

end AlgebraicGeometry.Scheme.Cohomology
