/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Cohomology.Restriction.Coefficients
public import Aglib.AlgebraicGeometry.Cohomology.BaseChange.Modules.Map.Open
public import Aglib.AlgebraicGeometry.Cohomology.Modules.Scalars.Iso

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

/-- Postcomposing the original restriction unit agrees with the original
coefficient map after the original open linear equivalence. -/
theorem moduleHPrimeOpenLinearEquiv_postcomp
    (X : Scheme.{u}) {R : Type u} [CommRing R] (α : R →+* Γ(X, ⊤))
    (U : X.Opens) (M : X.Modules) {N : U.toScheme.Modules}
    (ε : M.restrict U.ι ⟶ N) (n : ℕ) :
    let αU := U.ι.appTop.hom.comp α
    let η := (Scheme.Modules.restrictAdjunction U.ι).unit.app M
    let C := moduleHPrimePresheaf U.toScheme αU N n
    let κ := (eqToHom U.ι_preimage_self.symm).op
    letI := moduleHPrimeModuleOfHom X α M n U
    letI := moduleHPrimeModuleOfHom U.toScheme αU N n ⊤
    letI := moduleCohomologyModuleOfHom U.toScheme αU (M.restrict U.ι) n
    letI := moduleCohomologyModuleOfHom U.toScheme αU N n
    (moduleHPrimeRestrictionMap U.ι (RingHom.id R) α αU (by rfl)
      (η ≫ (Scheme.Modules.pushforward U.ι).map ε) n).app (op U) ≫
        (ModuleCat.restrictScalars (RingHom.id R)).map (C.map κ) ≫
        (ModuleCat.restrictScalars (RingHom.id R)).map
          (moduleHPrimeTopLinearEquivOfHom U.toScheme αU N n).toModuleIso.hom =
      (moduleHPrimeOpenLinearEquiv X α M U n).toModuleIso.hom ≫
        ModuleCat.ofHom (moduleCohomologyMapOfHom U.toScheme αU ε n) := by
  let αU := U.ι.appTop.hom.comp α
  let : Module R (Sheaf.H'.{u + 1} (moduleAddSheaf X M) n U) :=
    moduleHPrimeModuleOfHom X α M n U
  let : Module R (Sheaf.H.{u + 1} (moduleAddSheaf U.toScheme N) n) :=
    moduleCohomologyModuleOfHom U.toScheme αU N n
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  change Sheaf.H'.{u + 1} (moduleAddSheaf X M) n U at x
  exact (moduleHPrimeOpenRestrictionAddEquiv_postcomp X U M ε n x).symm

end AlgebraicGeometry.Scheme.Cohomology
