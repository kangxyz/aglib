/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Cohomology.Restriction.LinearCoefficients
public import Aglib.AlgebraicGeometry.Cohomology.BaseChange.Modules.Map.ExtScalarSquare.RestrictionMap
public import Mathlib.CategoryTheory.ConcreteCategory.EpiMono

/-! # Invertibility of the original coefficient-restriction composite

The original coefficient arrow acts on unchanged cohomology. Its invertibility
makes the original restriction, index transport and top comparison invertible,
without introducing a second presentation by coefficient cohomology isomorphisms.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
universe u
open CategoryTheory AlgebraicGeometry TopologicalSpace Opposite
namespace AlgebraicGeometry.Scheme.Cohomology

/-- The original structural-linear coefficient map preserves invertibility. -/
theorem moduleCohomologyMapOfHom_isIso (X : Scheme.{u}) {R : Type u} [CommRing R]
    (α : R →+* Γ(X, ⊤)) {M N : X.Modules} (ε : M ⟶ N) [IsIso ε] (n : ℕ) :
    letI := moduleCohomologyModuleOfHom X α M n
    letI := moduleCohomologyModuleOfHom X α N n
    IsIso (ModuleCat.ofHom (moduleCohomologyMapOfHom X α ε n)) := by
  let := moduleCohomologyModuleOfHom X α M n
  let := moduleCohomologyModuleOfHom X α N n
  apply (ConcreteCategory.isIso_iff_bijective _).mpr
  exact bijective_sheafH_map_of_iso (asIso ε) n

/-- The shared original normalized map is invertible for an invertible coefficient. -/
theorem moduleHPrimeRestrictionPostcompMap_isIso
    (X : Scheme.{u}) {R : Type u} [CommRing R] (α : R →+* Γ(X, ⊤))
    (U : X.Opens) (M : X.Modules) {N : U.toScheme.Modules}
    (ε : M.restrict U.ι ⟶ N) [IsIso ε] (n : ℕ) :
    IsIso (moduleHPrimeRestrictionPostcompMap X α U M ε n) := by
  let αU := U.ι.appTop.hom.comp α
  let := moduleHPrimeModuleOfHom X α M n U
  let := moduleHPrimeModuleOfHom U.toScheme αU N n ⊤
  let := moduleCohomologyModuleOfHom U.toScheme αU (M.restrict U.ι) n
  let := moduleCohomologyModuleOfHom U.toScheme αU N n
  let : IsIso (ModuleCat.ofHom (moduleCohomologyMapOfHom U.toScheme αU ε n)) :=
    moduleCohomologyMapOfHom_isIso U.toScheme αU ε n
  exact (congrArg (fun f => IsIso f)
    ((moduleHPrimeRestrictionPostcompMap_eq X α U M ε n).trans
      (moduleHPrimeOpenLinearEquiv_postcomp X α U M ε n))).mpr (by infer_instance)

/-- Compatibility with the unchanged expanded raw-map interface. -/
theorem moduleHPrimeRestriction_postcomp_isIso
    (X : Scheme.{u}) {R : Type u} [CommRing R] (α : R →+* Γ(X, ⊤))
    (U : X.Opens) (M : X.Modules) {N : U.toScheme.Modules}
    (ε : M.restrict U.ι ⟶ N) [IsIso ε] (n : ℕ) :
    let αU := U.ι.appTop.hom.comp α
    let η := (Scheme.Modules.restrictAdjunction U.ι).unit.app M
    let C := moduleHPrimePresheaf U.toScheme αU N n
    let κ := (eqToHom U.ι_preimage_self.symm).op
    letI := moduleHPrimeModuleOfHom X α M n U
    letI := moduleHPrimeModuleOfHom U.toScheme αU N n ⊤
    letI := moduleCohomologyModuleOfHom U.toScheme αU (M.restrict U.ι) n
    letI := moduleCohomologyModuleOfHom U.toScheme αU N n
    IsIso ((moduleHPrimeRestrictionMap U.ι (RingHom.id R) α αU (by rfl)
      (η ≫ (Scheme.Modules.pushforward U.ι).map ε) n).app (op U) ≫
        (ModuleCat.restrictScalars (RingHom.id R)).map (C.map κ) ≫
        (ModuleCat.restrictScalars (RingHom.id R)).map
          (moduleHPrimeTopLinearEquivOfHom U.toScheme αU N n).toModuleIso.hom) := by
  exact (congrArg (fun f => IsIso f)
    (moduleHPrimeRestrictionPostcompMap_eq X α U M ε n)).mp
      (moduleHPrimeRestrictionPostcompMap_isIso X α U M ε n)

end AlgebraicGeometry.Scheme.Cohomology
