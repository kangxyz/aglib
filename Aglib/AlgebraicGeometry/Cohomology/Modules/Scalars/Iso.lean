/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Cohomology.Modules.Scalars

/-! # The original structural-linear cohomology maps of coefficient isomorphisms

An actual module-sheaf isomorphism induces the original coefficient maps in
both directions on unchanged `Sheaf.H`. Their structural linearity is the
existing coefficient linearity; functoriality proves the inverse equations. In particular the
additive coefficient map of an isomorphism is bijective (`bijective_sheafH_map_of_iso`).
-/

@[expose] public section

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

universe u

open CategoryTheory AlgebraicGeometry TopologicalSpace Opposite

namespace AlgebraicGeometry.Scheme.Cohomology

variable (X : Scheme.{u}) {R : Type u} [CommRing R]
  (α : R →+* Γ(X, ⊤)) {M N : X.Modules}

/-- An actual coefficient isomorphism induces the original structural-linear cohomology maps. -/
def moduleCohomologyIsoOfHom (e : M ≅ N) (n : ℕ) :
    letI := moduleCohomologyModuleOfHom X α M n
    letI := moduleCohomologyModuleOfHom X α N n
    ModuleCat.of R (Sheaf.H.{u + 1} (moduleAddSheaf X M) n) ≅
      ModuleCat.of R (Sheaf.H.{u + 1} (moduleAddSheaf X N) n) := by
  letI := moduleCohomologyModuleOfHom X α M n
  letI := moduleCohomologyModuleOfHom X α N n
  refine {
    hom := ModuleCat.ofHom (moduleCohomologyMapOfHom X α e.hom n)
    inv := ModuleCat.ofHom (moduleCohomologyMapOfHom X α e.inv n)
    hom_inv_id := ?_
    inv_hom_id := ?_ }
  · ext x
    change Sheaf.H.map ((SheafOfModules.toSheaf X.ringCatSheaf).map e.inv) n
      (Sheaf.H.map ((SheafOfModules.toSheaf X.ringCatSheaf).map e.hom) n x) = x
    erw [← Sheaf.H.map_comp_apply, ← CategoryTheory.Functor.map_comp, e.hom_inv_id,
      CategoryTheory.Functor.map_id]
    exact Sheaf.H.map_id_apply x
  · ext x
    change Sheaf.H.map ((SheafOfModules.toSheaf X.ringCatSheaf).map e.hom) n
      (Sheaf.H.map ((SheafOfModules.toSheaf X.ringCatSheaf).map e.inv) n x) = x
    erw [← Sheaf.H.map_comp_apply, ← CategoryTheory.Functor.map_comp, e.inv_hom_id,
      CategoryTheory.Functor.map_id]
    exact Sheaf.H.map_id_apply x

/-- The forward comparison is the original additive coefficient map on unchanged cohomology. -/
theorem moduleCohomologyIsoOfHom_hom_apply (e : M ≅ N) (n : ℕ)
    (x : Sheaf.H.{u + 1} (moduleAddSheaf X M) n) :
    letI := moduleCohomologyModuleOfHom X α M n
    letI := moduleCohomologyModuleOfHom X α N n
    (moduleCohomologyIsoOfHom X α e n).hom x =
      Sheaf.H.map ((SheafOfModules.toSheaf X.ringCatSheaf).map e.hom) n x := rfl

/-- The inverse comparison is the original coefficient map of the actual inverse. -/
theorem moduleCohomologyIsoOfHom_inv_apply (e : M ≅ N) (n : ℕ)
    (x : Sheaf.H.{u + 1} (moduleAddSheaf X N) n) :
    letI := moduleCohomologyModuleOfHom X α M n
    letI := moduleCohomologyModuleOfHom X α N n
    (moduleCohomologyIsoOfHom X α e n).inv x =
      Sheaf.H.map ((SheafOfModules.toSheaf X.ringCatSheaf).map e.inv) n x := rfl

end AlgebraicGeometry.Scheme.Cohomology

namespace AlgebraicGeometry.Scheme.Cohomology

/-- An isomorphism of modules induces bijections on sheaf cohomology. -/
theorem bijective_sheafH_map_of_iso {X : Scheme.{u}} {M N : X.Modules} (e : M ≅ N) (q : ℕ) :
    Function.Bijective (Sheaf.H.map ((SheafOfModules.toSheaf X.ringCatSheaf).map e.hom) q) :=
  (moduleCohomologyIsoOfHom X (RingHom.id Γ(X, ⊤)) e q).toLinearEquiv.bijective

end AlgebraicGeometry.Scheme.Cohomology
