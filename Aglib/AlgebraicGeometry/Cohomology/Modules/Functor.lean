/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Cohomology.Modules.Scalars

/-!
# The actual cohomology functor with specified structural scalars

For a specified ring map to global functions, original additive sheaf cohomology and its
original coefficient maps form an additive functor to modules over that ring. Forgetting
scalars gives the native sheaf-cohomology functor by the identity isomorphism. In particular,
native preservation of finite biproducts applies to these unchanged cohomology groups.
-/

@[expose] public section

noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory TopologicalSpace

universe u

namespace AlgebraicGeometry.Scheme.Cohomology

variable (X : Scheme.{u}) {R : Type u} [CommRing R]
  (α : R →+* Γ(X, ⊤)) (n : ℕ)

/-- Original sheaf cohomology as a module-valued functor for the specified structural
ring map. Both its object action and coefficient maps are the existing scalar interfaces. -/
def moduleCohomologyFunctorOfHom : X.Modules ⥤ ModuleCat.{u + 1} R where
  obj M := by
    letI := moduleCohomologyModuleOfHom X α M n
    exact ModuleCat.of R (Sheaf.H.{u + 1} (moduleAddSheaf X M) n)
  map {M N} φ := by
    letI := moduleCohomologyModuleOfHom X α M n
    letI := moduleCohomologyModuleOfHom X α N n
    exact ModuleCat.ofHom (moduleCohomologyMapOfHom X α φ n)
  map_id M := by
    apply (forget₂ (ModuleCat.{u + 1} R) AddCommGrpCat).map_injective
    exact ((SheafOfModules.toSheaf.{u} X.ringCatSheaf) ⋙ Sheaf.functorH _ n).map_id M
  map_comp φ ψ := by
    apply (forget₂ (ModuleCat.{u + 1} R) AddCommGrpCat).map_injective
    exact ((SheafOfModules.toSheaf.{u} X.ringCatSheaf) ⋙ Sheaf.functorH _ n).map_comp φ ψ

/-- Forgetting the specified structural scalars recovers the native additive-coefficient
cohomology functor by the literal identity. -/
def moduleCohomologyFunctorOfHomForgetIso :
    moduleCohomologyFunctorOfHom X α n ⋙ forget₂ (ModuleCat.{u + 1} R) AddCommGrpCat ≅
      (SheafOfModules.toSheaf.{u} X.ringCatSheaf) ⋙ Sheaf.functorH _ n := Iso.refl _

/-- The module-valued coefficient map is exactly the existing map on original `Sheaf.H`. -/
theorem moduleCohomologyFunctorOfHom_map_apply {M N : X.Modules} (φ : M ⟶ N)
    (x : Sheaf.H.{u + 1} (moduleAddSheaf X M) n) :
    (moduleCohomologyFunctorOfHom X α n).map φ x =
      Sheaf.H.map ((SheafOfModules.toSheaf.{u} X.ringCatSheaf).map φ) n x := rfl

instance moduleCohomologyFunctorOfHom_additive :
    (moduleCohomologyFunctorOfHom X α n).Additive := by
  let : (moduleCohomologyFunctorOfHom X α n ⋙
      forget₂ (ModuleCat.{u + 1} R) AddCommGrpCat).Additive :=
    inferInstanceAs
      (((SheafOfModules.toSheaf.{u} X.ringCatSheaf) ⋙ Sheaf.functorH _ n).Additive)
  exact Functor.additive_of_comp_faithful (moduleCohomologyFunctorOfHom X α n)
    (forget₂ (ModuleCat.{u + 1} R) AddCommGrpCat)

end AlgebraicGeometry.Scheme.Cohomology
