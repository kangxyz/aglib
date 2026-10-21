/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Cohomology.Modules.Sections
public import Mathlib.AlgebraicGeometry.AffineScheme
public import Mathlib.Topology.Sheaves.Forget
public import Mathlib.Topology.Sheaves.SheafCondition.Sites

/-!
# Extending actual scalar-linear affine section comparisons

Natural comparisons on the affine basis extend uniquely to the original
scalar-linear section sheaves. This helper does not identify arbitrary
sectionwise images or impose any formal-functions comparison premise.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

universe u
open CategoryTheory Limits Opposite TopologicalSpace

namespace AlgebraicGeometry.Scheme.Cohomology

variable {A : Type u} [CommRing A] (X : Scheme.{u}) (α : A →+* Γ(X, ⊤))

/-- Actual scalar-restricted sections remain a module-valued sheaf. -/
theorem moduleSectionsPresheaf_isSheaf (M : X.Modules) :
    TopCat.Presheaf.IsSheaf (moduleSectionsPresheaf X α M) := by
  apply (TopCat.Presheaf.isSheaf_iff_isSheaf_comp
    (forget₂ (ModuleCat.{u} A) AddCommGrpCat.{u}) _).mpr
  exact M.isSheaf

/-- The module-valued sheaf whose sections are the original structural scalar modules. -/
def moduleSectionsSheaf (M : X.Modules) : TopCat.Sheaf (ModuleCat.{u} A) X :=
  ⟨moduleSectionsPresheaf X α M, moduleSectionsPresheaf_isSheaf X α M⟩

/-- The explicit inclusion of affine opens has basis range. -/
theorem affineOpens_range_isBasis :
    Opens.IsBasis (Set.range (fun U : X.affineOpens => U.val)) := by
  simpa only [Subtype.range_coe_subtype, Set.ofPred_mem_eq] using X.isBasis_affineOpens

/-- A natural affine-basis section comparison extends to the actual section presheaves. -/
def moduleSectionsIsoOfAffine (M N : X.Modules)
    (e : (inducedFunctor (fun U : X.affineOpens => U.val)).op ⋙
        moduleSectionsPresheaf X α M ≅
      (inducedFunctor (fun U : X.affineOpens => U.val)).op ⋙
        moduleSectionsPresheaf X α N) :
    moduleSectionsPresheaf X α M ≅ moduleSectionsPresheaf X α N where
  hom := TopCat.Sheaf.restrictHomEquivHom _ (moduleSectionsSheaf X α N)
    (affineOpens_range_isBasis X) e.hom
  inv := TopCat.Sheaf.restrictHomEquivHom _ (moduleSectionsSheaf X α M)
    (affineOpens_range_isBasis X) e.inv
  hom_inv_id := by
    apply TopCat.Sheaf.hom_ext _ (moduleSectionsSheaf X α M) (affineOpens_range_isBasis X)
    intro U
    simp only [NatTrans.comp_app, TopCat.Sheaf.extend_hom_app, NatTrans.id_app]
    exact e.hom_inv_id_app (op U)
  inv_hom_id := by
    apply TopCat.Sheaf.hom_ext _ (moduleSectionsSheaf X α N) (affineOpens_range_isBasis X)
    intro U
    simp only [NatTrans.comp_app, TopCat.Sheaf.extend_hom_app, NatTrans.id_app]
    exact e.inv_hom_id_app (op U)

/-- Extension changes no affine section map. -/
@[simp]
theorem moduleSectionsIsoOfAffine_hom_app (M N : X.Modules)
    (e : (inducedFunctor (fun U : X.affineOpens => U.val)).op ⋙
        moduleSectionsPresheaf X α M ≅
      (inducedFunctor (fun U : X.affineOpens => U.val)).op ⋙
        moduleSectionsPresheaf X α N) (U : X.affineOpens) :
    (moduleSectionsIsoOfAffine X α M N e).hom.app (op U.val) = e.hom.app (op U) :=
  TopCat.Sheaf.extend_hom_app _ _ _ _ _

end AlgebraicGeometry.Scheme.Cohomology
