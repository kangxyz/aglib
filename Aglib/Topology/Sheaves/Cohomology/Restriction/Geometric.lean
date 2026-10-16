/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.Topology.Sheaves.Cohomology.Restriction
public import Aglib.Topology.Sheaves.Restriction

/-!
# Geometric normalization of the original open restriction equivalence

The extension-by-zero Ext adjunction gives the same map as actual geometric
inverse image, the original free-open comparison and the original restriction
unit. The only open transport is the native equality between an open and the
inverse image of its image under an open embedding.
-/

@[expose] public section

noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian TopologicalSpace Opposite

namespace TopCat.Sheaf

universe u

variable {X : TopCat.{u}} (U : Opens X)

/-- The original inverse image with its underlying site-sheaf categories displayed explicitly. -/
abbrev openRestrictionInverseImage :
    CategoryTheory.Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u} ⥤
      CategoryTheory.Sheaf (Opens.grothendieckTopology U) AddCommGrpCat.{u} :=
  pullback AddCommGrpCat.{u} U.inclusion'

/-- The original unit-normalized comparison with explicit underlying sheaf categories. -/
abbrev openRestrictionInverseImageIso :
    openRestrictionInverseImage U ≅ U.sheafRestrict (C := AddCommGrpCat.{u}) :=
  openRestrictionPullbackIso U

local instance :
    HasExt.{u + 1} (CategoryTheory.Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}) :=
  HasExt.standard _

local instance :
    HasExt.{u + 1} (CategoryTheory.Sheaf (Opens.grothendieckTopology U) AddCommGrpCat.{u}) :=
  HasExt.standard _

local instance : HasExt.{u + 1} (TopCat.Sheaf AddCommGrpCat.{u} X) := by
  change HasExt.{u + 1}
    (CategoryTheory.Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u})
  exact HasExt.standard _

local instance :
    HasExt.{u + 1} (TopCat.Sheaf AddCommGrpCat.{u} ((Opens.toTopCat X).obj U)) := by
  change HasExt.{u + 1}
    (CategoryTheory.Sheaf (Opens.grothendieckTopology U) AddCommGrpCat.{u})
  exact HasExt.standard _

local instance : (U.sheafRestrict (C := AddCommGrpCat.{u})).IsRightAdjoint :=
  (extensionByZeroRestrictAdjunction U).isRightAdjoint

local instance : (U.sheafRestrict (C := AddCommGrpCat.{u})).Additive where
  map_add := by intros; rfl

local instance : (openRestrictionInverseImage U).Additive :=
  Functor.additive_of_iso (openRestrictionInverseImageIso U).symm

local instance : PreservesFiniteLimits (openRestrictionInverseImage U) :=
  preservesFiniteLimits_of_natIso (openRestrictionInverseImageIso U).symm

local instance : PreservesFiniteColimits (openRestrictionInverseImage U) :=
  preservesFiniteColimits_of_natIso (openRestrictionInverseImageIso U).symm

/-- The original free-open extension unit is the original geometric free-open map. -/
theorem openFreeAbelianRestriction_unit_geometric (V : Opens U) :
    (extensionByZeroRestrictAdjunction U).unit.app
        ((openFreeAbelianFunctor (TopCat.of U)).obj V) ≫
      (U.sheafRestrict (C := AddCommGrpCat.{u})).map
        (openFreeAbelianExtensionByZeroObjIso U V).hom =
    (openFreeAbelianFunctor (TopCat.of U)).map
        (eqToHom (Opens.map_functor_eq V).symm) ≫
      (openFreeAbelianPullbackObjIso U.inclusion' (U.isOpenEmbedding.functor.obj V)).inv ≫
        (openRestrictionPullbackIso U).hom.app
          ((openFreeAbelianFunctor X).obj (U.isOpenEmbedding.functor.obj V)) := by
  let W := U.isOpenEmbedding.functor.obj V
  let F := (openFreeAbelianFunctor X).obj W
  let q := eqToHom (Opens.map_functor_eq V).symm
  have hs := openFreeAbelianExtensionByZeroHomEquiv_sections U V F
    (openFreeAbelianExtensionByZeroObjIso U V).hom
  rw [openFreeAbelianExtensionByZeroHomEquiv_hom] at hs
  rw [Adjunction.homEquiv_unit] at hs
  apply (openFreeAbelianHomEquiv (TopCat.of U) V
    ((U.sheafRestrict (C := AddCommGrpCat.{u})).obj F)).injective
  rw [← hs]
  symm
  erw [openFreeAbelianHomEquiv_naturality (TopCat.of U) q
    ((U.sheafRestrict (C := AddCommGrpCat.{u})).obj F)
    ((openFreeAbelianPullbackObjIso U.inclusion' W).inv ≫
      (openRestrictionPullbackIso U).hom.app F)]
  rw [← openFreeAbelianPullbackHomEquiv_eq U.inclusion' W
    ((U.sheafRestrict (C := AddCommGrpCat.{u})).obj F)
    ((openRestrictionPullbackIso U).hom.app F)]
  erw [openFreeAbelianPullbackHomEquiv_sections U.inclusion' W
    ((U.sheafRestrict (C := AddCommGrpCat.{u})).obj F)
    ((openRestrictionPullbackIso U).hom.app F)]
  erw [openRestrictionPullbackIso_homEquiv U F]
  have hu := openFreeAbelianHomEquiv_comp X W (𝟙 F)
    ((openRestrictPushforwardAdjunction U).unit.app F)
  rw [Category.id_comp] at hu
  erw [hu, openRestrictPushforwardAdjunction_unit_app U F W]
  change F.obj.map (U.isOpenEmbedding.functor.map q).op
      (F.obj.map (U.isOpenEmbedding.isOpenMap.adjunction.counit.app W).op
        (openFreeAbelianHomEquiv X W F (𝟙 F))) = _
  change (F.obj.map (U.isOpenEmbedding.isOpenMap.adjunction.counit.app W).op ≫
    F.obj.map (U.isOpenEmbedding.functor.map q).op)
      (openFreeAbelianHomEquiv X W F (𝟙 F)) = openFreeAbelianHomEquiv X W F (𝟙 F)
  rw [← F.obj.map_comp]
  have h : (U.isOpenEmbedding.isOpenMap.adjunction.counit.app W).op ≫
      (U.isOpenEmbedding.functor.map q).op = 𝟙 (op W) := Subsingleton.elim _ _
  rw [h]
  exact ConcreteCategory.congr_hom (F.obj.map_id (op W)) _

/-- The actual open-Ext restriction equivalence is the original geometric inverse-image
map, with the original restriction coefficient and native inverse-image/image transport. -/
theorem cohomologyOpenRestrictionAddEquiv_geometric
    (F : CategoryTheory.Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u})
    (n : ℕ) (V : Opens U)
    (x : CategoryTheory.Sheaf.H'.{u + 1} F n (U.isOpenEmbedding.functor.obj V)) :
    cohomologyOpenRestrictionAddEquiv U F n V x =
      (Ext.mk₀ ((openFreeAbelianFunctor (TopCat.of U)).map
          (eqToHom (Opens.map_functor_eq V).symm))).comp
        (((Ext.mk₀ ((openFreeAbelianPullbackObjIso U.inclusion'
            (U.isOpenEmbedding.functor.obj V)).inv)).comp
          (x.mapExactFunctor (openRestrictionInverseImage U)) (Nat.zero_add n)).comp
            (Ext.mk₀ ((openRestrictionInverseImageIso U).hom.app F)) (Nat.add_zero n))
        (Nat.zero_add n) := by
  rw [cohomologyOpenRestrictionAddEquiv_apply, openFreeAbelianRestriction_unit_geometric]
  have hn := Ext.mapExactFunctor_comp_mk₀_natTransApp x (openRestrictionInverseImageIso U).hom
  rw [Ext.comp_assoc_of_third_deg_zero, hn]
  simp only [← Ext.mk₀_comp_mk₀, Ext.comp_assoc_of_second_deg_zero]
  rfl

end TopCat.Sheaf
