/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Mathlib.AlgebraicGeometry.Fiber
public import Mathlib.Topology.Sheaves.Stalks

/-!
# The ordinary pushforward-stalk map to actual fibre sections

Sections over inverse images of neighborhoods of a point restrict to the literal
scheme-theoretic fibre. Their compatibility defines a map from the ordinary pushforward
stalk to the actual fibre's global sections. The original structure-sheaf map and germs
commute with this construction.

The proper Noetherian assertion about idempotents in the image of this map is a separate
obligation. No idempotent preimage or completed or etale stalk is introduced here.
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite TopologicalSpace
open scoped AlgebraicGeometry

namespace AlgebraicGeometry.Scheme.Cohomology.ProperFibreIdempotents

universe u

variable {X Y : Scheme.{u}} (f : X ⟶ Y) (y : Y)

/-- Every point of the actual fibre lies over every neighborhood of its base point. -/
theorem fibreRestriction_le (U : Y.Opens) (hy : y ∈ U) :
    ⊤ ≤ (f.fiberι y) ⁻¹ᵁ (f ⁻¹ᵁ U) := by
  intro z _
  change f (f.fiberι y z) ∈ U
  have hz : f (f.fiberι y z) = y := (f.range_fiberι y).le ⟨z, rfl⟩
  rw [hz]
  exact hy

/-- Restriction of actual inverse-image sections to the same scheme-theoretic fibre. -/
def fibreSectionRestriction (U : Y.Opens) (hy : y ∈ U) :
    Γ(X, f ⁻¹ᵁ U) ⟶ Γ(f.fiber y, ⊤) :=
  (f.fiberι y).appLE (f ⁻¹ᵁ U) ⊤ (fibreRestriction_le f y U hy)

/-- The actual neighborhood-restriction cocone defining the ordinary stalk map. -/
def restrictionCocone :
    Cocone ((OpenNhds.inclusion y).op ⋙ (f.base _* X.presheaf)) where
  pt := Γ(f.fiber y, ⊤)
  ι := {
    app := fun U => fibreSectionRestriction f y U.unop.1 U.unop.2
    naturality := by
      intro U V k
      change X.presheaf.map
          ((TopologicalSpace.Opens.map f.base).map
            ((OpenNhds.inclusion y).map k.unop)).op ≫
          (f.fiberι y).appLE (f ⁻¹ᵁ V.unop.1) ⊤
            (fibreRestriction_le f y V.unop.1 V.unop.2) =
        (f.fiberι y).appLE (f ⁻¹ᵁ U.unop.1) ⊤
          (fibreRestriction_le f y U.unop.1 U.unop.2)
      exact (f.fiberι y).map_appLE
        (fibreRestriction_le f y V.unop.1 V.unop.2)
        ((TopologicalSpace.Opens.map f.base).map
          ((OpenNhds.inclusion y).map k.unop)).op }

/-- The canonical map from the ordinary pushforward stalk to actual fibre sections. -/
def stalkToFibreSections :
    (f.base _* X.presheaf).stalk y ⟶ Γ(f.fiber y, ⊤) :=
  colimit.desc _ (restrictionCocone f y)

@[reassoc]
theorem germ_stalkToFibreSections (U : Y.Opens) (hy : y ∈ U) :
    (f.base _* X.presheaf).germ U y hy ≫ stalkToFibreSections f y =
      fibreSectionRestriction f y U hy :=
  colimit.ι_desc (restrictionCocone f y) (op ⟨U, hy⟩)

/-- The original structure-sheaf map agrees with restriction on every actual germ. -/
@[reassoc]
theorem structureMap_germ_stalkToFibreSections (U : Y.Opens) (hy : y ∈ U) :
    Y.presheaf.germ U y hy ≫
        (TopCat.Presheaf.stalkFunctor CommRingCat.{u} y).map f.c ≫
        stalkToFibreSections f y =
      f.app U ≫ fibreSectionRestriction f y U hy := by
  rw [← Category.assoc, TopCat.Presheaf.stalkFunctor_map_germ, Category.assoc,
    germ_stalkToFibreSections]

private theorem appLE_top {A B : Scheme.{u}} (g : A ⟶ B) (h : ⊤ ≤ g ⁻¹ᵁ ⊤) :
    g.appLE ⊤ ⊤ h = g.appTop := by
  simpa only [Scheme.Hom.preimage_top] using (g.appLE_eq_app (U := ⊤))

private theorem appLE_congr_hom {A B : Scheme.{u}} (g h : A ⟶ B) (heq : g = h)
    (U : B.Opens) (V : A.Opens) (eg : V ≤ g ⁻¹ᵁ U) (eh : V ≤ h ⁻¹ᵁ U) :
    g.appLE U V eg = h.appLE U V eh := by
  subst h
  rfl

/-- Every neighborhood of a point pulls back to the whole spectrum of its actual stalk. -/
theorem stalkRestriction_le (U : Y.Opens) (hy : y ∈ U) :
    ⊤ ≤ (Y.fromSpecStalk y) ⁻¹ᵁ U :=
  (Scheme.preimage_eq_top_of_closedPoint_mem (Y.fromSpecStalk y)
    (by simpa only [Scheme.fromSpecStalk_closedPoint] using hy)).ge

/-- The original stalk-point section map is the actual germ followed by the Spec comparison. -/
theorem stalkPoint_appLE (U : Y.Opens) (hy : y ∈ U) :
    (Y.fromSpecStalk y).appLE U ⊤ (stalkRestriction_le y U hy) =
      Y.presheaf.germ U y hy ≫ (Scheme.ΓSpecIso (Y.presheaf.stalk y)).inv := by
  rw [Scheme.Hom.appLE, Scheme.fromSpecStalk_app hy, Category.assoc, Category.assoc,
    ← Functor.map_comp]
  have hmap : ((homOfLE le_top).op ≫ (homOfLE (stalkRestriction_le y U hy)).op :
      (op ⊤ : (Spec (Y.presheaf.stalk y)).Opensᵒᵖ) ⟶ op ⊤) = 𝟙 _ :=
    Subsingleton.elim _ _
  rw [hmap, CategoryTheory.Functor.map_id, Category.comp_id]

/-- Every neighborhood pulls back to the whole spectrum of the actual residue field. -/
theorem residueRestriction_le (U : Y.Opens) (hy : y ∈ U) :
    ⊤ ≤ (Y.fromSpecResidueField y) ⁻¹ᵁ U := by
  intro z _
  change Y.fromSpecResidueField y z ∈ U
  rw [Scheme.fromSpecResidueField_apply]
  exact hy

/-- Actual residue-point restriction is the germ, residue map and original Spec comparison. -/
theorem residuePoint_appLE (U : Y.Opens) (hy : y ∈ U) :
    (Y.fromSpecResidueField y).appLE U ⊤ (residueRestriction_le y U hy) =
      Y.presheaf.germ U y hy ≫ Y.residue y ≫
        (Scheme.ΓSpecIso (Y.residueField y)).inv := by
  have hcomp : (Y.fromSpecResidueField y).appLE U ⊤ (residueRestriction_le y U hy) =
      (Y.fromSpecStalk y).appLE U ⊤ (stalkRestriction_le y U hy) ≫
        (Spec.map (Y.residue y)).appTop := by
    change (Spec.map (Y.residue y) ≫ Y.fromSpecStalk y).appLE U ⊤ _ = _
    exact (Scheme.Hom.appLE_comp_appLE (Spec.map (Y.residue y)) (Y.fromSpecStalk y)
      U ⊤ ⊤ (stalkRestriction_le y U hy) (by simp)).symm.trans
        (congrArg (fun k => (Y.fromSpecStalk y).appLE U ⊤
          (stalkRestriction_le y U hy) ≫ k)
            (appLE_top (Spec.map (Y.residue y)) (by simp)))
  rw [hcomp, stalkPoint_appLE, Category.assoc, ← Scheme.ΓSpecIso_inv_naturality]

/-- The literal residue-field constants on the actual fibre. -/
def fibreConstants : Y.residueField y ⟶ Γ(f.fiber y, ⊤) :=
  (Scheme.ΓSpecIso (Y.residueField y)).inv ≫ (f.fiberToSpecResidueField y).appTop

/-- The original structure-sheaf stalk map followed by beta factors through the residue field. -/
@[reassoc]
theorem structureMap_stalkToFibreSections :
    (TopCat.Presheaf.stalkFunctor CommRingCat.{u} y).map f.c ≫ stalkToFibreSections f y =
      Y.residue y ≫ fibreConstants f y := by
  apply Y.presheaf.stalk_hom_ext
  intro U hy
  let fibreMap := f.fiberToSpecResidueField y
  let residuePoint := Y.fromSpecResidueField y
  have hpre : ⊤ ≤ (fibreMap ≫ residuePoint) ⁻¹ᵁ U := by
    intro z _
    change (fibreMap ≫ residuePoint) z ∈ U
    rw [Scheme.Hom.comp_apply, Scheme.fromSpecResidueField_apply]
    exact hy
  calc
    _ = (fibreMap ≫ residuePoint).appLE U ⊤ hpre := by
      rw [structureMap_germ_stalkToFibreSections, fibreSectionRestriction]
      calc
        _ = (f.fiberι y ≫ f).appLE U ⊤ (fibreRestriction_le f y U hy) :=
          (Scheme.Hom.comp_appLE (f.fiberι y) f U ⊤
            (fibreRestriction_le f y U hy)).symm
        _ = _ := appLE_congr_hom _ _ (f.fiber_fac y) U ⊤ _ hpre
    _ = residuePoint.appLE U ⊤ (residueRestriction_le y U hy) ≫ fibreMap.appTop := by
      exact (Scheme.Hom.appLE_comp_appLE fibreMap residuePoint U ⊤ ⊤
        (residueRestriction_le y U hy) (by simp)).symm.trans
          (congrArg (fun k => residuePoint.appLE U ⊤
            (residueRestriction_le y U hy) ≫ k) (appLE_top fibreMap (by simp)))
    _ = _ := by
      rw [residuePoint_appLE y U hy]
      simp only [fibreConstants, fibreMap, Category.assoc]

/-- An ordinary pushforward-stalk image is a residue-field constant when the actual
structure-sheaf map is an isomorphism. No surjectivity onto fibre sections is asserted. -/
theorem exists_residue_constant_of_stalk [IsIso f.c]
    (a : (f.base _* X.presheaf).stalk y) :
    ∃ c : Y.residueField y, stalkToFibreSections f y a = fibreConstants f y c := by
  let cy := (TopCat.Presheaf.stalkFunctor CommRingCat.{u} y).map f.c
  let : IsIso cy := inferInstance
  obtain ⟨b, hb⟩ := (ConcreteCategory.bijective_of_isIso cy).2 a
  refine ⟨Y.residue y b, ?_⟩
  rw [← hb]
  exact ConcreteCategory.congr_hom (structureMap_stalkToFibreSections f y) b

end AlgebraicGeometry.Scheme.Cohomology.ProperFibreIdempotents
