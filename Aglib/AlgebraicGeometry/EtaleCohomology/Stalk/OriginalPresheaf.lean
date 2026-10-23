/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.Stalk.OriginalRestriction
public import Mathlib.Algebra.Group.Shrink

/-!
# Sheafification of original represented cohomology

Only the original cohomology groups are resized, using their proved smallness;
the coefficient sheaf and native higher direct image retain their original
universe. Every restriction is transported from the original Ext presheaf.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u w

namespace AlgebraicGeometry.Scheme.EtaleCohomology

attribute [local instance] hasSheafifyLarge

variable {X S : Scheme.{u}} (f : X ⟶ S)
  [HasExt.{w} (AbelianSheaf.{u, u + 1} X)]
  (F : AbelianSheaf.{u, u + 1} X) (q : ℕ)

/-- Original represented cohomology on the base-changed étale objects. -/
abbrev originalCohomologyPresheaf : S.Etaleᵒᵖ ⥤ AddCommGrpCat.{w} :=
  (siteBaseChange f).op ⋙
    Sheaf.LargeCohomology.presheaf.{w, u + 1, u, u + 1}
      (Scheme.smallEtaleTopology X) F q

/-- The original cohomology groups fit the native coefficient universe,
proved through the actual resolution calculation. -/
instance originalCohomologyPresheaf_small (U : S.Etaleᵒᵖ) :
    Small.{u + 1} ((originalCohomologyPresheaf f F q).obj U) :=
  small_of_injective (originalCohomologyResolutionEquiv f U.unop F q).injective

/-- Resize the original groups, not the coefficient sheaf, and transport
literal original restrictions. -/
def smallOriginalCohomologyPresheaf : S.Etaleᵒᵖ ⥤ AddCommGrpCat.{u + 1} where
  obj U := AddCommGrpCat.of (Shrink.{u + 1} ((originalCohomologyPresheaf f F q).obj U))
  map g := AddCommGrpCat.ofHom
    (Shrink.addEquiv.symm.toAddMonoidHom.comp
      (((originalCohomologyPresheaf f F q).map g).hom.comp Shrink.addEquiv.toAddMonoidHom))
  map_id U := by
    ext a
    simp
  map_comp g h := by
    ext a
    simp

/-- Original restrictions and the canonical value comparison give the
actual natural isomorphism with the resolution presheaf. -/
def smallOriginalCohomologyResolutionIso :
    smallOriginalCohomologyPresheaf f F q ≅ (resolutionCohomologyPresheaf f q).obj F :=
  NatIso.ofComponents
    (fun U => ((Shrink.addEquiv :
      Shrink.{u + 1} ((originalCohomologyPresheaf f F q).obj U) ≃+
        (originalCohomologyPresheaf f F q).obj U).trans
      (originalCohomologyResolutionEquiv f U.unop F q)).toAddCommGrpIso)
    (by
      intro U V g
      let : Small.{u + 1} (Sheaf.LargeCohomology.H.{w, u + 1, u, u + 1}
          (Scheme.smallEtaleTopology X) F q ((siteBaseChange f).obj U.unop)) :=
        originalCohomologyPresheaf_small f F q U
      let : Small.{u + 1} (Sheaf.LargeCohomology.H.{w, u + 1, u, u + 1}
          (Scheme.smallEtaleTopology X) F q ((siteBaseChange f).obj V.unop)) :=
        originalCohomologyPresheaf_small f F q V
      ext a
      change originalCohomologyResolutionEquiv f V.unop F q
          (Shrink.addEquiv (Shrink.addEquiv.symm
            ((originalCohomologyPresheaf f F q).map g (Shrink.addEquiv a)))) =
        ((resolutionCohomologyPresheaf f q).obj F).map g
          (originalCohomologyResolutionEquiv f U.unop F q (Shrink.addEquiv a))
      rw [AddEquiv.apply_symm_apply]
      exact originalCohomologyResolutionEquiv_restriction f g.unop F q _)

/-- Sheafification of the size-correct original cohomology presheaf is the
original native higher direct image. -/
def originalCohomologySheafificationIso :
    (presheafToSheaf (Scheme.smallEtaleTopology S) AddCommGrpCat.{u + 1}).obj
        (smallOriginalCohomologyPresheaf f F q) ≅ (higherDirectImage f q).obj F :=
  (presheafToSheaf (Scheme.smallEtaleTopology S) AddCommGrpCat.{u + 1}).mapIso
      (smallOriginalCohomologyResolutionIso f F q) ≪≫
    (resolutionCohomologySheafificationIso f q).app F

/-- The original presheaf map is the actual value comparison followed by
the native resolution-to-higher-image map. -/
def originalCohomologyToHigherDirectImage :
    smallOriginalCohomologyPresheaf f F q ⟶
      ((higherDirectImage f q).obj F).obj :=
  (smallOriginalCohomologyResolutionIso f F q).hom ≫
    (resolutionCohomologyToHigherDirectImage f q).app F

/-- The comparison is induced by precisely the original sheafification unit. -/
theorem originalCohomologyToHigherDirectImage_unit :
    toSheafify (Scheme.smallEtaleTopology S) (smallOriginalCohomologyPresheaf f F q) ≫
      (originalCohomologySheafificationIso f F q).hom.hom =
        originalCohomologyToHigherDirectImage f F q := by
  have h := (sheafificationAdjunction (Scheme.smallEtaleTopology S)
    AddCommGrpCat.{u + 1}).unit.naturality
      (smallOriginalCohomologyResolutionIso f F q).hom
  change (smallOriginalCohomologyResolutionIso f F q).hom ≫
      toSheafify (Scheme.smallEtaleTopology S) ((resolutionCohomologyPresheaf f q).obj F) =
    toSheafify (Scheme.smallEtaleTopology S) (smallOriginalCohomologyPresheaf f F q) ≫
      ((presheafToSheaf (Scheme.smallEtaleTopology S) AddCommGrpCat.{u + 1}).map
        (smallOriginalCohomologyResolutionIso f F q).hom).hom at h
  change _ ≫
      ((presheafToSheaf (Scheme.smallEtaleTopology S) AddCommGrpCat.{u + 1}).map
        (smallOriginalCohomologyResolutionIso f F q).hom).hom ≫
      ((resolutionCohomologySheafificationIso f q).hom.app F).hom =
    (smallOriginalCohomologyResolutionIso f F q).hom ≫
      toSheafify (Scheme.smallEtaleTopology S) ((resolutionCohomologyPresheaf f q).obj F) ≫
      ((resolutionCohomologySheafificationIso f q).hom.app F).hom
  rw [← Category.assoc, ← h, Category.assoc]

end AlgebraicGeometry.Scheme.EtaleCohomology
