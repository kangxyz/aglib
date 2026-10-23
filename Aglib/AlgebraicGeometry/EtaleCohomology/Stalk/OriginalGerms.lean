/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.Stalk.OriginalPresheaf
public import Mathlib.AlgebraicGeometry.Sites.EtalePoint
public import Mathlib.CategoryTheory.Sites.Point.Skyscraper

/-! # Original cohomology germs and native higher-direct-image stalks -/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits Opposite

universe u w

namespace AlgebraicGeometry.Scheme.EtaleCohomology

attribute [local instance] hasSheafifyLarge

variable {X S : Scheme.{u}} (f : X ⟶ S)
  [HasExt.{w} (AbelianSheaf.{u, u + 1} X)]
  (F : AbelianSheaf.{u, u + 1} X) (q : ℕ)
  {Ω : Type u} [Field Ω] [IsSepClosed Ω] (η : Spec (.of Ω) ⟶ S)

local instance (U : S.Etale) :
    Small.{u + 1} (Sheaf.LargeCohomology.H.{w, u + 1, u, u + 1}
      (Scheme.smallEtaleTopology X) F q ((siteBaseChange f).obj U)) :=
  originalCohomologyPresheaf_small f F q (op U)

/-- The actual original presheaf map becomes invertible on every geometric stalk. -/
instance originalCohomologyToHigherDirectImage_stalk_isIso :
    IsIso (((pointSmallEtale η).presheafFiber (A := AddCommGrpCat.{u + 1})).map
      (originalCohomologyToHigherDirectImage f F q)) := by
  rw [← originalCohomologyToHigherDirectImage_unit, Functor.map_comp]
  infer_instance

/-- The native higher-image stalk is the point-colimit of original cohomology,
with its map fixed by the original sheafification unit. -/
def originalCohomologyStalkIso :
    ((pointSmallEtale η).presheafFiber (A := AddCommGrpCat.{u + 1})).obj
        (smallOriginalCohomologyPresheaf f F q) ≅
      ((pointSmallEtale η).sheafFiber (A := AddCommGrpCat.{u + 1})).obj
        ((higherDirectImage f q).obj F) := by
  let : IsIso (((pointSmallEtale η).presheafFiber (A := AddCommGrpCat.{u + 1})).map
      (originalCohomologyToHigherDirectImage f F q)) :=
    originalCohomologyToHigherDirectImage_stalk_isIso f F q η
  exact asIso (((pointSmallEtale η).presheafFiber (A := AddCommGrpCat.{u + 1})).map
    (originalCohomologyToHigherDirectImage f F q))

/-- Each actual neighborhood cocone map is the original cohomology-to-higher-image
map followed by the original geometric germ. -/
@[reassoc]
theorem germ_originalCohomologyStalkIso (U : S.Etale)
    (p : (pointSmallEtale η).fiber.obj U) :
    (pointSmallEtale η).toPresheafFiber U p (smallOriginalCohomologyPresheaf f F q) ≫
        (originalCohomologyStalkIso f F q η).hom =
      (originalCohomologyToHigherDirectImage f F q).app (op U) ≫
        (pointSmallEtale η).toPresheafFiber U p ((higherDirectImage f q).obj F).obj :=
  (pointSmallEtale η).toPresheafFiber_naturality
    (originalCohomologyToHigherDirectImage f F q) U p

/-- Original, unresized Ext classes have the literal represented-section germ. -/
def originalCohomologyGerm (U : S.Etale)
    (p : (pointSmallEtale η).fiber.obj U) :
    Sheaf.LargeCohomology.H.{w, u + 1, u, u + 1}
        (Scheme.smallEtaleTopology X) F q ((siteBaseChange f).obj U) →+
      ((pointSmallEtale η).sheafFiber (A := AddCommGrpCat.{u + 1})).obj
        ((higherDirectImage f q).obj F) :=
  ((pointSmallEtale η).toPresheafFiber U p ((higherDirectImage f q).obj F).obj).hom.comp
    ((((resolutionCohomologyToHigherDirectImage f q).app F).app (op U)).hom.comp
      (originalCohomologyResolutionEquiv f U F q).toAddMonoidHom)

/-- The neighborhood-colimit comparison retains each original Ext class. -/
theorem germ_originalCohomologyStalkIso_apply (U : S.Etale)
    (p : (pointSmallEtale η).fiber.obj U)
    (x : Sheaf.LargeCohomology.H.{w, u + 1, u, u + 1}
      (Scheme.smallEtaleTopology X) F q ((siteBaseChange f).obj U)) :
    (originalCohomologyStalkIso f F q η).hom
      ((pointSmallEtale η).toPresheafFiber U p (smallOriginalCohomologyPresheaf f F q)
        (Shrink.addEquiv.symm x)) = originalCohomologyGerm f F q η U p x := by
  have h := ConcreteCategory.congr_hom
    (germ_originalCohomologyStalkIso f F q η U p) (Shrink.addEquiv.symm x)
  change _ = (pointSmallEtale η).toPresheafFiber U p ((higherDirectImage f q).obj F).obj
    ((((resolutionCohomologyToHigherDirectImage f q).app F).app (op U))
      (originalCohomologyResolutionEquiv f U F q
        (Shrink.addEquiv (Shrink.addEquiv.symm x)))) at h
  change (originalCohomologyStalkIso f F q η).hom
      ((pointSmallEtale η).toPresheafFiber U p (smallOriginalCohomologyPresheaf f F q)
        (Shrink.addEquiv.symm x)) =
    (pointSmallEtale η).toPresheafFiber U p ((higherDirectImage f q).obj F).obj
      ((((resolutionCohomologyToHigherDirectImage f q).app F).app (op U))
        (originalCohomologyResolutionEquiv f U F q x))
  simpa only [ConcreteCategory.comp_apply, AddEquiv.apply_symm_apply] using h

end AlgebraicGeometry.Scheme.EtaleCohomology
