/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.Stalk.BaseChangeGlobalSections
public import Aglib.AlgebraicGeometry.EtaleCohomology.Stalk.GlobalSectionsPullbackGerm

/-! # Original higher exchange on germs of global cohomology classes

The original stalk-unit comparison followed by the original higher exchange
preserves the original germ of every global Ext class. This is the genuine
all-degree map equality for these germs, not an assertion that every pointed
neighborhood class extends globally. The source and target Ext universes remain independent.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits

universe u w w' dX dS dX' dS'

namespace AlgebraicGeometry.Scheme.EtaleCohomology

attribute [local instance] hasSheafifyLarge

variable {X S X' S' : Scheme.{u}}
  [HasExt.{w} (AbelianSheaf.{u, u + 1} X)]
  [HasExt.{w'} (AbelianSheaf.{u, u + 1} X')]
  [HasDerivedCategory.{dX} (AbelianSheaf.{u, u + 1} X)]
  [HasDerivedCategory.{dS} (AbelianSheaf.{u, u + 1} S)]
  [HasDerivedCategory.{dX'} (AbelianSheaf.{u, u + 1} X')]
  [HasDerivedCategory.{dS'} (AbelianSheaf.{u, u + 1} S')]
  (f : X ⟶ S) (f' : X' ⟶ S') (g : S' ⟶ S) (g' : X' ⟶ X)
  (h : f' ≫ g = g' ≫ f)

omit [HasDerivedCategory.{dX} (AbelianSheaf.{u, u + 1} X)]
  [HasDerivedCategory.{dS} (AbelianSheaf.{u, u + 1} S)]
  [HasDerivedCategory.{dX'} (AbelianSheaf.{u, u + 1} X')]
  [HasDerivedCategory.{dS'} (AbelianSheaf.{u, u + 1} S')] in
/-- The original higher exchange preserves the actual original germ of a global
class, with the original cohomology pullback on the total spaces. -/
theorem higherBaseChangeMap_globalCohomologyGerm
    (F : AbelianSheaf.{u, u + 1} X) (q : ℕ)
    {Ω : Type u} [Field Ω] [IsSepClosed Ω] (η : Spec (.of Ω) ⟶ S')
    (p : (pointSmallEtale (η ≫ g)).fiber.obj (etaleTerminal S))
    (p' : (pointSmallEtale η).fiber.obj (etaleTerminal S')) (x : Sheaf.H.{w} F q) :
    (pointSmallEtale η).sheafFiber.map ((higherBaseChangeMap f f' g g' h q).app F)
        ((StalkInverseImage.stalkUnitNatIso g η).hom.app ((higherDirectImage f q).obj F)
          (originalCohomologyGerm f F q (η ≫ g) (etaleTerminal S) p
            (globalCohomologyTerminalClass f F q x))) =
      originalCohomologyGerm f' ((inverseImage g').obj F) q η (etaleTerminal S') p'
        (globalCohomologyTerminalClass f' ((inverseImage g').obj F) q
          (cohomologyPullback.{u, w, w'} g' F q x)) := by
  let L := (higherDirectImage f q).obj F
  let R := (higherDirectImage f' q).obj ((inverseImage g').obj F)
  let b := (higherBaseChangeMap f f' g g' h q).app F
  have hu := ConcreteCategory.congr_hom
    (globalSectionsPullback_germ g η L p p') (cohomologyToHigherSections f F q x)
  have hn := ConcreteCategory.congr_hom
    ((pointSmallEtale η).toPresheafFiber_naturality b.hom (etaleTerminal S') p')
      (globalSectionsPullback g L (cohomologyToHigherSections f F q x))
  have hb := higherBaseChangeMap_cohomologyToHigherSections f f' g g' h F q x
  change (pointSmallEtale η).presheafFiber.map b.hom
    ((StalkInverseImage.stalkUnitNatIso g η).hom.app L
      ((pointSmallEtale (η ≫ g)).toPresheafFiber (etaleTerminal S) p L.obj
        (cohomologyToHigherSections f F q x))) =
    (pointSmallEtale η).toPresheafFiber (etaleTerminal S') p' R.obj
      (cohomologyToHigherSections f' ((inverseImage g').obj F) q
        (cohomologyPullback.{u, w, w'} g' F q x))
  change (StalkInverseImage.stalkUnitNatIso g η).hom.app L
      ((pointSmallEtale (η ≫ g)).toPresheafFiber (etaleTerminal S) p L.obj
        (cohomologyToHigherSections f F q x)) =
    (pointSmallEtale η).toPresheafFiber (etaleTerminal S') p' ((inverseImage g).obj L).obj
      (globalSectionsPullback g L (cohomologyToHigherSections f F q x)) at hu
  change (pointSmallEtale η).presheafFiber.map b.hom
      ((pointSmallEtale η).toPresheafFiber (etaleTerminal S') p' ((inverseImage g).obj L).obj
        (globalSectionsPullback g L (cohomologyToHigherSections f F q x))) =
    (pointSmallEtale η).toPresheafFiber (etaleTerminal S') p' R.obj
      ((globalSections S').map b
        (globalSectionsPullback g L (cohomologyToHigherSections f F q x))) at hn
  exact (congrArg ((pointSmallEtale η).presheafFiber.map b.hom) hu).trans
    (hn.trans (congrArg
      ((pointSmallEtale η).toPresheafFiber (etaleTerminal S') p' R.obj) hb))

end AlgebraicGeometry.Scheme.EtaleCohomology
