/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.GeometricPoints.InverseImage
public import Aglib.AlgebraicGeometry.EtaleCohomology.Pullback

/-! # The original section pullback and the original geometric germ

The original inverse-image stalk unit takes the germ of a global section to
the germ of its original section pullback. Native terminal transport and the
actual pulled-back point are retained; no cohomological hypothesis is used.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry.Scheme.EtaleCohomology

attribute [local instance] hasSheafifyLarge

/-- The original stalk-unit isomorphism preserves the original global-section
pullback, with any actual points of the fixed terminal etale objects. -/
theorem globalSectionsPullback_germ {X S : Scheme.{u}} (f : S ⟶ X)
    {Ω : Type u} [Field Ω] [IsSepClosed Ω] (η : Spec (.of Ω) ⟶ S)
    (L : AbelianSheaf.{u, u + 1} X)
    (p : (pointSmallEtale (η ≫ f)).fiber.obj (etaleTerminal X))
    (p' : (pointSmallEtale η).fiber.obj (etaleTerminal S)) :
    (pointSmallEtale (η ≫ f)).toPresheafFiber (etaleTerminal X) p L.obj ≫
        (StalkInverseImage.stalkUnitNatIso f η).hom.app L =
      globalSectionsPullback f L ≫
        (pointSmallEtale η).toPresheafFiber (etaleTerminal S) p'
          ((inverseImage f).obj L).obj := by
  let M := (inverseImage f).obj L
  let V := (siteBaseChange f).obj (etaleTerminal X)
  let e := siteBaseChangeTerminalIso f
  let t := CoefficientStalkBaseChange.pulledBackPoint f η (etaleTerminal X) p
  let E := M.obj.mapIso e.symm.op
  have ht : (pointSmallEtale η).fiber.map e.hom t = p' :=
    Over.mkIdTerminal.hom_ext _ _
  have hw : E.inv ≫ (pointSmallEtale η).toPresheafFiber V t M.obj =
      (pointSmallEtale η).toPresheafFiber (etaleTerminal S) p' M.obj := by
    change M.obj.map e.hom.op ≫ _ = _
    simpa only [ht] using (pointSmallEtale η).toPresheafFiber_w e.hom t M.obj
  have hg : (pointSmallEtale η).toPresheafFiber V t M.obj =
      E.hom ≫ (pointSmallEtale η).toPresheafFiber (etaleTerminal S) p' M.obj := by
    rw [← hw, Iso.hom_inv_id_assoc]
  rw [StalkInverseImage.germ_stalkUnitNatIso]
  change ((inverseImageAdjunction f).unit.app L).hom.app (op (etaleTerminal X)) ≫
      (pointSmallEtale η).toPresheafFiber V t M.obj =
    (((inverseImageAdjunction f).unit.app L).hom.app (op (etaleTerminal X)) ≫ E.hom) ≫
      (pointSmallEtale η).toPresheafFiber (etaleTerminal S) p' M.obj
  rw [hg, Category.assoc]

end AlgebraicGeometry.Scheme.EtaleCohomology
