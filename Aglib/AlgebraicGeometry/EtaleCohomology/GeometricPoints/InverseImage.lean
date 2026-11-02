/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.GeometricPoints.InverseImage.Skyscraper
public import Aglib.AlgebraicGeometry.EtaleCohomology.GeometricPoints.InverseImage.Projection

/-! # Inverse image and original geometric stalks

For every abelian sheaf in the standard value universe, the original
adjunction-unit map on geometric stalks is an isomorphism. The proof takes
the native adjunction mate of the actual Hom-point reindexing of skyscrapers
and identifies its map on the original germs.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.Scheme.EtaleCohomology.StalkInverseImage

universe u

variable {X S : Scheme.{u}} {Ω : Type u} [Field Ω] [IsSepClosed Ω]
  (f : S ⟶ X) (η : Spec (.of Ω) ⟶ S)

open CoefficientStalkBaseChange
attribute [local instance] hasSheafifyLarge

/-- The native mate of the actual skyscraper reindexing isomorphism. -/
def nativeStalkIso :
    (pointSmallEtale (η ≫ f)).sheafFiber (A := AddCommGrpCat.{u + 1}) ≅
      inverseImage f ⋙ (pointSmallEtale η).sheafFiber :=
  GrothendieckTopology.Point.InverseImageComparison.fiberIso
    (pointSmallEtale (η ≫ f)) (pointSmallEtale η) (siteBaseChange f)
    (pointEquiv f η) (fun a p => pointEquiv_naturality f η a p)
    (inverseImage f) (inverseImageAdjunction f)

/-- A coordinate of the native skyscraper adjunction unit is the original germ. -/
@[reassoc (attr := simp)]
theorem skyscraperUnit_π (L : AbelianSheaf.{u, u + 1} S) (U : S.Etale)
    (p : (pointSmallEtale η).fiber.obj U) :
    (((pointSmallEtale η).skyscraperSheafAdjunction.unit.app L).hom.app (op U)) ≫
        Pi.π (fun _ : (pointSmallEtale η).fiber.obj U =>
          (pointSmallEtale η).sheafFiber.obj L) p =
      (pointSmallEtale η).toPresheafFiber U p L.obj :=
  pointSkyscraperUnit_π (pointSmallEtale η) L U p

/-- The mate has the literal original inverse-image-unit formula on every germ. -/
@[reassoc]
theorem germ_nativeStalkIso (L : AbelianSheaf.{u, u + 1} X) (U : X.Etale)
    (p : (pointSmallEtale (η ≫ f)).fiber.obj U) :
    (pointSmallEtale (η ≫ f)).toPresheafFiber U p L.obj ≫
        (nativeStalkIso f η).hom.app L =
      ((inverseImageAdjunction f).unit.app L).hom.app (op U) ≫
        (pointSmallEtale η).toPresheafFiber ((siteBaseChange f).obj U)
          (pulledBackPoint f η U p) ((inverseImage f).obj L).obj :=
  GrothendieckTopology.Point.InverseImageComparison.germ_fiberIso
    (pointSmallEtale (η ≫ f)) (pointSmallEtale η) (siteBaseChange f)
    (pointEquiv f η) (fun a p => pointEquiv_naturality f η a p)
    (inverseImage f) (inverseImageAdjunction f) L U p

/-- The native point-colimit comparison has exactly the existing canonical stalk-unit map. -/
theorem nativeStalkIso_hom (L : AbelianSheaf.{u, u + 1} X) :
    (nativeStalkIso f η).hom.app L = stalkUnit f η L := by
  apply (pointSmallEtale (η ≫ f)).presheafFiber_hom_ext
  intro U p
  exact (germ_nativeStalkIso f η L U p).trans (germ_stalkUnit f η L U p).symm

/-- The original canonical stalk-unit map is invertible for every abelian coefficient sheaf. -/
instance stalkUnit_isIso (L : AbelianSheaf.{u, u + 1} X) :
    IsIso (stalkUnit f η L) := by
  rw [← nativeStalkIso_hom f η L]
  infer_instance

/-- The all-coefficient comparison reuses this same proved mate and its original-unit hom. -/
def stalkUnitNatIso :
    (pointSmallEtale (η ≫ f)).sheafFiber (A := AddCommGrpCat.{u + 1}) ≅
      inverseImage f ⋙ (pointSmallEtale η).sheafFiber :=
  nativeStalkIso f η

/-- The component is the original canonical map by its proved germ-unit identification. -/
@[simp]
theorem stalkUnitNatIso_hom (L : AbelianSheaf.{u, u + 1} X) :
    (stalkUnitNatIso f η).hom.app L = stalkUnit f η L :=
  nativeStalkIso_hom f η L

/-- The all-coefficient isomorphism retains the original section, pulled-back point and unit. -/
@[reassoc]
theorem germ_stalkUnitNatIso (L : AbelianSheaf.{u, u + 1} X) (U : X.Etale)
    (p : (pointSmallEtale (η ≫ f)).fiber.obj U) :
    (pointSmallEtale (η ≫ f)).toPresheafFiber U p L.obj ≫
        (stalkUnitNatIso f η).hom.app L =
      ((inverseImageAdjunction f).unit.app L).hom.app (op U) ≫
        (pointSmallEtale η).toPresheafFiber ((siteBaseChange f).obj U)
          (pulledBackPoint f η U p) ((inverseImage f).obj L).obj :=
  germ_nativeStalkIso f η L U p

end AlgebraicGeometry.Scheme.EtaleCohomology.StalkInverseImage
