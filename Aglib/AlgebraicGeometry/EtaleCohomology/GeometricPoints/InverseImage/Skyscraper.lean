/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.GeometricPoints.InverseImage.Unit
public import Aglib.CategoryTheory.Sites.Point.InverseImageComparison

/-! # Geometric-point pullback and skyscraper sheaves

The actual pullback universal property reindexes the products defining the
native skyscraper sheaves. No condition on the coefficient sheaf is used.
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

/-- The pullback universal property on the original geometric Hom witnesses. -/
def pointEquiv (U : X.Etale) :
    (pointSmallEtale (η ≫ f)).fiber.obj U ≃
      (pointSmallEtale η).fiber.obj ((siteBaseChange f).obj U) :=
  (Over.mapPullbackAdj f).homEquiv (Over.mk η)
    ((Scheme.Etale.forget X).obj U)

/-- Its forward map is the original geometric pulled-back point. -/
@[simp]
theorem pointEquiv_apply (U : X.Etale)
    (p : (pointSmallEtale (η ≫ f)).fiber.obj U) :
    pointEquiv f η U p = pulledBackPoint f η U p := rfl

/-- Naturality of the actual point bijection as a map of the native point fibres. -/
theorem pointEquiv_naturality {U V : X.Etale} (g : U ⟶ V)
    (p : (pointSmallEtale (η ≫ f)).fiber.obj U) :
    pointEquiv f η V ((pointSmallEtale (η ≫ f)).fiber.map g p) =
      (pointSmallEtale η).fiber.map ((siteBaseChange f).map g) (pointEquiv f η U p) :=
  pulledBackPoint_naturality f η g p

/-- The native product isomorphism retains literal constant product families on both sides. -/
def pointProductIso (U : X.Etale) (M : AddCommGrpCat.{u + 1}) :
    (∏ᶜ fun _ : (pointSmallEtale η).fiber.obj ((siteBaseChange f).obj U) => M) ≅
      (∏ᶜ fun _ : (pointSmallEtale (η ≫ f)).fiber.obj U => M) :=
  GrothendieckTopology.Point.InverseImageComparison.constantProductIso (pointEquiv f η U) M

/-- The product comparison reads precisely the coordinate of the original point bijection. -/
@[reassoc (attr := simp)]
theorem pointProductIso_hom_π (U : X.Etale) (M : AddCommGrpCat.{u + 1})
    (p : (pointSmallEtale (η ≫ f)).fiber.obj U) :
    (pointProductIso f η U M).hom ≫ Pi.π _ p =
      Pi.π (fun _ : (pointSmallEtale η).fiber.obj ((siteBaseChange f).obj U) => M)
        (pointEquiv f η U p) :=
  GrothendieckTopology.Point.InverseImageComparison.constantProductIso_hom_π (pointEquiv f η U) M p

/-- Pullback reindexes the native skyscraper presheaf by the actual Hom-point bijection. -/
def skyscraperPresheafIso (M : AddCommGrpCat.{u + 1}) :
    (siteBaseChange f).op ⋙ (pointSmallEtale η).skyscraperPresheaf M ≅
      (pointSmallEtale (η ≫ f)).skyscraperPresheaf M :=
  GrothendieckTopology.Point.InverseImageComparison.presheafIso
    (pointSmallEtale (η ≫ f)) (pointSmallEtale η) (siteBaseChange f)
    (pointEquiv f η) (fun a p => pointEquiv_naturality f η a p) M

/-- Reindexing reads the coordinate indexed by the original pulled-back point. -/
@[reassoc]
theorem skyscraperPresheafIso_hom_π (M : AddCommGrpCat.{u + 1}) (U : X.Etale)
    (p : (pointSmallEtale (η ≫ f)).fiber.obj U) :
    (skyscraperPresheafIso f η M).hom.app (op U) ≫ Pi.π _ p =
      Pi.π (fun _ : (pointSmallEtale η).fiber.obj ((siteBaseChange f).obj U) => M)
        (pulledBackPoint f η U p) :=
  pointProductIso_hom_π f η U M p

/-- The genuine skyscraper sheaves commute with original small-étale direct image. -/
def skyscraperSheafIso :
    (pointSmallEtale η).skyscraperSheafFunctor (A := AddCommGrpCat.{u + 1}) ⋙
        directImage f ≅
      (pointSmallEtale (η ≫ f)).skyscraperSheafFunctor :=
  GrothendieckTopology.Point.InverseImageComparison.sheafIso
    (pointSmallEtale (η ≫ f)) (pointSmallEtale η) (siteBaseChange f)
    (pointEquiv f η) (fun a p => pointEquiv_naturality f η a p)

/-- The right-adjoint comparison retains the original pulled-back coordinate. -/
@[reassoc]
theorem skyscraperSheafIso_hom_π (M : AddCommGrpCat.{u + 1}) (U : X.Etale)
    (p : (pointSmallEtale (η ≫ f)).fiber.obj U) :
    ((skyscraperSheafIso f η).hom.app M).hom.app (op U) ≫ Pi.π _ p =
      Pi.π (fun _ : (pointSmallEtale η).fiber.obj ((siteBaseChange f).obj U) => M)
        (pulledBackPoint f η U p) :=
  skyscraperPresheafIso_hom_π f η M U p

end AlgebraicGeometry.Scheme.EtaleCohomology.StalkInverseImage
