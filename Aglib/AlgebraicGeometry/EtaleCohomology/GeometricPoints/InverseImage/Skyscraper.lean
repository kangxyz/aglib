/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.H1.CoefficientStalkBaseChange
public import Mathlib.CategoryTheory.Sites.Point.Skyscraper
public import Mathlib.CategoryTheory.Adjunction.Mates

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
  SchemeTorsorBaseChange.pullbackSectionEquiv f (Over.mk η)
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
      (∏ᶜ fun _ : (pointSmallEtale (η ≫ f)).fiber.obj U => M) where
  hom := Pi.lift (fun p => Pi.π _ (pointEquiv f η U p))
  inv := Pi.lift (fun q => Pi.π _ ((pointEquiv f η U).symm q))
  hom_inv_id := by
    apply Pi.hom_ext
    intro p
    simp only [Category.assoc, Pi.lift_comp_π,
      Equiv.apply_symm_apply, Category.id_comp]
  inv_hom_id := by
    apply Pi.hom_ext
    intro p
    simp only [Category.assoc, Pi.lift_comp_π,
      Equiv.symm_apply_apply, Category.id_comp]

/-- The product comparison reads precisely the coordinate of the original point bijection. -/
@[reassoc (attr := simp)]
theorem pointProductIso_hom_π (U : X.Etale) (M : AddCommGrpCat.{u + 1})
    (p : (pointSmallEtale (η ≫ f)).fiber.obj U) :
    (pointProductIso f η U M).hom ≫ Pi.π _ p =
      Pi.π (fun _ : (pointSmallEtale η).fiber.obj ((siteBaseChange f).obj U) => M)
        (pointEquiv f η U p) :=
  Pi.lift_comp_π _ p

/-- Pullback reindexes the native skyscraper presheaf by the actual Hom-point bijection. -/
def skyscraperPresheafIso (M : AddCommGrpCat.{u + 1}) :
    (siteBaseChange f).op ⋙ (pointSmallEtale η).skyscraperPresheaf M ≅
      (pointSmallEtale (η ≫ f)).skyscraperPresheaf M :=
  NatIso.ofComponents
    (fun U => pointProductIso f η U.unop M)
    (by
      intro U V g
      apply Pi.hom_ext
      intro p
      change Pi.map' _ (fun _ => 𝟙 M) ≫
          ((pointProductIso f η V.unop M).hom ≫ Pi.π _ p) =
        (pointProductIso f η U.unop M).hom ≫
          (Pi.map' _ (fun _ => 𝟙 M) ≫ Pi.π _ p)
      erw [pointProductIso_hom_π f η V.unop M p]
      simp only [Pi.map'_comp_π, Category.comp_id]
      erw [pointProductIso_hom_π f η U.unop M
        ((pointSmallEtale (η ≫ f)).fiber.map g.unop p)]
      simp only [Functor.op_map, Quiver.Hom.unop_op]
      erw [pointEquiv_naturality f η g.unop p]
      all_goals rfl)

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
  NatIso.ofComponents
    (fun M => ObjectProperty.isoMk _ (skyscraperPresheafIso f η M))
    (by
      intro M N q
      apply Sheaf.hom_ext
      apply NatTrans.ext
      funext U
      apply Pi.hom_ext
      intro p
      change Limits.Pi.map (fun _ => q) ≫
          ((skyscraperPresheafIso f η N).hom.app U ≫ Pi.π _ p) =
        (skyscraperPresheafIso f η M).hom.app U ≫
          (Limits.Pi.map (fun _ => q) ≫ Pi.π _ p)
      erw [skyscraperPresheafIso_hom_π f η N U.unop p]
      erw [Limits.Pi.map_π, Limits.Pi.map_π,
        skyscraperPresheafIso_hom_π_assoc f η M U.unop p q]
      rfl)

/-- The right-adjoint comparison retains the original pulled-back coordinate. -/
@[reassoc]
theorem skyscraperSheafIso_hom_π (M : AddCommGrpCat.{u + 1}) (U : X.Etale)
    (p : (pointSmallEtale (η ≫ f)).fiber.obj U) :
    ((skyscraperSheafIso f η).hom.app M).hom.app (op U) ≫ Pi.π _ p =
      Pi.π (fun _ : (pointSmallEtale η).fiber.obj ((siteBaseChange f).obj U) => M)
        (pulledBackPoint f η U p) :=
  skyscraperPresheafIso_hom_π f η M U p

end AlgebraicGeometry.Scheme.EtaleCohomology.StalkInverseImage
