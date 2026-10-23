/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import
  Aglib.AlgebraicGeometry.EtaleCohomology.Finite.ExactImageComparison.PointFiberExtension
public import Mathlib.CategoryTheory.Sites.Point.Category
public import Mathlib.Algebra.Category.Grp.Colimits

/-! # Original stalk comparison for extensions of separably closed geometric points -/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe w

namespace CategoryTheory.GrothendieckTopology.Point.Hom

/-- Original point-morphism stalk maps preserve the prescribed actual germs. -/
theorem presheafFiber_germ
    {C : Type*} [Category* C] {J : GrothendieckTopology C}
    {Φ₁ Φ₂ : Point.{w} J} (f : Φ₁ ⟶ Φ₂)
    {A : Type*} [Category* A] [HasColimitsOfSize.{w, w} A]
    (P : Cᵒᵖ ⥤ A) (U : C) (p : Φ₂.fiber.obj U) :
    Φ₂.toPresheafFiber U p P ≫ f.presheafFiber.app P =
      Φ₁.toPresheafFiber U (f.hom.app U p) P := by
  let φ := fun (V : C) (x : Φ₂.fiber.obj V) => Φ₁.toPresheafFiber V (f.hom.app V x) P
  have hφ : ∀ ⦃V W : C⦄ (a : V ⟶ W) (x : Φ₂.fiber.obj V),
      P.map a.op ≫ φ V x = φ W (Φ₂.fiber.map a x) := by
    intro V W a x
    exact (Φ₁.toPresheafFiber_w a (f.hom.app V x) P).trans
      (congrArg (fun y => Φ₁.toPresheafFiber W y P)
        (ConcreteCategory.congr_hom (f.hom.naturality a) x).symm)
  change Φ₂.toPresheafFiber U p P ≫ Φ₂.presheafFiberDesc φ hφ = φ U p
  exact Φ₂.toPresheafFiber_presheafFiberDesc φ hφ U p

end CategoryTheory.GrothendieckTopology.Point.Hom

namespace AlgebraicGeometry.Scheme.EtaleCohomology

universe u

variable {κ Ω : Type u} [Field κ] [IsSepClosed κ] [Field Ω] [IsSepClosed Ω]
  {X : Scheme.{u}} (ξ : Spec (.of κ) ⟶ X) (e : Spec (.of Ω) ⟶ Spec (.of κ))

/-- Extension of the field is an isomorphism of the actual etale Hom-fibre functors. -/
def pointFiberExtensionIso : (pointSmallEtale ξ).fiber ≅ (pointSmallEtale (e ≫ ξ)).fiber :=
  NatIso.ofComponents
    (fun U => (Equiv.ofBijective (pointFiberExtension ξ e U)
      (pointFiberExtension_bijective ξ e U)).toIso)
    (by
      intro U V f
      apply ConcreteCategory.hom_ext
      intro p
      exact (Category.assoc
        (Over.homMk e rfl : Over.mk (e ≫ ξ) ⟶ Over.mk ξ) p
        ((Scheme.Etale.forget X).map f)).symm)

/-- The actual induced map of points, with the native contravariant convention. -/
def pointExtensionHom : pointSmallEtale (e ≫ ξ) ⟶ pointSmallEtale ξ :=
  ⟨(pointFiberExtensionIso ξ e).hom⟩

/-- The inverse point morphism uses the proved bijection of etale Hom fibres. -/
def pointExtensionInv : pointSmallEtale ξ ⟶ pointSmallEtale (e ≫ ξ) :=
  ⟨(pointFiberExtensionIso ξ e).inv⟩

/-- The original point morphisms are inverse, with no chosen replacement stalks. -/
theorem pointExtension_inv_hom : pointExtensionInv ξ e ≫ pointExtensionHom ξ e = 𝟙 _ := by
  apply GrothendieckTopology.Point.hom_ext
  exact (pointFiberExtensionIso ξ e).hom_inv_id

/-- The original point morphisms are inverse in the other order. -/
theorem pointExtension_hom_inv : pointExtensionHom ξ e ≫ pointExtensionInv ξ e = 𝟙 _ := by
  apply GrothendieckTopology.Point.hom_ext
  exact (pointFiberExtensionIso ξ e).inv_hom_id

/-- Extension of the geometric field gives the canonical isomorphism on original
abelian presheaf stalks, induced by the literal map on pointed neighborhoods. -/
def pointExtensionPresheafFiberIso :
    (pointSmallEtale ξ).presheafFiber (A := AddCommGrpCat.{u + 1}) ≅
      (pointSmallEtale (e ≫ ξ)).presheafFiber where
  hom := (pointExtensionHom ξ e).presheafFiber
  inv := (pointExtensionInv ξ e).presheafFiber
  hom_inv_id := by
    rw [← GrothendieckTopology.Point.Hom.presheafFiber_comp, pointExtension_inv_hom,
      GrothendieckTopology.Point.Hom.presheafFiber_id]
  inv_hom_id := by
    rw [← GrothendieckTopology.Point.Hom.presheafFiber_comp, pointExtension_hom_inv,
      GrothendieckTopology.Point.Hom.presheafFiber_id]

/-- The new comparison preserves the literal original germ at the extended point. -/
theorem pointExtensionPresheafFiberIso_germ
    (P : X.Etaleᵒᵖ ⥤ AddCommGrpCat.{u + 1}) (U : X.Etale)
    (p : (pointSmallEtale ξ).fiber.obj U) :
    (pointSmallEtale ξ).toPresheafFiber U p P ≫
        (pointExtensionPresheafFiberIso ξ e).hom.app P =
      (pointSmallEtale (e ≫ ξ)).toPresheafFiber U (pointFiberExtension ξ e U p) P := by
  exact GrothendieckTopology.Point.Hom.presheafFiber_germ (pointExtensionHom ξ e) P U p

end AlgebraicGeometry.Scheme.EtaleCohomology
