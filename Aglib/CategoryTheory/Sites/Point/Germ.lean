/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Mathlib.CategoryTheory.Sites.Point.Category

/-! # Original germ values of native point morphisms -/

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

