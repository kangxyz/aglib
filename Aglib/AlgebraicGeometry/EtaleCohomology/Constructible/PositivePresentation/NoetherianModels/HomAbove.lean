/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.Constructible.PositivePresentation.NoetherianModels.FixedTargetHom

/-! # Original bounded maps above any specified model stage

The actual under-category tail has the chosen model as its initial stage.
Its native final forgetful functor retains the actual scheme colimit. The
fixed-target Hom theorem therefore gives original bounded maps and equations
above every specified stage of the original filtered base system.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.Scheme.EtaleCohomology.Constructible.PositivePresentation
namespace NoetherianModels

universe u

attribute [local instance] hasSheafifyLarge TorsionZMod.hasSheafifyStandard
  Cardinal.fact_isRegular_aleph0

open Continuity

variable {I : Type u} [SmallCategory I]
  (X : I ⥤ Scheme.{u}ᵒᵖ) (c : Cocone X) (i : I)

/-- The actual tail of the original inverse scheme diagram. -/
def modelTail : Under i ⥤ Scheme.{u}ᵒᵖ := Under.forget i ⋙ X

/-- The original structural arrows from the chosen model to that tail. -/
def modelTailBase : (Functor.const (Under i)).obj (X.obj i) ⟶ modelTail X i where
  app a := X.map a.hom
  naturality {a b} q := by
    change 𝟙 _ ≫ X.map b.hom = X.map a.hom ≫ X.map q.right
    rw [Category.id_comp, ← X.map_comp, Under.w q]

/-- The tail's chosen base component is the original identity comparison. -/
theorem modelTailBase_id :
    (modelTailBase X i).app (Under.mk (𝟙 i)) = 𝟙 (X.obj i) := X.map_id i

/-- The actual original limit cocone restricted to the tail. -/
def modelTailCocone : Cocone (modelTail X i) := c.whisker (Under.forget i)

/-- The original tail is final, so its specified cocone remains colimiting. -/
def modelTailCoconeIsColimit [IsFiltered I] (hc : IsColimit c) :
    IsColimit (modelTailCocone X c i) :=
  (Functor.Final.isColimitWhiskerEquiv (Under.forget i) c).symm hc

/-- The original cone/transition inverse-image comparison in bounded coefficients. -/
def boundedConeCompIso (n : ℕ) {i j : I} (a : i ⟶ j) :
    boundedInverseImage (c.ι.app i).unop n ≅
      boundedInverseImage (X.map a).unop n ⋙ boundedInverseImage (c.ι.app j).unop n :=
  boundedPullbackTriangleIso (c.ι.app i).unop (X.map a).unop
    (c.ι.app j).unop (coneSquare X c a) n

variable [IsFiltered I]
  [∀ {j k} (a : j ⟶ k), IsAffineHom (X.map a).unop] (hc : IsColimit c)

include hc in
/-- An original bounded Hom at the limit lifts to an actual later-stage
bounded Hom, retaining the native original cone-composition square. -/
theorem exists_boundedHom_above (n : ℕ)
    (A : BoundedPresentation.Coefficient (X.obj i).unop n)
    (hA : BoundedPresentation.finiteColimitStages (X.obj i).unop n A)
    (B : BoundedPresentation.Coefficient (X.obj i).unop n)
    (γ : (boundedInverseImage (c.ι.app i).unop n).obj A ⟶
      (boundedInverseImage (c.ι.app i).unop n).obj B) :
    ∃ (j : I) (a : i ⟶ j)
      (β : (boundedInverseImage (X.map a).unop n).obj A ⟶
        (boundedInverseImage (X.map a).unop n).obj B),
      (boundedConeCompIso X c n a).hom.app A ≫
          (boundedInverseImage (c.ι.app j).unop n).map β =
        γ ≫ (boundedConeCompIso X c n a).hom.app B := by
  let T := modelTail X i
  let C := modelTailCocone X c i
  have {a b : Under i} (q : a ⟶ b) : IsAffineHom (T.map q).unop :=
    inferInstanceAs (IsAffineHom (X.map q.right).unop)
  obtain ⟨a, β, hβ⟩ := exists_baseHom T (Under.mk (𝟙 i)) (modelTailBase X i)
    (modelTailBase_id X i) C (modelTailCoconeIsColimit X c i hc) n A hA B γ.hom
  refine ⟨a.right.right, a.hom.right, ObjectProperty.homMk β, ?_⟩
  apply ObjectProperty.hom_ext
  exact hβ

include hc in
/-- Equality after the original limit inverse image holds after one actual
later original base transition, for a native canonical source stage. -/
theorem boundedHom_eventually_equal_above (n : ℕ)
    (A : BoundedPresentation.Coefficient (X.obj i).unop n)
    (hA : BoundedPresentation.finiteColimitStages (X.obj i).unop n A)
    (B : BoundedPresentation.Coefficient (X.obj i).unop n) (f g : A ⟶ B)
    (h : (boundedInverseImage (c.ι.app i).unop n).map f =
      (boundedInverseImage (c.ι.app i).unop n).map g) :
    ∃ (j : I) (a : i ⟶ j), (boundedInverseImage (X.map a).unop n).map f =
      (boundedInverseImage (X.map a).unop n).map g := by
  let T := modelTail X i
  let C := modelTailCocone X c i
  have {a b : Under i} (q : a ⟶ b) : IsAffineHom (T.map q).unop :=
    inferInstanceAs (IsAffineHom (X.map q.right).unop)
  obtain ⟨a, ha⟩ := baseHom_eventually_equal T (Under.mk (𝟙 i)) (modelTailBase X i)
    (modelTailBase_id X i) C (modelTailCoconeIsColimit X c i hc) n A hA B f.hom g.hom
      (congrArg (fun f => f.hom) h)
  refine ⟨a.right.right, a.hom.right, ?_⟩
  apply ObjectProperty.hom_ext
  exact ha

end NoetherianModels
end AlgebraicGeometry.Scheme.EtaleCohomology.Constructible.PositivePresentation
