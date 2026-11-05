/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.Constructible.Modules.FixedTargetEquality

/-! # Original native maps above any specified model stage

The actual under-category tail has the chosen model as its initial stage.
Its native final forgetful functor retains the actual scheme colimit. The
fixed-target Hom theorem therefore gives original native maps and equations
above every specified stage of the original filtered base system.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.Scheme.EtaleCohomology.Continuity.NativeModule
namespace ModelDescent

universe u

attribute [local instance] ModuleCat.Sheaf.hasSheafify

open Constructible.Modules.NativeFreePresentation

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

variable (R : Type (u + 1)) [Ring R]

private instance coefficientColimits (S : Scheme.{u}) :
    HasColimitsOfShape I (Coefficient R S) := by
  let : HasColimitsOfShape I AddCommGrpCat.{u + 1} := AddCommGrpCat.hasColimitsOfShape
  let : HasColimitsOfShape I (ModuleCat.{u + 1} R) := ModuleCat.hasColimitsOfShape R I
  exact CategoryTheory.Sheaf.instHasColimitsOfShape (J := S.smallEtaleTopology) (K := I)

/-- The original native inverse-image triangle. -/
def coneCompIso {j : I} (a : i ⟶ j) :
    inverseImage R (c.ι.app i).unop ≅
      inverseImage R (X.map a).unop ⋙ inverseImage R (c.ι.app j).unop :=
  (schemeAdjunctionData R).triangleIso (c.ι.app i) (X.map a) (c.ι.app j) (c.w a)

variable [IsFiltered I]
  [∀ {j k} (a : j ⟶ k), IsAffineHom (X.map a).unop] (hc : IsColimit c)

include hc in
/-- An original native Hom at the limit lifts to an actual later-stage
native Hom, retaining the native original cone-composition square. -/
theorem exists_nativeHom_above
    (A : Coefficient R (X.obj i).unop)
    (hA : finiteColimitStages R (X.obj i).unop A)
    (B : Coefficient R (X.obj i).unop)
    (γ : (inverseImage R (c.ι.app i).unop).obj A ⟶
      (inverseImage R (c.ι.app i).unop).obj B) :
    ∃ (j : I) (a : i ⟶ j)
      (β : (inverseImage R (X.map a).unop).obj A ⟶
        (inverseImage R (X.map a).unop).obj B),
      (coneCompIso X c i R a).hom.app A ≫
          (inverseImage R (c.ι.app j).unop).map β =
        γ ≫ (coneCompIso X c i R a).hom.app B := by
  let T := modelTail X i
  let C := modelTailCocone X c i
  have {a b : Under i} (q : a ⟶ b) : IsAffineHom (T.map q).unop :=
    inferInstanceAs (IsAffineHom (X.map q.right).unop)
  obtain ⟨a, β, hβ⟩ := exists_baseHom R T (Under.mk (𝟙 i)) (modelTailBase X i)
    (modelTailBase_id X i) C (modelTailCoconeIsColimit X c i hc) A hA B γ
  exact ⟨a.right.right, a.hom.right, β, hβ⟩

include hc in
/-- Equality after the original limit inverse image holds after one actual
later original base transition, for a native canonical source stage. -/
theorem nativeHom_eventually_equal_above
    (A : Coefficient R (X.obj i).unop)
    (hA : finiteColimitStages R (X.obj i).unop A)
    (B : Coefficient R (X.obj i).unop) (f g : A ⟶ B)
    (h : (inverseImage R (c.ι.app i).unop).map f =
      (inverseImage R (c.ι.app i).unop).map g) :
    ∃ (j : I) (a : i ⟶ j), (inverseImage R (X.map a).unop).map f =
      (inverseImage R (X.map a).unop).map g := by
  let T := modelTail X i
  let C := modelTailCocone X c i
  have {a b : Under i} (q : a ⟶ b) : IsAffineHom (T.map q).unop :=
    inferInstanceAs (IsAffineHom (X.map q.right).unop)
  obtain ⟨a, ha⟩ := baseHom_eventually_equal R T (Under.mk (𝟙 i)) (modelTailBase X i)
    (modelTailBase_id X i) C B (modelTailCoconeIsColimit X c i hc) A hA f g h
  exact ⟨a.right.right, a.hom.right, ha⟩

end ModelDescent
end AlgebraicGeometry.Scheme.EtaleCohomology.Continuity.NativeModule
