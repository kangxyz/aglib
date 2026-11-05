/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.Constructible.Modules.HomAbove
public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Zero
public import Mathlib.CategoryTheory.Preadditive.AdditiveFunctor

/-! # Original annihilator relations descend over the unchanged ring

An annihilator at the actual limit is an equality of two actual model arrows.
Native eventual equality descends it without replacing the coefficient ring
or forgetting to a finite underlying additive group.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.Scheme.EtaleCohomology.Continuity.NativeModule
namespace ModelDescent

universe u

variable (R : Type (u + 1)) [Ring R]

private instance nativeInverseImage_additive {S T : Scheme.{u}} (f : S ⟶ T) :
    (inverseImage R f).Additive := by
  let : (inverseImage R f).IsLeftAdjoint := (imageAdjunction R f).isLeftAdjoint
  exact Functor.additive_of_preserves_binary_products _

/-- A literal annihilator relation at the limit holds at an actual later
original model, over exactly the same coefficient ring. -/
theorem annihilator_eventually_above
    {I : Type u} [SmallCategory I] [IsFiltered I]
    (X : I ⥤ Scheme.{u}ᵒᵖ) (c : Cocone X) (hc : IsColimit c)
    [∀ {i j} (q : i ⟶ j), IsAffineHom (X.map q).unop]
    (i : I) (A : Coefficient R (X.obj i).unop)
    (hA : Constructible.Modules.NativeFreePresentation.finiteColimitStages R (X.obj i).unop A)
    (n : ℕ) (hn : n • 𝟙 ((inverseImage R (c.ι.app i).unop).obj A) = 0) :
    ∃ (j : I) (q : i ⟶ j), n • 𝟙 ((inverseImage R (X.map q).unop).obj A) = 0 := by
  let L := inverseImage R (c.ι.app i).unop
  have h : L.map (n • 𝟙 A) = L.map (0 : A ⟶ A) :=
    (L.map_nsmul.trans (congrArg (fun f => n • f) (L.map_id A))).trans
      (hn.trans (L.map_zero A A).symm)
  obtain ⟨j, q, hq⟩ := nativeHom_eventually_equal_above X c i R hc A hA A (n • 𝟙 A) 0 h
  let K := inverseImage R (X.map q).unop
  exact ⟨j, q, (K.map_nsmul.trans (congrArg (fun f => n • f) (K.map_id A))).symm.trans
    (hq.trans (K.map_zero A A))⟩

end ModelDescent
end AlgebraicGeometry.Scheme.EtaleCohomology.Continuity.NativeModule
