/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Mathlib.Algebra.Module.ZMod
public import Mathlib.Algebra.Category.ModuleCat.Basic
public import Mathlib.CategoryTheory.Sites.Whiskering

/-! # Full scalar forgetting for genuine ZMod coefficients

Every additive map between actual ZMod modules is linear for their supplied
scalar actions. The original underlying-abelian functor, and its original
sheaf-composition functor, are therefore full. This includes modulus zero;
no injectivity assertion after forgetting scalars is made.
-/

@[expose] public noncomputable section

namespace CategoryTheory.TorsionZMod

universe u v w

/-- The original underlying-abelian functor on actual module objects is full. -/
theorem moduleUnderlying_full (n : ℕ) :
    (forget₂ (ModuleCat.{w} (ZMod n)) AddCommGrpCat.{w}).Full where
  map_surjective {X Y} f := by
    let g : X →+ Y := f.hom
    exact ⟨ModuleCat.ofHom (g.toZModLinearMap n), rfl⟩

/-- Every original underlying abelian coefficient arrow lifts to an arrow of
the supplied genuine module sheaves, with their original scalar actions. -/
theorem sheafUnderlying_full {C : Type u} [Category.{v} C]
    (J : GrothendieckTopology C) (n : ℕ)
    [J.HasSheafCompose (forget₂ (ModuleCat.{w} (ZMod n)) AddCommGrpCat.{w})] :
    (sheafCompose J (forget₂ (ModuleCat.{w} (ZMod n)) AddCommGrpCat.{w})).Full := by
  let : (forget₂ (ModuleCat.{w} (ZMod n)) AddCommGrpCat.{w}).Full :=
    moduleUnderlying_full n
  infer_instance

end CategoryTheory.TorsionZMod
