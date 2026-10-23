/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.H0.ConstantSections
public import Mathlib.Algebra.Category.Grp.Ulift

/-! # Actual morphisms between finite constant additive sheaves

On a nonempty one-point base, including the spectrum of any field, the original
constant functor is fully faithful on finite values. No separable-closure or
local-site hypothesis is imposed on the base field.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Scheme.EtaleCohomology.ConstantFinite

attribute [local instance] hasSheafifyLarge

variable (X : Scheme.{u}) [Nonempty X] [Subsingleton X]
  (A B : Type u) [AddCommGroup A] [AddCommGroup B] [Finite B]

/-- The original constant functor induces a bijection on the displayed Hom sets. -/
theorem constant_map_bijective : Function.Bijective
    (fun f : value A ⟶ value B =>
      (constantSheaf (smallEtaleTopology X) AddCommGrpCat.{u+1}).map f) := by
  let adj := constantAdjunction X
  let e : value B ≅ (globalSections X).obj (coefficient B X) :=
    (AddEquiv.ofBijective (adj.unit.app (value B)).hom
      (constantUnit_bijective X B)).toAddCommGrpIso
  have he : e.hom = adj.unit.app (value B) := by
    ext x
    rfl
  have hmap (f : value A ⟶ value B) :
      adj.homEquiv (value A) (coefficient B X)
        ((constantSheaf (smallEtaleTopology X) AddCommGrpCat.{u+1}).map f) = f ≫ e.hom := by
    rw [he]
    simpa only [Category.comp_id, Adjunction.homEquiv_id] using
      adj.homEquiv_naturality_left f (𝟙 (coefficient B X))
  constructor
  · intro f g hfg
    apply (cancel_mono e.hom).mp
    rw [← hmap, ← hmap]
    exact congrArg (adj.homEquiv (value A) (coefficient B X)) hfg
  · intro g
    refine ⟨adj.homEquiv (value A) (coefficient B X) g ≫ e.inv, ?_⟩
    apply (adj.homEquiv (value A) (coefficient B X)).injective
    rw [hmap]
    simp

/-- Every actual sheaf morphism comes from a unique original additive value map. -/
theorem constant_addHom_bijective : Function.Bijective
    (fun f : A →+ B =>
      (constantSheaf (smallEtaleTopology X) AddCommGrpCat.{u+1}).map
        (AddCommGrpCat.uliftFunctor.{u+1,u}.map (AddCommGrpCat.ofHom f))) := by
  have hU : Function.Bijective
      (AddCommGrpCat.uliftFunctor.{u+1,u}.map :
        (AddCommGrpCat.of A ⟶ AddCommGrpCat.of B) → (value A ⟶ value B)) :=
    ⟨(AddCommGrpCat.uliftFunctor.{u+1,u}).map_injective,
      (AddCommGrpCat.uliftFunctor.{u+1,u}).map_surjective⟩
  have hV : Function.Bijective
      (AddCommGrpCat.ofHom : (A →+ B) → (AddCommGrpCat.of A ⟶ AddCommGrpCat.of B)) :=
    ⟨fun _ _ h => congrArg AddCommGrpCat.Hom.hom h, fun g => ⟨g.hom, rfl⟩⟩
  exact (constant_map_bijective X A B).comp (hU.comp hV)

end AlgebraicGeometry.Scheme.EtaleCohomology.ConstantFinite
