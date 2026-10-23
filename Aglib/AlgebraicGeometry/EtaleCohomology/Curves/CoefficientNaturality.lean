/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.Curves.ConstantRestriction

/-!
# Coefficient naturality of original constant restriction

The coefficient square uses the original constant-sheaf functors and the
original inverse-image constant comparison. It allows finite split coefficient
arguments without replacing the restriction map by an abstract equivalent map.
-/

@[expose] public noncomputable section

universe u w w'

open CategoryTheory

namespace AlgebraicGeometry.Scheme.EtaleCohomology.Curves

attribute [local instance] hasSheafifyLarge

variable {A B : Type u} [AddCommGroup A] [AddCommGroup B]
  {X S : Scheme.{u}} (f : S ⟶ X)
  [HasExt.{w} (AbelianSheaf.{u, u + 1} X)]
  [HasExt.{w'} (AbelianSheaf.{u, u + 1} S)]

/-- Constant restriction commutes with every original morphism of coefficient values. -/
theorem constantRestriction_coefficientMap
    (a : ConstantFinite.value A ⟶ ConstantFinite.value B) (q : ℕ)
    (x : Sheaf.H.{w} (ConstantFinite.coefficient A X) q) :
    constantRestriction B f q
      (Sheaf.H.map
        ((constantSheaf (Scheme.smallEtaleTopology X) AddCommGrpCat.{u + 1}).map a) q x) =
      Sheaf.H.map ((constantSheaf (Scheme.smallEtaleTopology S) AddCommGrpCat.{u + 1}).map a) q
        (constantRestriction A f q x) := by
  change Sheaf.H.map _ q (cohomologyPullback f _ q (Sheaf.H.map _ q x)) =
    Sheaf.H.map _ q (Sheaf.H.map _ q (cohomologyPullback f _ q x))
  rw [cohomologyPullback_coefficientMap, ← Sheaf.H.map_comp_apply,
    ← Sheaf.H.map_comp_apply]
  exact congrArg (fun g => Sheaf.H.map g q (cohomologyPullback f _ q x))
    ((inverseImageConstantIso f).hom.naturality a)

/-- A split coefficient retract inherits surjectivity of the actual restriction map. -/
theorem constantRestriction_surjective_of_retract
    (i : ConstantFinite.value A ⟶ ConstantFinite.value B)
    (r : ConstantFinite.value B ⟶ ConstantFinite.value A)
    (hir : i ≫ r = 𝟙 _) (q : ℕ)
    (hB : Function.Surjective (constantRestriction B f q)) :
    Function.Surjective (constantRestriction A f q) := by
  intro x
  obtain ⟨y, hy⟩ := hB
    (Sheaf.H.map ((constantSheaf (Scheme.smallEtaleTopology S) AddCommGrpCat.{u + 1}).map i) q x)
  refine ⟨Sheaf.H.map
    ((constantSheaf (Scheme.smallEtaleTopology X) AddCommGrpCat.{u + 1}).map r) q y, ?_⟩
  rw [constantRestriction_coefficientMap, hy, ← Sheaf.H.map_comp_apply,
    ← CategoryTheory.Functor.map_comp, hir, CategoryTheory.Functor.map_id, Sheaf.H.map_id_apply]

end AlgebraicGeometry.Scheme.EtaleCohomology.Curves
