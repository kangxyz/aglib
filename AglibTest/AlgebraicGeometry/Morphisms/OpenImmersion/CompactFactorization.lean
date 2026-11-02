/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Morphisms.OpenImmersion.CompactFactorization

/-!
# Consumer checks for compact factorization through directed open subschemes

The factorization retains the original morphism and its whole cartesian square. The compact
source form has no separatedness, finite-type or immersion premise.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u v

namespace AglibTest.OpenImmersionCompactFactorization

example {X Y : Scheme.{u}} [CompactSpace X] (f : X ⟶ Y)
    {I : Type v} [SemilatticeSup I] [Nonempty I]
    (U : I → Y.Opens) (hU : Monotone U)
    (hcover : Set.range f ⊆ (⨆ i, U i : Y.Opens)) :
    ∃ (i : I) (g : X ⟶ (U i).toScheme),
      g ≫ (U i).ι = f ∧ IsPullback g (𝟙 X) (U i).ι f :=
  f.exists_lift_opens_of_compactSpace U
    (fun i j => ⟨i ⊔ j, hU le_sup_left, hU le_sup_right⟩) hcover

/--
info: 'AlgebraicGeometry.Scheme.Hom.exists_lift_opens_of_isCompact_range' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms AlgebraicGeometry.Scheme.Hom.exists_lift_opens_of_isCompact_range

/--
info: 'AlgebraicGeometry.Scheme.Hom.exists_lift_opens_of_compactSpace' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms AlgebraicGeometry.Scheme.Hom.exists_lift_opens_of_compactSpace

end AglibTest.OpenImmersionCompactFactorization
