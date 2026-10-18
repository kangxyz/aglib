/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Aglib.AlgebraicGeometry.IdealSheaf.GlueImmersion

/-! Focused consumer of the gluing of immersions that represent a Zariski-local condition, with
axiom guards. -/

@[expose] public section

open CategoryTheory Limits AlgebraicGeometry

universe u

/-- A condition on morphisms from locally Noetherian schemes, stable under restriction to opens,
local on the source and represented by immersions near every point, is represented by one
immersion. -/
example {X : Scheme.{u}} [IsLocallyNoetherian X] (P : ∀ ⦃T : Scheme.{u}⦄, (T ⟶ X) → Prop)
    (hres : ∀ ⦃T : Scheme.{u}⦄ [IsLocallyNoetherian T] (g : T ⟶ X) (V : T.Opens), P g →
      P (V.ι ≫ g))
    (hloc : ∀ ⦃T : Scheme.{u}⦄ [IsLocallyNoetherian T] (g : T ⟶ X),
      (∀ t : T, ∃ V : T.Opens, t ∈ V ∧ P (V.ι ≫ g)) → P g)
    (hrep : ∀ x : X, ∃ (U : X.Opens) (_ : x ∈ U) (Z : Scheme.{u}) (m : Z ⟶ X) (_ : IsImmersion m),
      Set.range m ⊆ U ∧ ∀ ⦃T : Scheme.{u}⦄ [IsLocallyNoetherian T] (g : T ⟶ X),
        Set.range g ⊆ U → (P g ↔ ∃ h : T ⟶ Z, h ≫ m = g)) :
    ∃ (Z : Scheme.{u}) (m : Z ⟶ X), IsImmersion m ∧
      ∀ ⦃T : Scheme.{u}⦄ [IsLocallyNoetherian T] (g : T ⟶ X),
        (∃ h : T ⟶ Z, h ≫ m = g) ↔ P g :=
  Scheme.exists_isImmersion_forall_exists_lift_iff P hres hloc hrep

/-- Factorization through a closed immersion is read on the pullback of its kernel. -/
example {Z Y W : Scheme.{u}} (c : Z ⟶ Y) [IsClosedImmersion c] (k : W ⟶ Y) :
    (∃ a : W ⟶ Z, a ≫ c = k) ↔ c.ker.comap k = ⊥ :=
  Scheme.exists_lift_iff_comap_ker_eq_bot c k


/--
info: 'AlgebraicGeometry.Scheme.exists_isImmersion_forall_exists_lift_iff' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms AlgebraicGeometry.Scheme.exists_isImmersion_forall_exists_lift_iff

/--
info: 'AlgebraicGeometry.Scheme.exists_lift_iff_comap_ker_eq_bot' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms AlgebraicGeometry.Scheme.exists_lift_iff_comap_ker_eq_bot

/--
info: 'AlgebraicGeometry.Scheme.comap_ker_glueImmersionLift_eq' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms AlgebraicGeometry.Scheme.comap_ker_glueImmersionLift_eq

/--
info: 'AlgebraicGeometry.Scheme.exists_comp_glueImmersion_eq' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms AlgebraicGeometry.Scheme.exists_comp_glueImmersion_eq

/--
info: 'AlgebraicGeometry.Scheme.exists_lift_glueImmersionLift_of_exists_lift' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms AlgebraicGeometry.Scheme.exists_lift_glueImmersionLift_of_exists_lift
