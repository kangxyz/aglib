/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Aglib.AlgebraicGeometry.Picard.Comparison.Endomorphisms

/-! Focused consumer of the global-scalar facts used by the rigidification of the Picard
functor: pullback of a global scalar is the scalar pulled back along `appTop`, and every
endomorphism of an actual locally rank-one module sheaf is a global scalar. -/

@[expose] public section

noncomputable section
open CategoryTheory AlgebraicGeometry Scheme.Modules

universe u

variable {X Y : Scheme.{u}} (f : X ⟶ Y)

example (M : Y.Modules) (a : Γ(Y, ⊤)) :
    (pullback f).map (globalScalarEndomorphism Y M a) =
      globalScalarEndomorphism X ((pullback f).obj M) (f.appTop a) :=
  pullback_map_globalScalarEndomorphism f M a

example (M : X.Modules) (hM : Invertible.IsLocallyRankOne X M) (φ : M ⟶ M) :
    ∃ r : Γ(X, ⊤), φ = globalScalarEndomorphism X M r :=
  exists_eq_globalScalarEndomorphism_of_isLocallyRankOne hM φ

example (M : X.Modules) (e : M ≅ SheafOfModules.unit X.ringCatSheaf) :
    Function.Injective (globalScalarEndomorphism X M) :=
  globalScalarEndomorphism_injective_of_iso e

/--
info: 'AlgebraicGeometry.Scheme.Modules.pullback_map_globalScalarEndomorphism' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms pullback_map_globalScalarEndomorphism

/--
info: 'AlgebraicGeometry.Scheme.Modules.exists_eq_globalScalarEndomorphism_of_isLocallyRankOne' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms exists_eq_globalScalarEndomorphism_of_isLocallyRankOne

/--
info: 'AlgebraicGeometry.Scheme.Modules.globalScalarEndomorphism_unitIsoGlobalUnit' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms globalScalarEndomorphism_unitIsoGlobalUnit
