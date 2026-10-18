/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Aglib.AlgebraicGeometry.Modules.FittingIdeal.Pullback

/-! Focused consumer of the Fitting ideal sheaves of a quasi-coherent sheaf of finite type (Stacks
Project, Tag 0C3C) and of their pullback (Tags 07ZA (3), 0C3D), with axiom guards. -/

@[expose] public section

open CategoryTheory Limits AlgebraicGeometry

universe u

example {S : Scheme.{u}} (F : S.Modules)
    (hF : Scheme.Modules.QuasiCoherent.affineLocallyFiniteType S F) (k : ℕ) (U : S.affineOpens) :
    (Scheme.Modules.fittingIdealSheaf F hF k).ideal U = Module.fittingIdeal Γ(S, U) Γ(F, U) k :=
  rfl

example {S T : Scheme.{u}} (g : T ⟶ S) (F : S.Modules)
    (hF : Scheme.Modules.QuasiCoherent.affineLocallyFiniteType S F) [F.IsFinitePresentation]
    (k : ℕ) :
    (Scheme.Modules.fittingIdealSheaf F hF k).comap g =
      Scheme.Modules.fittingIdealSheaf ((Scheme.Modules.pullback g).obj F)
        (Scheme.Modules.QuasiCoherent.affineLocallyFiniteType_pullback_of_finitePresentation
          g F) k :=
  Scheme.Modules.fittingIdealSheaf_comap g F hF _ k

/--
info: 'AlgebraicGeometry.Scheme.Modules.fittingIdealSheaf' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms AlgebraicGeometry.Scheme.Modules.fittingIdealSheaf

/--
info: 'AlgebraicGeometry.Scheme.Modules.fittingIdeal_sections_basicOpen' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms AlgebraicGeometry.Scheme.Modules.fittingIdeal_sections_basicOpen

/--
info: 'AlgebraicGeometry.Scheme.Modules.fittingIdeal_sections_pullback' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms AlgebraicGeometry.Scheme.Modules.fittingIdeal_sections_pullback

/--
info: 'AlgebraicGeometry.Scheme.Modules.fittingIdealSheaf_comap' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms AlgebraicGeometry.Scheme.Modules.fittingIdealSheaf_comap

/--
info: 'AlgebraicGeometry.Scheme.Modules.QuasiCoherent.finite_sections_of_affineLocallyFiniteType' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms AlgebraicGeometry.Scheme.Modules.QuasiCoherent.finite_sections_of_affineLocallyFiniteType

/--
info: 'AlgebraicGeometry.Scheme.Modules.QuasiCoherent.affineLocallyFiniteType_pullback_of_finitePresentation' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms AlgebraicGeometry.Scheme.Modules.QuasiCoherent.affineLocallyFiniteType_pullback_of_finitePresentation
