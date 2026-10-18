/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Aglib.AlgebraicGeometry.Cohomology.BaseChange.Modules.Naturality

/-! Focused consumer of the naturality of geometric pullback and of the cohomology base-change map
in the coefficient module, with axiom guards. -/

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.Scheme.Cohomology

universe u

/-- Geometric pullback on degree-zero module cohomology commutes with a coefficient map. -/
example {X Y : Scheme.{u}} (f : X ⟶ Y) {M M' : Y.Modules} (φ : M ⟶ M')
    (x : Sheaf.H.{u + 1} (moduleAddSheaf Y M) 0) :
    moduleCohomologyPullback f M' 0
        (Sheaf.H.map ((SheafOfModules.toSheaf Y.ringCatSheaf).map φ) 0 x) =
      Sheaf.H.map ((SheafOfModules.toSheaf X.ringCatSheaf).map
        ((Scheme.Modules.pullback f).map φ)) 0 (moduleCohomologyPullback f M 0 x) :=
  moduleCohomologyPullback_map f φ 0 x

/--
info: 'AlgebraicGeometry.Scheme.Cohomology.zariskiCohomologyMap_map' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms AlgebraicGeometry.Scheme.Cohomology.zariskiCohomologyMap_map

/--
info: 'AlgebraicGeometry.Scheme.Cohomology.moduleCohomologyPullback_map' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms AlgebraicGeometry.Scheme.Cohomology.moduleCohomologyPullback_map

/--
info: 'AlgebraicGeometry.Scheme.Cohomology.moduleCohomologyBaseChangeMap_naturality' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms AlgebraicGeometry.Scheme.Cohomology.moduleCohomologyBaseChangeMap_naturality
