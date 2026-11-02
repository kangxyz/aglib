/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.Exceptional.Finite.LowerShriek

/-! Original diagonal and clopen maps, with approved-axiom guards. -/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry
open AlgebraicGeometry.Scheme.EtaleCohomology

universe u
variable {Y X : Scheme.{u}}

/-- The raw diagonal comparison is available for separated étale maps before finiteness. -/
example (f : Y ⟶ X) [Etale f] [IsSeparated f] :
    (etaleLowerShriekAdjunction f).unit ≫
      Functor.whiskerRight (etaleLowerShriekToDirectImage f) (inverseImage f) =
        etaleDirectImageDiagonalMap f := etaleLowerShriekToDirectImage_unit f

/-- info: 'AlgebraicGeometry.Scheme.EtaleCohomology.etaleLowerShriekClopenIso_unit'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms AlgebraicGeometry.Scheme.EtaleCohomology.etaleLowerShriekClopenIso_unit

/-- info: 'AlgebraicGeometry.Scheme.EtaleCohomology.etaleDiagonalLowerShriekMap_unit'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms AlgebraicGeometry.Scheme.EtaleCohomology.etaleDiagonalLowerShriekMap_unit

/-- info: 'AlgebraicGeometry.Scheme.EtaleCohomology.etaleDirectImageDiagonalMap_baseChange'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms AlgebraicGeometry.Scheme.EtaleCohomology.etaleDirectImageDiagonalMap_baseChange

/-- info: 'AlgebraicGeometry.Scheme.EtaleCohomology.etaleDirectImageDiagonalMap_off_diagonal'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms AlgebraicGeometry.Scheme.EtaleCohomology.etaleDirectImageDiagonalMap_off_diagonal

/-- info: 'AlgebraicGeometry.Scheme.EtaleCohomology.etaleLowerShriekToDirectImage_unit'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms AlgebraicGeometry.Scheme.EtaleCohomology.etaleLowerShriekToDirectImage_unit

/-- info: 'AlgebraicGeometry.Scheme.EtaleCohomology.etaleDiagonalLowerShriekMap_inverseImage'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms AlgebraicGeometry.Scheme.EtaleCohomology.etaleDiagonalLowerShriekMap_inverseImage


/-- info: 'AlgebraicGeometry.Scheme.EtaleCohomology.finiteEtaleDirectImage_right_triangle'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms AlgebraicGeometry.Scheme.EtaleCohomology.finiteEtaleDirectImage_right_triangle

/-- info: 'AlgebraicGeometry.Scheme.EtaleCohomology.finiteEtaleDirectImage_left_triangle'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms AlgebraicGeometry.Scheme.EtaleCohomology.finiteEtaleDirectImage_left_triangle

/-- info: 'AlgebraicGeometry.Scheme.EtaleCohomology.finiteEtaleLowerShriekToDirectImage_isIso'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms AlgebraicGeometry.Scheme.EtaleCohomology.finiteEtaleLowerShriekToDirectImage_isIso

/-- info: 'AlgebraicGeometry.Scheme.EtaleCohomology.finiteEtaleLowerShriekToDirectImage_counit'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms AlgebraicGeometry.Scheme.EtaleCohomology.finiteEtaleLowerShriekToDirectImage_counit
