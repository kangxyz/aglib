/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.Finite.DirectImageEvaluationComposition

/-! Original pointed-map interfaces and approved-axiom guards. -/

@[expose] public section

open CategoryTheory AlgebraicGeometry
open AlgebraicGeometry.Scheme.EtaleCohomology

universe u
variable {X Y Z : Scheme.{u}} {Ω : Type u} [Field Ω] [IsSepClosed Ω]
  (f : Y ⟶ X) (g : Z ⟶ Y)
  (x : Spec (.of Ω) ⟶ X) (y : Spec (.of Ω) ⟶ Y) (z : Spec (.of Ω) ⟶ Z)
  (hy : y ≫ f = x) (hz : z ≫ g = y)

/-- Original pointed evaluation composes for arbitrary scheme arrows, without finite or Ext data. -/
example (F : AbelianSheaf.{u, u + 1} Z) :
    (Scheme.pointSmallEtale x).sheafFiber.map ((directImageCompIso f g).hom.app F) ≫
        pointedDirectImageEvaluation (g ≫ f) z x (by rw [← Category.assoc, hz, hy]) F =
      pointedDirectImageEvaluation f y x hy ((directImage g).obj F) ≫
        pointedDirectImageEvaluation g z y hz F :=
  pointedDirectImageEvaluation_comp f y x hy g z hz F

/-- info: 'AlgebraicGeometry.Scheme.EtaleCohomology.pointedDirectImageEvaluation_naturality'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms AlgebraicGeometry.Scheme.EtaleCohomology.pointedDirectImageEvaluation_naturality

/-- info: 'AlgebraicGeometry.Scheme.EtaleCohomology.pointedDirectImageEvaluationNatTrans_eq_unit_counit'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms AlgebraicGeometry.Scheme.EtaleCohomology.pointedDirectImageEvaluationNatTrans_eq_unit_counit

/-- info: 'AlgebraicGeometry.Scheme.EtaleCohomology.pointedDirectImageEvaluationNatTrans_congr'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms AlgebraicGeometry.Scheme.EtaleCohomology.pointedDirectImageEvaluationNatTrans_congr

/-- info: 'AlgebraicGeometry.Scheme.EtaleCohomology.pointedDirectImageEvaluationNatTrans_id'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms AlgebraicGeometry.Scheme.EtaleCohomology.pointedDirectImageEvaluationNatTrans_id

/-- info: 'AlgebraicGeometry.Scheme.EtaleCohomology.pointedDirectImageEvaluationNatTrans_comp'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms AlgebraicGeometry.Scheme.EtaleCohomology.pointedDirectImageEvaluationNatTrans_comp
