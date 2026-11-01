/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.H1.CyclicKilling

/-! The original class and pullback, with independent source and target Ext worlds. -/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry
open AlgebraicGeometry.Scheme.EtaleCohomology

universe u w w'

attribute [local instance] hasSheafifyLarge

variable {X : Scheme.{u}} [HasExt.{w} (AbelianSheaf.{u, u + 1} X)]

/-- Killing is a theorem for every finite locally constant coefficient. -/
example (L : AbelianSheaf.{u, u + 1} X) (hL : IsFiniteLocallyConstant L)
    (c : H1Etale X L) :
    ∃ Y : Scheme.FiniteEtale X, Surjective Y.obj.hom ∧
      ∀ [HasExt.{w'} (AbelianSheaf.{u, u + 1} Y.obj.left)],
        h1Pullback Y.obj.hom L c = 0 :=
  exists_finiteEtale_h1Pullback_eq_zero hL c

/-- Connected Galois refinement is proved on the same original class. -/
example [ConnectedSpace X] (L : AbelianSheaf.{u, u + 1} X)
    (hL : IsFiniteLocallyConstant L) (c : H1Etale X L) :
    ∃ Y : Scheme.FiniteEtale X,
      PreGaloisCategory.IsGalois Y ∧ ConnectedSpace Y.obj.left ∧ Surjective Y.obj.hom ∧
      ∀ [HasExt.{w'} (AbelianSheaf.{u, u + 1} Y.obj.left)],
        h1Pullback Y.obj.hom L c = 0 :=
  exists_galois_finiteEtale_h1Pullback_eq_zero hL c

/-- The positive composite level is covered without a field assumption on the ring. -/
example (c : H1Etale X ((constantSheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}).obj
    (AddCommGrpCat.of (ULift.{u + 1} (ZMod 6))))) :
    ∃ Y : Scheme.FiniteEtale X, Surjective Y.obj.hom ∧
      ∀ [HasExt.{w'} (AbelianSheaf.{u, u + 1} Y.obj.left)],
        h1Pullback Y.obj.hom _ c = 0 :=
  exists_finiteEtale_cyclic_h1Pullback_eq_zero 6 c

/-- Level one uses the same theorem and original map. -/
example (c : H1Etale X ((constantSheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}).obj
    (AddCommGrpCat.of (ULift.{u + 1} (ZMod 1))))) :
    ∃ Y : Scheme.FiniteEtale X, Surjective Y.obj.hom ∧
      ∀ [HasExt.{w'} (AbelianSheaf.{u, u + 1} Y.obj.left)],
        h1Pullback Y.obj.hom _ c = 0 :=
  exists_finiteEtale_cyclic_h1Pullback_eq_zero 1 c

/-- info: 'AlgebraicGeometry.Scheme.EtaleCohomology.exists_finiteEtale_h1Pullback_eq_zero' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms AlgebraicGeometry.Scheme.EtaleCohomology.exists_finiteEtale_h1Pullback_eq_zero

/-- info: 'AlgebraicGeometry.Scheme.EtaleCohomology.exists_finiteEtale_cyclic_h1Pullback_eq_zero' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms AlgebraicGeometry.Scheme.EtaleCohomology.exists_finiteEtale_cyclic_h1Pullback_eq_zero

/-- info: 'AlgebraicGeometry.Scheme.EtaleCohomology.exists_galois_finiteEtale_h1Pullback_eq_zero' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms AlgebraicGeometry.Scheme.EtaleCohomology.exists_galois_finiteEtale_h1Pullback_eq_zero
