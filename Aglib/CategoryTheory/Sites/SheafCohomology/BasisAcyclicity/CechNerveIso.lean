/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Mathlib.CategoryTheory.Whiskering
public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Products
public import Mathlib.AlgebraicTopology.CechNerve
public import Mathlib.AlgebraicTopology.AlternatingFaceMapComplex

/-! # Isomorphisms of actual product Čech nerves

An isomorphism of covering objects induces the original product isomorphisms
in every degree. Every simplex map and alternating differential is preserved.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

namespace CategoryTheory.Cech

universe u v a b

variable {C : Type u} [Category.{v} C] [HasFiniteProducts C]
  {X Y : C} (e : X ≅ Y)

/-- The literal product-nerve isomorphism induced by an isomorphism of objects. -/
def productNerveIso : cechNerveTerminalFrom X ≅ cechNerveTerminalFrom Y := by
  refine NatIso.ofComponents (fun n => Pi.mapIso fun _ : Fin (n.unop.len + 1) => e) ?_
  intro n m f
  apply Pi.hom_ext
  intro i
  simp [cechNerveTerminalFrom]

variable {A : Type a} [Category.{b} A] (P : Cᵒᵖ ⥤ A)

/-- Evaluation of the original product-nerve isomorphism on contravariant coefficients. -/
def productNerveCoefficientsIso :
    (cechNerveTerminalFrom X).rightOp ⋙ P ≅ (cechNerveTerminalFrom Y).rightOp ⋙ P := by
  let q := productNerveIso e
  let r : (cechNerveTerminalFrom X).rightOp ≅ (cechNerveTerminalFrom Y).rightOp :=
    { hom := q.inv.rightOp
      inv := q.hom.rightOp
      hom_inv_id := by rw [← NatTrans.rightOp_comp, Iso.hom_inv_id, NatTrans.rightOp_id]
      inv_hom_id := by rw [← NatTrans.rightOp_comp, Iso.inv_hom_id, NatTrans.rightOp_id] }
  exact Functor.isoWhiskerRight r P

variable [Preadditive A]

/-- The original alternating complexes agree after an isomorphism of covering objects. -/
def productNerveComplexIso :
    (AlgebraicTopology.alternatingCofaceMapComplex A).obj
      ((cechNerveTerminalFrom X).rightOp ⋙ P) ≅
    (AlgebraicTopology.alternatingCofaceMapComplex A).obj
      ((cechNerveTerminalFrom Y).rightOp ⋙ P) :=
  (AlgebraicTopology.alternatingCofaceMapComplex A).mapIso (productNerveCoefficientsIso e P)

section Change

variable {D : Type*} [Category D] [HasFiniteProducts D]
  (G : C ⥤ D) [PreservesFiniteProducts G] (Z : C)

/-- A finite-product-preserving functor carries the original product nerve to
that of the image, using its original product comparison maps. -/
def productNerveChangeIso :
    cechNerveTerminalFrom Z ⋙ G ≅ cechNerveTerminalFrom (G.obj Z) := by
  refine NatIso.ofComponents
    (fun n => PreservesProduct.iso G (fun _ : Fin (n.unop.len + 1) => Z)) ?_
  intro n m f
  apply Pi.hom_ext
  intro i
  simp [cechNerveTerminalFrom, PreservesProduct.iso_hom, Category.assoc]

/-- Evaluation of the native product-nerve change on original coefficients. -/
def productNerveChangeCoefficientsIso (Q : Dᵒᵖ ⥤ A) :
    (cechNerveTerminalFrom Z).rightOp ⋙ (G.op ⋙ Q) ≅
      (cechNerveTerminalFrom (G.obj Z)).rightOp ⋙ Q := by
  let q := productNerveChangeIso G Z
  let r : (cechNerveTerminalFrom Z ⋙ G).rightOp ≅
      (cechNerveTerminalFrom (G.obj Z)).rightOp :=
    { hom := q.inv.rightOp
      inv := q.hom.rightOp
      hom_inv_id := by rw [← NatTrans.rightOp_comp, Iso.hom_inv_id, NatTrans.rightOp_id]
      inv_hom_id := by rw [← NatTrans.rightOp_comp, Iso.inv_hom_id, NatTrans.rightOp_id] }
  exact Functor.isoWhiskerRight r Q

/-- Alternating complexes retain the original product comparisons and signs. -/
def productNerveChangeComplexIso (Q : Dᵒᵖ ⥤ A) :
    (AlgebraicTopology.alternatingCofaceMapComplex A).obj
      ((cechNerveTerminalFrom Z).rightOp ⋙ (G.op ⋙ Q)) ≅
    (AlgebraicTopology.alternatingCofaceMapComplex A).obj
      ((cechNerveTerminalFrom (G.obj Z)).rightOp ⋙ Q) :=
  (AlgebraicTopology.alternatingCofaceMapComplex A).mapIso
    (productNerveChangeCoefficientsIso G Z Q)

end Change

end CategoryTheory.Cech
