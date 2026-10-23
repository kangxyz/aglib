/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.Algebra.Homology.Amitsur.Augmented
public import Mathlib.AlgebraicTopology.ExtraDegeneracy
public import Mathlib.Algebra.Homology.Opposite

/-!
# All-degree exactness of the native split augmented coface complex

An actual native extra degeneracy on the opposite augmented object gives
an actual native null homotopy on the augmented complex. Homology vanishes
in every degree, including the original augmentation degree.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits Opposite
open scoped Simplicial

namespace AlgebraicTopology.Amitsur

universe v u

variable {C : Type u} [Category.{v} C] [Preadditive C]

theorem augmentedObj_op_d_zero_one (X : CosimplicialObject.Augmented C) :
    (augmentedObj X).op.d 1 0 = (X.hom.app ⦋0⦌).op := rfl

theorem augmentedObj_op_d_succ (X : CosimplicialObject.Augmented C) (n : ℕ) :
    (augmentedObj X).op.d (n + 2) (n + 1) =
      AlternatingFaceMapComplex.objD (opAugmented X).left n := by
  rw [HomologicalComplex.op_d, augmentedObj_d_succ]
  simp only [AlternatingFaceMapComplex.objD, op_sum, op_zsmul, opAugmented_δ]

/-- The original extra-degeneracy maps, shifted by the original augmentation. -/
def contractingHom (X : CosimplicialObject.Augmented C)
    (ed : SimplicialObject.Augmented.ExtraDegeneracy (opAugmented X)) :
    ∀ n : ℕ, (augmentedObj X).op.X n ⟶ (augmentedObj X).op.X (n + 1)
  | 0 => ed.s'
  | n + 1 => ed.s n

/-- The native augmented alternating complex is null homotopic through the
same original extra-degeneracy maps. -/
def nullHomotopy (X : CosimplicialObject.Augmented C)
    (ed : SimplicialObject.Augmented.ExtraDegeneracy (opAugmented X)) :
    Homotopy (𝟙 (augmentedObj X).op) 0 where
  hom i := Pi.single (i + 1) (contractingHom X ed i)
  zero i j hij := Pi.single_eq_of_ne (Ne.symm hij) _
  comm i := by
    cases i with
    | zero =>
        rw [Homotopy.prevD_chainComplex, Homotopy.dNext_zero_chainComplex]
        simp [contractingHom, ← opAugmented_hom_app, ed.s'_comp_ε]
        rfl
    | succ i =>
        cases i with
        | zero =>
            rw [Homotopy.prevD_chainComplex, Homotopy.dNext_succ_chainComplex]
            simp [contractingHom, augmentedObj_d_succ,
              Fin.sum_univ_two, Preadditive.comp_add,
              ← opAugmented_hom_app, ← opAugmented_δ,
              ed.s_comp_δ₀, ed.s₀_comp_δ₁]
            rfl
        | succ n =>
            rw [Homotopy.prevD_chainComplex, Homotopy.dNext_succ_chainComplex]
            simp [contractingHom, Nat.add_assoc, augmentedObj_d_succ,
              Fin.sum_univ_succ (n := n + 2), Preadditive.comp_sum,
              Preadditive.sum_comp, ← opAugmented_δ,
              ed.s_comp_δ₀, ed.s_comp_δ, pow_succ]
            rfl

variable {D : Type u} [Category.{v} D] [Abelian D]

/-- An actual native extra degeneracy makes the actual native augmented
cochain complex exact in every original degree. -/
theorem augmentedObj_exactAt_of_extraDegeneracy (X : CosimplicialObject.Augmented D)
    (ed : SimplicialObject.Augmented.ExtraDegeneracy (opAugmented X)) (n : ℕ) :
    (augmentedObj X).ExactAt n := by
  apply (HomologicalComplex.exactAt_op_iff (augmentedObj X)).mp
  apply ((augmentedObj X).op.exactAt_iff_isZero_homology n).mpr
  apply (IsZero.iff_id_eq_zero _).mpr
  simpa only [HomologicalComplex.homologyMap_id, HomologicalComplex.homologyMap_zero] using
    (nullHomotopy X ed).homologyMap_eq n

/-- Every homology object of the same original augmented complex vanishes. -/
theorem isZero_homology_augmentedObj_of_extraDegeneracy
    (X : CosimplicialObject.Augmented D)
    (ed : SimplicialObject.Augmented.ExtraDegeneracy (opAugmented X)) (n : ℕ) :
    IsZero ((augmentedObj X).homology n) :=
  (augmentedObj_exactAt_of_extraDegeneracy X ed n).isZero_homology

end AlgebraicTopology.Amitsur
