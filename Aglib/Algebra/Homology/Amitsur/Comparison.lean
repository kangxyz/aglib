/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.Algebra.Homology.Amitsur.Coordinates
public import Aglib.Algebra.Homology.Amitsur.Split
public import Mathlib.Algebra.Category.ModuleCat.Abelian

/-!
# The actual scalar-extended module complex

The original algebraic contraction acts on the original coefficient module.
The canonical tensor associator identifies the resulting augmented complex
with the original native scalar extension of the original Amitsur complex.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory
open scoped Simplicial TensorProduct

namespace ModuleCat.Amitsur

universe u v

variable (R S : Type u) [CommRing R] [CommRing S] [Algebra R S]
variable (M : ModuleCat.{max u v} R)

/-- Apply the original coefficient-module functor to the actual split algebraic conerve. -/
def scalarModuleAugmented : CosimplicialObject.Augmented (ModuleCat.{max u v} R) :=
  (CosimplicialObject.Augmented.whiskeringObj _ _ (tensorModule R M)).obj
    (Algebra.Amitsur.scalarAugmented R S)

/-- The original coefficient-module functor preserves the actual native extra degeneracy. -/
def scalarModuleExtraDegeneracy : SimplicialObject.Augmented.ExtraDegeneracy
    (AlgebraicTopology.Amitsur.opAugmented (scalarModuleAugmented R S M)) :=
  (Algebra.Amitsur.scalarExtraDegeneracy R S).map (tensorModule R M).op

/-- The comparison uses the identity on the original augmented scalar module
and the original tensor associator in every later degree. -/
def scalarComplexIso :
    AlgebraicTopology.Amitsur.augmentedObj (scalarModuleAugmented R S M) ≅
      ((scalarTensorFunctor R S).mapHomologicalComplex (ComplexShape.up ℕ)).obj
        (augmentedComplex R S M) := by
  refine HomologicalComplex.Hom.isoOfComponents (fun i => match i with
    | 0 => Iso.refl _
    | n + 1 => (TensorProduct.assoc R S (Algebra.Amitsur.term R S n) M).toModuleIso) ?_
  intro i j hij
  have hij' : i + 1 = j := by simpa using hij
  subst j
  cases i with
  | zero =>
      apply ModuleCat.hom_ext
      apply TensorProduct.ext'
      intro s m
      rfl
  | succ n =>
      have hδ (i : Fin (n + 2)) :
          (TensorProduct.assoc R S (Algebra.Amitsur.term R S n) M).toModuleIso.hom ≫
            (scalarTensorFunctor R S).map ((cosimplicial R S M).δ i) =
          (scalarModuleAugmented R S M).right.δ i ≫
            (TensorProduct.assoc R S (Algebra.Amitsur.term R S (n + 1)) M).toModuleIso.hom := by
        apply ModuleCat.hom_ext
        apply TensorProduct.ext_threefold
        intro s a m
        rfl
      change (TensorProduct.assoc R S (Algebra.Amitsur.term R S n) M).toModuleIso.hom ≫
          (scalarTensorFunctor R S).map ((augmentedComplex R S M).d (n + 1) (n + 2)) =
        (AlgebraicTopology.Amitsur.augmentedObj (scalarModuleAugmented R S M)).d
          (n + 1) (n + 2) ≫
          (TensorProduct.assoc R S (Algebra.Amitsur.term R S (n + 1)) M).toModuleIso.hom
      rw [augmentedComplex_d_succ, AlgebraicTopology.Amitsur.augmentedObj_d_succ]
      simp only [Functor.map_sum, Functor.map_zsmul, Preadditive.comp_sum,
        Preadditive.sum_comp, Preadditive.comp_zsmul, Preadditive.zsmul_comp]
      apply Finset.sum_congr rfl
      intro i _
      exact congrArg (fun f => (-1 : ℤ) ^ (i : ℕ) • f) (hδ i)

/-- The actual native scalar extension is exact in every original degree,
through the actual leading-factor multiplication contraction. -/
theorem scalarTensor_augmentedComplex_exactAt (n : ℕ) :
    (((scalarTensorFunctor R S).mapHomologicalComplex (ComplexShape.up ℕ)).obj
      (augmentedComplex R S M)).ExactAt n :=
  (AlgebraicTopology.Amitsur.augmentedObj_exactAt_of_extraDegeneracy
    (scalarModuleAugmented R S M) (scalarModuleExtraDegeneracy R S M) n).of_iso
      (scalarComplexIso R S M)

end ModuleCat.Amitsur
