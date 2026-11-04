/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Aglib.AlgebraicGeometry.Group.CartierDuality.SpecUnits

/-!
# Products of original represented unit maps

The whole Cartesian product law is proved before specializing it to native
Spec. Its only input is an arbitrary commutative algebra and a unit.
-/

@[expose] public section

noncomputable section

open CategoryTheory AlgebraicGeometry Opposite
open MonoidalCategory CartesianMonoidalCategory MonObj
open scoped TensorProduct CategoryTheory.MonObj

namespace AlgebraicGeometry.Scheme.Group.CartierDuality

universe u

private theorem comp_tensorHom_mul {C : Type*} [Category C] [CartesianMonoidalCategory C]
    {P X Y M : C} [MonObj M] (p : P ⟶ X ⊗ Y) (f : X ⟶ M) (g : Y ⟶ M) :
    p ≫ (f ⊗ₘ g) ≫ μ[M] = (p ≫ fst X Y ≫ f) * (p ≫ snd X Y ≫ g) := by
  rw [MonObj.mul_eq_mul, MonObj.comp_mul, MonObj.comp_mul, tensorHom_fst, tensorHom_snd]

variable {k : Type u} [CommRing k]

local instance instBraidedAlgSpecUnitsTensor :
    (AlgebraicGeometry.algSpec (CommRingCat.of k)).Braided :=
  AlgebraicGeometry.braidedAlgSpec

local instance instCommGrpObjSpecUnitsTensor :
    CommGrpObj (MultiplicativeGroup.scheme (Spec (CommRingCat.of k))) :=
  MultiplicativeGroup.commGroup _

/-- The product of two represented unit maps uses the two original tensor inclusions. -/
theorem specUnitMap_tensor_coordinates (A : CommAlgCat.{u} k) (u : Aˣ) :
    (algSpecTensorIso A A).inv ≫ (specUnitMap A u ⊗ₘ specUnitMap A u) ≫
        μ[MultiplicativeGroup.scheme (Spec (CommRingCat.of k))] =
      specUnitMap (A ⊗ A)
        (Units.map (Algebra.TensorProduct.includeLeft : A →ₐ[k] A ⊗[k] A).toMonoidHom u *
          Units.map (Algebra.TensorProduct.includeRight : A →ₐ[k] A ⊗[k] A).toMonoidHom u) := by
  rw [comp_tensorHom_mul]
  change
    ((Functor.OplaxMonoidal.δ (AlgebraicGeometry.algSpec (CommRingCat.of k))
          (op (A)) (op (A))) ≫ fst _ _ ≫ specUnitMap A u) *
      ((Functor.OplaxMonoidal.δ (AlgebraicGeometry.algSpec (CommRingCat.of k))
          (op (A)) (op (A))) ≫ snd _ _ ≫ specUnitMap A u) = _
  rw [Functor.OplaxMonoidal.δ_fst_assoc, Functor.OplaxMonoidal.δ_snd_assoc]
  have hl := specUnitMap_naturality (fst (op A) (op A)).unop u
  have hr := specUnitMap_naturality (snd (op A) (op A)).unop u
  have hm := specUnitMap_mul (op A ⊗ op A).unop
    (Units.map (fst (op A) (op A)).unop.hom.toMonoidHom u)
    (Units.map (snd (op A) (op A)).unop.hom.toMonoidHom u)
  have h := (congrArg₂ (· * ·) hl hr).trans hm.symm
  simp only [Quiver.Hom.op_unop, Opposite.unop_op,
    CommAlgCat.fst_unop_hom, CommAlgCat.snd_unop_hom] at h
  exact h

end AlgebraicGeometry.Scheme.Group.CartierDuality
