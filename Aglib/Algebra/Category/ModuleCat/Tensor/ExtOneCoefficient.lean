/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.Algebra.Homology.DerivedCategory.Ext.Cokernel
public import Mathlib.Algebra.Category.ModuleCat.Ext.Basic
public import Mathlib.Algebra.Homology.ShortComplex.ModuleCat
public import Mathlib.LinearAlgebra.Contraction
public import Mathlib.LinearAlgebra.TensorProduct.RightExactness

/-!
# Degree-one Ext and tensoring its coefficients

For a short exact sequence whose first two modules are finite projective,
right exactness of tensor products and the native tensor-Hom equivalence
identify `Ext¹(M,R) ⊗ N` with `Ext¹(M,N)`. The target N need not be flat,
projective, or finite. The proof uses the original connecting maps and
restriction maps and does not invoke derived tensor machinery.
-/

@[expose] public section

noncomputable section

universe u w

open CategoryTheory CategoryTheory.Abelian
open scoped TensorProduct

namespace ModuleCat

variable {R : Type u} [CommRing R] (N : ModuleCat.{u} R)

/-- The tensor-Hom equivalence on actual categorical Hom modules. -/
def homTensorCoefficientLinearEquiv (P : ModuleCat.{u} R)
    [Module.Finite R P] [Module.Projective R P] :
    ((P ⟶ ModuleCat.of R R) ⊗[R] N) ≃ₗ[R] (P ⟶ N) :=
  ((ModuleCat.homLinearEquiv (S := R) (M := P)
    (N := ModuleCat.of R R)).rTensor N).trans
    ((dualTensorHomEquiv R P N).trans
      (ModuleCat.homLinearEquiv (S := R) (M := P) (N := N)).symm)

/-- The tensor-Hom equivalence preserves the original restriction map. -/
theorem homTensorCoefficientLinearEquiv_comp {P Q : ModuleCat.{u} R}
    [Module.Finite R P] [Module.Projective R P]
    [Module.Finite R Q] [Module.Projective R Q] (f : P ⟶ Q) :
    (homTensorCoefficientLinearEquiv N P).toLinearMap.comp
        ((CategoryTheory.Linear.leftComp R (ModuleCat.of R R) f).rTensor N) =
      (CategoryTheory.Linear.leftComp R N f).comp
        (homTensorCoefficientLinearEquiv N Q).toLinearMap := by
  ext φ n p
  rfl

/-- Tensor-Hom comparison identifies the two concrete Hom cokernels. -/
def homCokernelTensorCoefficientLinearEquiv
    (S : ShortComplex (ModuleCat.{u} R))
    [Module.Finite R S.X₁] [Module.Projective R S.X₁]
    [Module.Finite R S.X₂] [Module.Projective R S.X₂] :
    (((S.X₁ ⟶ ModuleCat.of R R) ⊗[R] N) ⧸
      LinearMap.range ((CategoryTheory.Linear.leftComp R
        (ModuleCat.of R R) S.f).rTensor N)) ≃ₗ[R]
    ((S.X₁ ⟶ N) ⧸ LinearMap.range (CategoryTheory.Linear.leftComp R N S.f)) :=
  Submodule.Quotient.equiv _ _ (homTensorCoefficientLinearEquiv N S.X₁) (by
    rw [← LinearMap.range_comp]
    exact (congrArg LinearMap.range (homTensorCoefficientLinearEquiv_comp N S.f)).trans
      (LinearMap.range_comp_of_range_eq_top _
        (homTensorCoefficientLinearEquiv N S.X₂).range))

variable [HasExt.{w} (ModuleCat.{u} R)]

/-- An actual finite-projective length-one resolution identifies tensoring
`Ext¹(M,R)` with changing its second coefficient to any module N. -/
def extOneTensorCoefficientLinearEquiv
    {S : ShortComplex (ModuleCat.{u} R)} (hS : S.ShortExact)
    [Module.Finite R S.X₁] [Module.Projective R S.X₁]
    [Module.Finite R S.X₂] [Module.Projective R S.X₂] :
    (Ext.{w} S.X₃ (ModuleCat.of R R) 1 ⊗[R] N) ≃ₗ[R] Ext.{w} S.X₃ N 1 := by
  have hex : Function.Exact
      (CategoryTheory.Linear.leftComp R (ModuleCat.of R R) S.f)
      (hS.homConnectingLinearMap (R := R) (ModuleCat.of R R)) := by
    rw [LinearMap.exact_iff]
    exact hS.ker_homConnectingLinearMap (R := R) (ModuleCat.of R R)
  exact (_root_.rTensor.equiv N hex
    (hS.homConnectingLinearMap_surjective (R := R) (ModuleCat.of R R))).symm.trans
      ((homCokernelTensorCoefficientLinearEquiv N S).trans
        (hS.homCokernelExtOneLinearEquiv (R := R) N))

end ModuleCat
