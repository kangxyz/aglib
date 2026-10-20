/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Aglib.LinearAlgebra.Matrix.ScalarRestriction
public import Aglib.Algebra.Category.FGModuleCat.ScalarAutomorphisms
public import Aglib.Algebra.Category.FGModuleCat.RestrictScalars
public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs
public import Mathlib.LinearAlgebra.Pi

/-!
# Matrix automorphisms of finite modules and restriction of scalar multiplication in a chosen
basis of a finite field extension

No separability hypothesis is used.

Source: `lean/R5Lab/Aglib/Algebra/Category/FGModuleCat/ScalarMatrices.lean`
at frozen R5 `f8a3314ddecffcada2ec721d26d56a937bed9690`.
SHA-256: `c2695d6afaa751833b829fed30137a52651f3adbc81782b109ed6f50b4a52723`.
Native objects and canonical maps are reused; provenance does not select declaration namespaces.
-/

@[expose] public section

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Limits
open Matrix.GeneralLinearGroup
namespace FGModuleCat
universe u v w

/-- A linear automorphism is literally the corresponding finite-module isomorphism. -/
def linearAutToFGAut (R : Type u) [Ring R] (V : Type v) [AddCommGroup V]
    [Module R V] [Module.Finite R V] : (V ≃ₗ[R] V) →* Aut (FGModuleCat.of R V) where
  toFun e := e.toFGModuleCatIso
  map_one' := by apply Iso.ext; rfl
  map_mul' e f := by apply Iso.ext; rfl

/-- A matrix acts by its usual linear automorphism of the standard finite vector space. -/
def matrixToFGAut (L : Type u) [Field L] (n : ℕ) :
    Matrix.GeneralLinearGroup (Fin n) L →* Aut (FGModuleCat.of L (Fin n → L)) :=
  (linearAutToFGAut L (Fin n → L)).comp
    ((LinearMap.GeneralLinearGroup.generalLinearEquiv L (Fin n → L)).toMonoidHom.comp
      Matrix.GeneralLinearGroup.toLin.toMonoidHom)

/-- Exact entrywise action of the finite-module matrix automorphism. -/
theorem matrixToFGAut_apply (L : Type u) [Field L] (n : ℕ)
    (g : Matrix.GeneralLinearGroup (Fin n) L) (x : Fin n → L) :
    (matrixToFGAut L n g).hom x = (g : Matrix (Fin n) (Fin n) L).mulVec x :=
  Matrix.GeneralLinearGroup.toLin_apply g x

/-- The literal scalar automorphism on the one-dimensional M-module. -/
abbrev scalarFGAut (M : Type u) [Field M] (a : Mˣ) : Aut (FGModuleCat.of M M) :=
  scalarUnitAut (CommRingCat.of M) a

/-- Evaluation is the canonical identification of the standard rank-one space with M. -/
abbrev rankOneEquiv (M : Type u) [Field M] : (Fin 1 → M) ≃ₗ[M] M :=
  LinearEquiv.funUnique (Fin 1) M M

/-- Evaluation as an isomorphism of actual finite modules. -/
def rankOneIso (M : Type u) [Field M] : FGModuleCat.of M (Fin 1 → M) ≅ FGModuleCat.of M M :=
  (rankOneEquiv M).toFGModuleCatIso

/-- The scalar one-by-one matrix becomes literal multiplication by a. -/
theorem rankOne_scalar_square (M : Type u) [Field M] (a : Mˣ) :
    (matrixToFGAut M 1 (Matrix.GeneralLinearGroup.scalar (Fin 1) a)).hom ≫
        (rankOneIso M).hom =
      (rankOneIso M).hom ≫ (scalarFGAut M a).hom := by
  apply FGModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  change (matrixToFGAut M 1 (Matrix.GeneralLinearGroup.scalar (Fin 1) a)).hom x 0 =
    (a : M) * x 0
  rw [matrixToFGAut_apply]
  simp [Matrix.GeneralLinearGroup.scalar]

section Restriction
variable {L M : Type u} [Field L] [Field M] [Algebra L M] [FiniteDimensional L M]
  {d : ℕ} (b : Module.Basis (Fin d) L M)

/-- The genuine restriction functor used by the finite affine transfer. -/
abbrev restrictFG : FGModuleCat.{u} M ⥤ FGModuleCat.{u} L :=
  _root_.ModuleCat.FiniteRestrictionScalars.moduleRestriction (CommRingCat.ofHom (algebraMap L M))
    (RingHom.finite_algebraMap.mpr inferInstance)

/-- Coordinates on the actual restricted module, with its actual L-action. -/
def restrictionBasisEquiv :
    (restrictFG (L := L) (M := M)).obj (FGModuleCat.of M M) ≃ₗ[L] (Fin d → L) where
  toFun := b.equivFun
  invFun := b.equivFun.symm
  left_inv := b.equivFun.left_inv
  right_inv := b.equivFun.right_inv
  map_add' := b.equivFun.map_add
  map_smul' r x := by
    change M at x
    change b.equivFun (algebraMap L M r * x) = r • b.equivFun x
    rw [← Algebra.smul_def]
    exact b.equivFun.map_smul r x

/-- The basis isomorphism in the actual category used in the transfer square. -/
def restrictionBasisIso :
    (restrictFG (L := L) (M := M)).obj (FGModuleCat.of M M) ≅
      FGModuleCat.of L (Fin d → L) where
  hom := ConcreteCategory.ofHom (restrictionBasisEquiv b).toLinearMap
  inv := ConcreteCategory.ofHom (restrictionBasisEquiv b).symm.toLinearMap
  hom_inv_id := by
    apply FGModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    exact (restrictionBasisEquiv b).left_inv x
  inv_hom_id := by
    apply FGModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    exact (restrictionBasisEquiv b).right_inv x

/-- Restriction of the scalar automorphism is literally the multiplication matrix
in b, as a commuting square of actual finite-module maps. -/
theorem scalar_restriction_basis_square (a : Mˣ) :
    (restrictFG (L := L) (M := M)).map (scalarFGAut M a).hom ≫ (restrictionBasisIso b).hom =
      (restrictionBasisIso b).hom ≫ (matrixToFGAut L d (restrictedScalarMatrix b a)).hom := by
  apply FGModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  change M at x
  change b.equivFun ((a : M) * x) =
    (matrixToFGAut L d (restrictedScalarMatrix b a)).hom (b.equivFun x)
  rw [matrixToFGAut_apply]
  exact (Algebra.leftMulMatrix_mulVec_repr b (a : M) x).symm

/-- The same equality as literal conjugacy of the original automorphisms. -/
theorem scalar_restriction_conjugate (a : Mˣ) :
    Aut.autMulEquivOfIso (restrictionBasisIso b)
      ((restrictFG (L := L) (M := M)).mapAut _ (scalarFGAut M a)) =
        matrixToFGAut L d (restrictedScalarMatrix b a) := by
  apply Iso.ext
  change (restrictionBasisIso b).inv ≫
    ((restrictFG (L := L) (M := M)).map (scalarFGAut M a).hom ≫ (restrictionBasisIso b).hom) = _
  rw [scalar_restriction_basis_square]
  simp

/-- Canonical coordinates on the actual restriction of the standard rank-one M-space. -/
def scalarTransferBasisIso :
    (restrictFG (L := L) (M := M)).obj (FGModuleCat.of M (Fin 1 → M)) ≅
      FGModuleCat.of L (Fin d → L) :=
  (restrictFG (L := L) (M := M)).mapIso (rankOneIso M) ≪≫ restrictionBasisIso b

/-- The complete square for restricting a rank-one scalar matrix in the chosen basis. -/
theorem scalarTransfer_matrix_square (a : Mˣ) :
    (restrictFG (L := L) (M := M)).map
        (matrixToFGAut M 1 (Matrix.GeneralLinearGroup.scalar (Fin 1) a)).hom ≫
        (scalarTransferBasisIso b).hom =
      (scalarTransferBasisIso b).hom ≫
        (matrixToFGAut L d (restrictedScalarMatrix b a)).hom := by
  let F := restrictFG (L := L) (M := M)
  change F.map _ ≫ (F.map (rankOneIso M).hom ≫ (restrictionBasisIso b).hom) =
    (F.map (rankOneIso M).hom ≫ (restrictionBasisIso b).hom) ≫ _
  rw [← Category.assoc, ← F.map_comp, rankOne_scalar_square, F.map_comp,
    Category.assoc, scalar_restriction_basis_square, Category.assoc]

/-- Exact conjugacy of the restricted one-by-one matrix and the norm matrix. -/
theorem scalarTransfer_matrix_conjugate (a : Mˣ) :
    Aut.autMulEquivOfIso (scalarTransferBasisIso b)
      ((restrictFG (L := L) (M := M)).mapAut _
        (matrixToFGAut M 1 (Matrix.GeneralLinearGroup.scalar (Fin 1) a))) =
      matrixToFGAut L d (restrictedScalarMatrix b a) := by
  apply Iso.ext
  change (scalarTransferBasisIso b).inv ≫
    ((restrictFG (L := L) (M := M)).map
      (matrixToFGAut M 1 (Matrix.GeneralLinearGroup.scalar (Fin 1) a)).hom ≫
      (scalarTransferBasisIso b).hom) = _
  rw [scalarTransfer_matrix_square]
  simp

end Restriction
end FGModuleCat
