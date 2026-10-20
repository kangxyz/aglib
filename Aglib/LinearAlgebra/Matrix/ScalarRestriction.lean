/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings
public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs
public import Mathlib.RingTheory.Norm.Defs

/-!
# Matrices of restricted scalar multiplication

Source: `lean/R5Lab/Aglib/LinearAlgebra/Matrix/ScalarRestriction.lean` at frozen R5
`f8a3314ddecffcada2ec721d26d56a937bed9690`, SHA-256
`72694e400410cfbbce2bae502cac9b319a802d489cedfe2f904d850c8caf7290`.
The chosen basis and actual field-algebra structure are explicit; no separability is assumed.
-/

@[expose] public section

noncomputable section
open CategoryTheory
namespace ModuleCat
universe u v

/-- Restricting a scalar automorphism of the one-dimensional M-space gives
multiplication by that same scalar on its underlying L-space. -/
theorem scalarRestriction_apply (L M : Type u) [Field L] [Field M]
    [Algebra L M] (a : M) (x : M) :
    ((ModuleCat.restrictScalars (algebraMap L M)).map
      (ModuleCat.ofHom (LinearMap.mul M M a))) x = a * x := rfl

end ModuleCat

namespace Matrix.GeneralLinearGroup
universe u v

/-- Multiplication matrices of units in the specified basis. -/
def restrictedScalarMatrix {L M : Type u} [Field L] [Field M] [Algebra L M]
    {ι : Type v} [Fintype ι] [DecidableEq ι] (b : Module.Basis ι L M) :
    Mˣ →* Matrix.GeneralLinearGroup ι L :=
  Units.map (Algebra.leftMulMatrix b).toRingHom.toMonoidHom

/-- The determinant of the actual restricted scalar matrix is the algebra norm. -/
theorem restrictedScalarMatrix_det {L M : Type u} [Field L] [Field M] [Algebra L M]
    {ι : Type v} [Fintype ι] [DecidableEq ι] (b : Module.Basis ι L M) (a : Mˣ) :
    Matrix.GeneralLinearGroup.det (restrictedScalarMatrix b a) =
      Units.map (Algebra.norm L) a := by
  apply Units.ext
  change Matrix.det (Algebra.leftMulMatrix b (a : M)) = Algebra.norm L (a : M)
  exact (Algebra.norm_eq_matrix_det b (a : M)).symm

end Matrix.GeneralLinearGroup
