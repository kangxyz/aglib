/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.RingTheory.DiscreteValuationRing.GenericTensorResidue
public import Aglib.RingTheory.DiscreteValuationRing.GenericRetainedMatrix
public import Aglib.RingTheory.Extension.Generators.LinearChange

/-! # The actual generic source generators

The source point uses `B ⊗[R] R₁`, whereas native generator base change uses
`R₁ ⊗[R] B`. The native right-linear commutation equivalence resolves this
orientation once. Linear change then uses exactly the matrix whose entries are
the actual coefficient variables; its values are the already proved residue
coordinate lifts, not a separately chosen family.
-/

@[expose] public noncomputable section

open scoped TensorProduct

namespace GenericParameterCentre

attribute [local instance] Algebra.TensorProduct.rightAlgebra

variable (R : Type*) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
  {B : Type*} [CommRing B] [Algebra R B]
  {n : Type*} [Fintype n] [DecidableEq n]
  (p : R) [Fact (Irreducible p)]

local notation "R₁" => ParameterLocalization.Ring R (n × n) p

/-- Original generators on the literal source tensor ring, over its right scalar ring. -/
def tensorGenerators (P : Algebra.Generators R B n) :
    Algebra.Generators R₁ (B ⊗[R] R₁) n :=
  (P.baseChange R₁).ofAlgEquiv (Algebra.TensorProduct.commRight R R₁ B)

omit [Fintype n] [DecidableEq n] in
@[simp] theorem tensorGenerators_val (P : Algebra.Generators R B n) (i : n) :
    (tensorGenerators R p P).val i =
      (Algebra.TensorProduct.includeLeft : B →ₐ[R] B ⊗[R] R₁) (P.val i) := by
  simp only [tensorGenerators, Algebra.Generators.ofAlgEquiv_val,
    Function.comp_apply, Algebra.Generators.baseChange_val,
    Algebra.TensorProduct.commRight_tmul]
  rfl

/-- Apply the actual invertible generic matrix, without changing the source or scalar action. -/
def genericGenerators (P : Algebra.Generators R B n) :
    Algebra.Generators R₁ (B ⊗[R] R₁) n :=
  (tensorGenerators R p P).linearChange (ParameterLocalization.genericMatrix R n p)
    (ParameterLocalization.isUnit_det_genericMatrix R n p)

/-- These generator values are literally the lifts whose tensor residues were computed. -/
theorem genericGenerators_val (P : Algebra.Generators R B n) (i : n) :
    (genericGenerators R p P).val i = liftedCoordinate R p P.val i := by
  simp only [genericGenerators, Algebra.Generators.linearChange_val,
    Algebra.Generators.linearCoordinates, Matrix.mulVec, dotProduct,
    RingHom.mapMatrix_apply, Matrix.map_apply, tensorGenerators_val]
  rfl

end GenericParameterCentre
