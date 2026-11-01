/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Cohomology.StructureSheaf.KunnethOpenAffine

/-! Native original-map consumers with an arbitrary affine open in the unchanged ambient. -/

@[expose] public noncomputable section

open CategoryTheory MonoidalCategory CartesianMonoidalCategory AlgebraicGeometry TopologicalSpace
open AlgebraicGeometry.Scheme.OverField AlgebraicGeometry.Scheme.Cohomology
open scoped TensorProduct

attribute [local instance] Over.cartesianMonoidalCategory

universe u

variable {k : Type u} [Field k] (X Y : FScheme k)

example (U : Y.left.Opens) (n : ℕ)
    (x : Scheme.structureCohomology k X n) (y : structureOpenCohomology Y U 0) :
    moduleOpenUnitNormalize (X ⊗ Y).left ((snd X Y).left ⁻¹ᵁ U) n
        (structureExternalOpenTensor X Y U (Nat.add_zero n) (x ⊗ₜ[k] y)) =
      Sheaf.H.map
        (moduleScalarOfGlobal ((snd X Y).left ⁻¹ᵁ U).toScheme
          (SheafOfModules.unit ((snd X Y).left ⁻¹ᵁ U).toScheme.ringCatSheaf)
          (((snd X Y).left ∣_ U).appTop (structureOpenH0Equiv Y U y))) n
        (structureCohomologyPullback
          (((snd X Y).left ⁻¹ᵁ U).ι ≫ (fst X Y).left) n x) :=
  structureExternalOpenTensor_zero_right X Y U n x y

example (U : Y.left.Opens) (hU : IsAffineOpen U) (n : ℕ) :
    (fun z : Scheme.structureCohomology k X n ⊗[k] structureOpenCohomology Y U 0 =>
      structureOpenAffineTensorMap X Y U hU n (structureOpenAffineSourceEquiv X Y U n z)) =
      fun z => moduleOpenUnitNormalize (X ⊗ Y).left ((snd X Y).left ⁻¹ᵁ U) n
        (structureExternalOpenTensor X Y U (Nat.add_zero n) z) :=
  structureOpenAffineTensorMap_sourceEquiv X Y U hU n

variable [QuasiCompact X.hom] [QuasiSeparated X.hom]

example (U : Y.left.Opens) (hU : IsAffineOpen U) (n : ℕ) :
    Function.Bijective (structureExternalOpenTensor X Y U (Nat.add_zero n)) :=
  structureExternalOpenTensor_bijective_of_isAffineOpen X Y U hU n

example (U : Y.left.Opens) (hU : IsAffineOpen U) (n : ℕ) :
    Function.Bijective (structureOpenKunnethMap X Y U n) :=
  structureOpenKunnethMap_bijective_of_isAffineOpen X Y U hU n
