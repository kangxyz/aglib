/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Cohomology.Godement.Tensor

/-! # Literal Godement tensor-unit consumers

The original component, its genuine weak law under finite local freeness, and
its original lower-bound and termwise-flasque properties are retained.
-/
@[expose] public section
set_option warningAsError true
set_option autoImplicit false
set_option linter.mathlibStandardSet true
noncomputable section
universe u
open CategoryTheory AlgebraicGeometry
open AlgebraicGeometry.Scheme.Modules
open AlgebraicGeometry.Scheme.Modules.Godement
namespace AglibTest.ArchiveGodementTensor

/-- The original arrow has the same actual outer-total and tensor-unit component. -/
theorem original_component (X : Scheme.{u}) (E : X.Modules)
    (C : CochainComplex.Plus X.Modules) :
    @Eq
      (((godementTotalPlus X).obj ((moduleTensorLeftFunctor X E).mapCochainComplexPlus.obj C)) ⟶
        (godementTotalPlus X).obj ((moduleTensorLeftFunctor X E).mapCochainComplexPlus.obj
          ((godementTotalPlus X).obj C)))
      ((godementTensorTotalUnit X E).app C)
      ((godementTotalPlus X).map
        (X := (moduleTensorLeftFunctor X E).mapCochainComplexPlus.obj C)
        (Y := (moduleTensorLeftFunctor X E).mapCochainComplexPlus.obj
          ((godementTotalPlus X).obj C))
        ((moduleTensorLeftFunctor X E).mapCochainComplexPlus.map
          (X := C) (Y := (godementTotalPlus X).obj C)
          ((godementTotalPlusUnit X).app C))) :=
  godementTensorTotalUnit_app X E C

/-- Rewriting the literal component proves the original total arrow is weak. -/
theorem original_total_arrow_quasiIso {X : Scheme.{u}} (E : X.Modules)
    [IsFiniteLocallyFree X E] (C : CochainComplex.Plus X.Modules) :
    QuasiIso ((godementTensorTotalUnit X E).app C).hom := by
  rw [godementTensorTotalUnit_app]
  let := godementTensorUnit_quasiIso E C
  exact godementTotalPlus_map_quasiIso ((godementTensorUnit X E).app C)

/-- The actual total retains the specified bound and all original flasque terms. -/
theorem original_total_bound_and_flasque {X : Scheme.{u}}
    (C : CochainComplex.Plus X.Modules) (a : ℤ) [C.obj.IsStrictlyGE a] :
    ((godementTotalPlus X).obj C).obj.IsStrictlyGE a ∧
      ∀ n : ℤ, TopCat.Presheaf.IsFlasque (((godementTotalPlus X).obj C).obj.X n).presheaf :=
  ⟨godementTotalPlus_sameLowerBound C a, godementTotalPlus_termwiseFlasque C⟩

end AglibTest.ArchiveGodementTensor
