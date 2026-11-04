/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Cohomology.Group.Coalgebra
public import Aglib.Algebra.Coalgebra.Multiplicativity
public import Aglib.AlgebraicGeometry.Cohomology.Proper.Field
public import Aglib.AlgebraicGeometry.Cohomology.Group.Vanishing

/-!
# The original coherent H1 dimension bound over every field

The actual multiplication pullback and original global Kunneth map supply
the native coalgebra laws. The accepted pure graded bound applies to these
operations, original proper finiteness and actual dimension vanishing.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true

open CategoryTheory MonoidalCategory CartesianMonoidalCategory AlgebraicGeometry
open AlgebraicGeometry.Scheme.OverField AlgebraicGeometry.Scheme.Cohomology
open scoped CategoryTheory.MonObj TensorProduct DirectSum

universe u

namespace AlgebraicGeometry.Scheme.Group

attribute [local instance] Over.cartesianMonoidalCategory

variable {k : Type u} [Field k] (G : FScheme k) [GrpObj G]
  [IsProper G.hom] [GeometricallyIntegral G.hom] [Smooth G.hom]

/-- Proper smooth geometrically integral groups satisfy the original coherent H1 bound.
No commutativity, perfectness, characteristic or extra theorem-family premise is required. -/
theorem finrank_structureH1_le_finrank_identityCotangent :
    Module.finrank k (structureCohomology k G 1) ≤
      Module.finrank k (Cotangent.Space η[G]) := by
  exact DirectSum.finrank_degreeOne_le_of_comul_grading
    (M := structureCohomology k G)
    (groupM := fun n => (inferInstance : AddCommGroup (structureCohomology k G n)))
    (moduleM := structureCohomologyModule G)
    (ringM := structureCohomologyGRing G) (algebraM := structureCohomologyGAlgebra G)
    (coalgebraM := structureCohomologyCoalgebra G)
    (finiteOne := properStructureCohomologyFinite k G 1 inferInstance)
    (t := fun z => structureExternalTensorSourceEquiv G G z)
    (structureCohomologyAugmentationLinear G) (structureCohomologyCoalgebra_counit G)
    (structureCohomology_proj_zero G) (structureCohomologyComul_one G)
    (structureCohomologyComul_multiplicative G) (fun _ => rfl)
    (structureCohomologyComul_degreeOne G)
    (Module.finrank k (Cotangent.Space η[G]))
    (fun n hn => structureCohomology_subsingleton_of_finrank_identityCotangent_lt G n hn)

end AlgebraicGeometry.Scheme.Group
