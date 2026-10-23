/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import
  Aglib.AlgebraicGeometry.EtaleCohomology.Finite.ExactImageComparison.GlobalEvaluationChart
public import Aglib.AlgebraicGeometry.EtaleCohomology.Finite.GeometricAffineChart

/-! # Global finite direct-image stalks with their original evaluation coordinates -/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Scheme.EtaleCohomology.Finite

universe u

open CoefficientStalkBaseChange
attribute [local instance] hasSheafifyLarge

variable {X S : Scheme.{u}} (f : X ⟶ S) [IsFinite f]
  {Ω : Type u} [Field Ω] [IsAlgClosed Ω]
  (s : Spec (.of Ω) ⟶ S) (F : AbelianSheaf.{u, u + 1} X)

/-- On any base scheme, the original direct-image evaluation map is an
isomorphism onto the tuple of stalks over the actual geometric fibre. -/
theorem finiteDirectImageEvaluationTuple_isIso : IsIso (directImageEvaluationTuple f s F) := by
  obtain ⟨i, φ, hφ⟩ := exists_affineOpenCover_point_factorization s
  let R : Type u := S.affineOpenCover.X i
  let ringR : CommRing R := inferInstanceAs (CommRing (S.affineOpenCover.X i))
  let alg : Algebra R Ω := φ.toAlgebra
  let g : Spec (.of R) ⟶ S := S.affineOpenCover.f i
  have hg : Etale g := inferInstanceAs (Etale (S.affineOpenCover.f i))
  exact @GeometricNeighborhood.finiteDirectImageEvaluationTuple_isIso_of_chart
    X S f inferInstance R Ω ringR inferInstance inferInstance alg g hg s hφ F

/-- The original finite stalk isomorphism uses actual geometric fibre points
and has exactly the original unit/counit evaluations as its coordinates. -/
def finiteDirectImageEvaluationIso :
    coefficientFiber s ((directImage f).obj F) ≅ directImageEvaluationTupleTarget f s F := by
  let := finiteDirectImageEvaluationTuple_isIso f s F
  exact asIso (directImageEvaluationTuple f s F)

@[simp] theorem finiteDirectImageEvaluationIso_hom :
    (finiteDirectImageEvaluationIso f s F).hom = directImageEvaluationTuple f s F := rfl

end AlgebraicGeometry.Scheme.EtaleCohomology.Finite
