/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.Continuity.SmoothAffineStageSystem
public import Aglib.AlgebraicGeometry.Descent.FinitePresentation.ArithmeticArrowPolynomialLimit
public import Aglib.AlgebraicGeometry.Spec.PolynomialLaurent.PolynomialTower

/-! # Actual simultaneous arrow systems for class reconstruction

Only geometric fields are constructed here. Apply
`SmoothAffineStageSystem.exists_stage_class` directly to this system; its
cohomology carriers stay at the system's original diagram and cone. Literal
projection equations below are independent of any cohomology dictionary.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits Opposite
namespace AlgebraicGeometry.Scheme.FiniteTypeArrowLimit.TargetBaseChange
universe u
open Algebra.FiniteTypeArrowLimit EtaleCohomology.Continuity
variable {R A B : Type u} [CommRing R] [CommRing A] [CommRing B]
  [Algebra R A] [Algebra R B] (α : A →ₐ[R] B)

/-- The quiver of the opposite finite-stage category. -/
local instance : Quiver (Index A B)ᵒᵖ :=
  (inferInstance : Category (Index A B)ᵒᵖ).toQuiver
/-- The quiver of the double-opposite finite-stage category. -/
local instance : Quiver ((Index A B)ᵒᵖ)ᵒᵖ :=
  (inferInstance : Category ((Index A B)ᵒᵖ)ᵒᵖ).toQuiver

/-- All geometric inputs are supplied by the original target-stage base changes. -/
def smoothStageSystem {X : Scheme.{u}} [IsAffine X]
    (p : X ⟶ Spec (.of R)) [Smooth p] :
    SmoothAffineStageSystem ((Index A B)ᵒᵖ)ᵒᵖ where
  diagram := (schemeDiagram α p).op
  cone := (schemeCone α p).op
  isColimit := (schemeConeIsLimit α p).op
  affine s := by
    change IsAffine ((schemeDiagram α p).obj s.unop)
    infer_instance
  affineMap g := by
    change IsAffineHom ((schemeDiagram α p).map g.unop)
    infer_instance
  base := Spec (.of B)
  projection := pullback.fst (Spec.algebraMap R B) p
  stageBase s := (targetSpecDiagram α).obj s.unop
  baseLeg s := (targetSpecCone α).π.app s.unop
  stageProjection s := pullback.fst
    (Spec.algebraMap R (targetStage α s.unop.unop)) p
  cartesian s := coefficientProjection_isPullback α p s.unop
  smooth s := coefficientProjection_smooth α p s.unop

/-- The polynomial instance needs no additional smoothness assumption. -/
def polynomialSmoothStageSystem : SmoothAffineStageSystem ((Index A B)ᵒᵖ)ᵒᵖ :=
  smoothStageSystem α (PolynomialLaurent.polynomialProjection (.of R))

/-- The base projection is the original pullback projection, not a replacement map. -/
theorem smoothStageSystem_projection {X : Scheme.{u}} [IsAffine X]
    (p : X ⟶ Spec (.of R)) [Smooth p] :
    (smoothStageSystem α p).projection = pullback.fst (Spec.algebraMap R B) p := rfl

/-- Each stage coefficient leg is the original target-spectrum cone leg. -/
theorem smoothStageSystem_baseLeg {X : Scheme.{u}} [IsAffine X]
    (p : X ⟶ Spec (.of R)) [Smooth p] (s : ((Index A B)ᵒᵖ)ᵒᵖ) :
    (smoothStageSystem α p).baseLeg s = (targetSpecCone α).π.app s.unop := rfl

/-- The original literal polynomial scheme identifies the system's actual limit point. -/
def polynomialSystemIso : Spec (.of (Polynomial B)) ≅
    (polynomialSmoothStageSystem α).cone.pt.unop :=
  polynomialLimitIso α

/-- The actual polynomial isomorphism respects the system's original coefficient map. -/
theorem polynomialSystemIso_projection :
    (polynomialSystemIso α).hom ≫ (polynomialSmoothStageSystem α).projection =
      PolynomialLaurent.polynomialProjection (.of B) :=
  (Pullback.Polynomial.polynomial_isPullback
    (CommRingCat.ofHom (algebraMap R B))).isoPullback_hom_fst

end AlgebraicGeometry.Scheme.FiniteTypeArrowLimit.TargetBaseChange
