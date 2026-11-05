/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Descent.FinitePresentation.FiniteTypeArrowBaseChangeLimit

/-! # Literal polynomial models of the simultaneous arithmetic-arrow total limit

The original polynomial Cartesian square identifies each literal stage with
the actual base-change limit diagram. Both projection equations are retained;
the original limiting polynomial scheme has the same reconstruction.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.Scheme.FiniteTypeArrowLimit.TargetBaseChange
universe u
open Algebra.FiniteTypeArrowLimit
variable {R A B : Type u} [CommRing R] [CommRing A] [CommRing B]
  [Algebra R A] [Algebra R B] (α : A →ₐ[R] B)

/-- Original polynomial stage, with its actual pullback reconstruction. -/
def polynomialStageIso (s : (Index A B)ᵒᵖ) :
    Spec (.of (Polynomial (targetStage α s.unop))) ≅
      (schemeDiagram α (PolynomialLaurent.polynomialProjection (.of R))).obj s :=
  (Pullback.Polynomial.polynomial_isPullback
    (CommRingCat.ofHom (algebraMap R (targetStage α s.unop)))).isoPullback

/-- The reconstruction preserves the literal coefficient projection. -/
theorem polynomialStageIso_hom_fst (s : (Index A B)ᵒᵖ) :
    (polynomialStageIso α s).hom ≫ pullback.fst
      (Spec.algebraMap R (targetStage α s.unop))
      (PolynomialLaurent.polynomialProjection (.of R)) =
        PolynomialLaurent.polynomialProjection (.of (targetStage α s.unop)) :=
  (Pullback.Polynomial.polynomial_isPullback
    (CommRingCat.ofHom (algebraMap R (targetStage α s.unop)))).isoPullback_hom_fst

/-- The reconstruction preserves the literal polynomial base map. -/
theorem polynomialStageIso_hom_snd (s : (Index A B)ᵒᵖ) :
    (polynomialStageIso α s).hom ≫ pullback.snd
      (Spec.algebraMap R (targetStage α s.unop))
      (PolynomialLaurent.polynomialProjection (.of R)) =
        Spec.map (CommRingCat.ofHom (Polynomial.mapRingHom
          (algebraMap R (targetStage α s.unop)))) :=
  (Pullback.Polynomial.polynomial_isPullback
    (CommRingCat.ofHom (algebraMap R (targetStage α s.unop)))).isoPullback_hom_snd

/-- The limit point is reconstructed from the original polynomial ring B[X]. -/
def polynomialLimitIso : Spec (.of (Polynomial B)) ≅
    (schemeCone α (PolynomialLaurent.polynomialProjection (.of R))).pt :=
  (Pullback.Polynomial.polynomial_isPullback
    (CommRingCat.ofHom (algebraMap R B))).isoPullback

end AlgebraicGeometry.Scheme.FiniteTypeArrowLimit.TargetBaseChange
