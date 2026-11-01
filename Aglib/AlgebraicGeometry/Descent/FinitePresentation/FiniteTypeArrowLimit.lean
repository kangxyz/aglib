/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.RingTheory.FiniteType.ArrowSubalgebraColimit
public import Aglib.AlgebraicGeometry.Descent.FinitePresentation.FiniteTypeBaseChangeLimit
public import Aglib.AlgebraicGeometry.Limits.Polynomial
public import Aglib.AlgebraicGeometry.Spec.PolynomialLaurent.Basic

/-! # Original spectrum limits of simultaneous finite-type arrows

Both ends of an arbitrary algebra arrow use the same filtered index. The
cones and their commuting arrow are obtained from the actual inclusion
cocones, and the polynomial squares use the existing polynomial pushout.
No smooth-base-change, injective-coefficient or coefficient-colimit statement
is an input to these purely geometric constructions.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.Scheme.FiniteTypeArrowLimit

universe u

open Algebra.FiniteTypeArrowLimit

variable {R A B : Type u} [CommRing R] [CommRing A] [CommRing B]
  [Algebra R A] [Algebra R B] (α : A →ₐ[R] B)

local instance : Quiver (Index A B)ᵒᵖ :=
  (inferInstance : Category (Index A B)ᵒᵖ).toQuiver

def sourceSpecDiagram : (Index A B)ᵒᵖ ⥤ Scheme.{u} :=
  (sourceDiagram α).op ⋙ Scheme.Spec

def targetSpecDiagram : (Index A B)ᵒᵖ ⥤ Scheme.{u} :=
  (targetDiagram α).op ⋙ Scheme.Spec

def sourceSpecCone : Cone (sourceSpecDiagram α) :=
  Scheme.Spec.mapCone (sourceCocone α).op

def targetSpecCone : Cone (targetSpecDiagram α) :=
  Scheme.Spec.mapCone (targetCocone α).op

/-- The source spectrum is the limit of its actual finite-type stages. -/
def sourceSpecConeIsLimit : IsLimit (sourceSpecCone α) :=
  isLimitOfPreserves Scheme.Spec (sourceCoconeIsColimit α).op

/-- The target spectrum is the limit of its actual finite-type stages. -/
def targetSpecConeIsLimit : IsLimit (targetSpecCone α) :=
  isLimitOfPreserves Scheme.Spec (targetCoconeIsColimit α).op

/-- Spectra of the actual restrictions of the original arrow. -/
def specDiagramMap : targetSpecDiagram α ⟶ sourceSpecDiagram α :=
  Functor.whiskerRight (NatTrans.op (diagramMap α)) Scheme.Spec

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- Every stage triangle retains the original affine arrow. -/
@[reassoc]
theorem specDiagramMap_cone (s : (Index A B)ᵒᵖ) :
    (targetSpecCone α).π.app s ≫ (specDiagramMap α).app s =
      Spec.map (CommRingCat.ofHom α.toRingHom) ≫ (sourceSpecCone α).π.app s := by
  change Spec.map ((targetCocone α).ι.app s.unop) ≫
      Spec.map ((diagramMap α).app s.unop) =
    Spec.map (CommRingCat.ofHom α.toRingHom) ≫ Spec.map ((sourceCocone α).ι.app s.unop)
  rw [← Spec.map_comp, ← Spec.map_comp, diagramMap_cocone]

instance source_transition_isAffineHom {s t : (Index A B)ᵒᵖ} (g : s ⟶ t) :
    IsAffineHom ((sourceSpecDiagram α).map g) := by
  change IsAffineHom (Spec.map _)
  infer_instance

instance target_transition_isAffineHom {s t : (Index A B)ᵒᵖ} (g : s ⟶ t) :
    IsAffineHom ((targetSpecDiagram α).map g) := by
  change IsAffineHom (Spec.map _)
  infer_instance

/-- The original affine-line base-change square at a simultaneous finite-type stage. -/
theorem stage_polynomial_isPullback (s : Index A B) :
    IsPullback (PolynomialLaurent.polynomialProjection (.of (targetStage α s)))
      (Spec.map (CommRingCat.ofHom (Polynomial.mapRingHom (stageMap α s).toRingHom)))
      (Spec.map (CommRingCat.ofHom (stageMap α s).toRingHom))
      (PolynomialLaurent.polynomialProjection (.of (sourceStage α s))) :=
  Pullback.Polynomial.polynomial_isPullback (CommRingCat.ofHom (stageMap α s).toRingHom)

/-- The limiting polynomial square is the square of the unchanged original arrow. -/
theorem original_polynomial_isPullback :
    IsPullback (PolynomialLaurent.polynomialProjection (.of B))
      (Spec.map (CommRingCat.ofHom (Polynomial.mapRingHom α.toRingHom)))
      (Spec.map (CommRingCat.ofHom α.toRingHom))
      (PolynomialLaurent.polynomialProjection (.of A)) :=
  Pullback.Polynomial.polynomial_isPullback (CommRingCat.ofHom α.toRingHom)

/-- The source-stage polynomial square preserves the original inclusion projection. -/
theorem source_polynomial_projection_isPullback (s : Index A B) :
    IsPullback (PolynomialLaurent.polynomialProjection (.of A))
      (Spec.map (CommRingCat.ofHom
        (Polynomial.mapRingHom (sourceStage α s).val.toRingHom)))
      ((sourceSpecCone α).π.app (op s))
      (PolynomialLaurent.polynomialProjection (.of (sourceStage α s))) :=
  Pullback.Polynomial.polynomial_isPullback
    (CommRingCat.ofHom (sourceStage α s).val.toRingHom)

/-- The target-stage polynomial square preserves the original inclusion projection. -/
theorem target_polynomial_projection_isPullback (s : Index A B) :
    IsPullback (PolynomialLaurent.polynomialProjection (.of B))
      (Spec.map (CommRingCat.ofHom
        (Polynomial.mapRingHom (targetStage α s).val.toRingHom)))
      ((targetSpecCone α).π.app (op s))
      (PolynomialLaurent.polynomialProjection (.of (targetStage α s))) :=
  Pullback.Polynomial.polynomial_isPullback
    (CommRingCat.ofHom (targetStage α s).val.toRingHom)

end AlgebraicGeometry.Scheme.FiniteTypeArrowLimit
