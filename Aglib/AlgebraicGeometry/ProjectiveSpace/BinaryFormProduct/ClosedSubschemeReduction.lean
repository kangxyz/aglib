/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.ProjectiveSpace.BinaryFormProduct.Finite
public import Aglib.AlgebraicGeometry.ProjectiveSpace.BinaryFormProduct.Surjective
public import Aglib.AlgebraicGeometry.ProjectiveSpace.Smooth
public import Aglib.AlgebraicGeometry.Morphisms.Smooth.Regularity
public import Aglib.AlgebraicGeometry.Stalk.Dimension
public import Aglib.AlgebraicGeometry.Dimension.Finite

/-! # Closed projective schemes covered by products of curves

Pull back the actual finite surjective binary-form multiplication along the
original projective embedding. The same cover is a closed subscheme of the
original native product of projective lines. Forgetting its first factor has
geometric fibres of dimension at most one: the product projection is smooth
of relative dimension one, and a finite map does not increase dimension.
These are actual maps and dimension proofs, not a supplied pencil packet.
No Noetherian, reducedness, field or characteristic assumption is imposed
on the original base. The zero-factor case is retained.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.ProjectiveSpace.BinaryFormProduct

variable (R : Type u) [CommRing R]

/-- Forget the first factor of the original native product. -/
abbrev tailProjection (n : ℕ) : source R (n + 1) ⟶ source R n :=
  (prod.snd : Over.mk (Scheme.ProjectiveLine.structureMap R) ⨯ product R n ⟶
    product R n).left

@[reassoc (attr := simp)]
theorem tailProjection_over (n : ℕ) :
    tailProjection R n ≫ structureMap R n = structureMap R (n + 1) :=
  (prod.snd : Over.mk (Scheme.ProjectiveLine.structureMap R) ⨯ product R n ⟶
    product R n).w

/-- The literal projective-line map has relative smooth dimension one over
an arbitrary original ring, through the existing coordinate comparison. -/
theorem line_smoothOfRelativeDimension :
    SmoothOfRelativeDimension 1 (Scheme.ProjectiveLine.structureMap R) := by
  have : SmoothOfRelativeDimension 1 (toSpec R (ULift.{u} (Fin 2))) :=
    toSpec_smoothOfRelativeDimension R (ULift.{u} (Fin 2)) 1 Equiv.ulift
  have h : SmoothOfRelativeDimension (0 + 1)
      ((finUliftIso R 2).hom ≫ toSpec R (ULift.{u} (Fin 2))) := inferInstance
  change SmoothOfRelativeDimension 1 (polynomialToSpec R (Fin 2))
  simpa only [Nat.zero_add, finUliftIso_hom_toSpec] using h

/-- Every original tail projection is a proper relative smooth curve. -/
instance tailProjection_smoothOfRelativeDimension (n : ℕ) :
    SmoothOfRelativeDimension 1 (tailProjection R n) := by
  let : MorphismProperty.IsStableUnderBaseChange
      (@SmoothOfRelativeDimension 1 : MorphismProperty Scheme.{u}) :=
    smoothOfRelativeDimension_isStableUnderBaseChange 1
  have := line_smoothOfRelativeDimension R
  change SmoothOfRelativeDimension 1
    (prod.snd : Over.mk (Scheme.ProjectiveLine.structureMap R) ⨯ product R n ⟶
      product R n).left
  rw [← Over.prodLeftIsoPullback_hom_snd]
  have : SmoothOfRelativeDimension 1
      (pullback.snd (Over.mk (Scheme.ProjectiveLine.structureMap R)).hom (product R n).hom) :=
    MorphismProperty.pullback_snd
      (P := (@SmoothOfRelativeDimension 1 : MorphismProperty Scheme.{u})) _ _
      (line_smoothOfRelativeDimension R)
  simpa only [Nat.zero_add] using
    (smoothOfRelativeDimension_comp 0 1
      ((Over.mk (Scheme.ProjectiveLine.structureMap R)).prodLeftIsoPullback (product R n)).hom
      (pullback.snd (Over.mk (Scheme.ProjectiveLine.structureMap R)).hom (product R n).hom))

instance tailProjection_isProper (n : ℕ) : IsProper (tailProjection R n) := by
  let : MorphismProperty.IsStableUnderBaseChange
      (@IsProper : MorphismProperty Scheme.{u}) := IsProper.isStableUnderBaseChange
  change IsProper
    (prod.snd : Over.mk (Scheme.ProjectiveLine.structureMap R) ⨯ product R n ⟶
      product R n).left
  rw [← Over.prodLeftIsoPullback_hom_snd]
  have : IsProper (Over.mk (Scheme.ProjectiveLine.structureMap R)).hom := by
    change IsProper (Scheme.ProjectiveLine.structureMap R)
    infer_instance
  have : IsProper
      (pullback.snd (Over.mk (Scheme.ProjectiveLine.structureMap R)).hom (product R n).hom) :=
    MorphismProperty.pullback_snd (P := (@IsProper : MorphismProperty Scheme.{u})) _ _ inferInstance
  infer_instance

/-- A finite source over the original product has curve-dimensional fibres
under the actual tail projection, even for empty or nonreduced fibres. -/
theorem finite_tailProjection_geometricFiber_dimension_le_one
    {Z : Scheme.{u}} (n : ℕ) (j : Z ⟶ source R (n + 1)) [IsFinite j]
    (K : Type u) [Field K] (η : Spec (.of K) ⟶ source R n) :
    topologicalKrullDim (pullback (j ≫ tailProjection R n) η : Scheme.{u}) ≤ 1 := by
  let : MorphismProperty.IsStableUnderBaseChange
      (@SmoothOfRelativeDimension 1 : MorphismProperty Scheme.{u}) :=
    smoothOfRelativeDimension_isStableUnderBaseChange 1
  let t := tailProjection R n
  let a : pullback (j ≫ t) η ⟶ pullback t η :=
    pullback.map _ _ _ _ j (𝟙 _) (𝟙 _) (by simp) (by simp)
  have ha : IsFinite a :=
    MorphismProperty.pullbackMap (P := @IsFinite) inferInstance inferInstance
      (by simp) (by simp)
  have : SmoothOfRelativeDimension 1 (pullback.snd t η) :=
    MorphismProperty.pullback_snd
      (P := (@SmoothOfRelativeDimension 1 : MorphismProperty Scheme.{u})) _ _ inferInstance
  apply (Scheme.Hom.topologicalKrullDim_le_of_isFinite a).trans
  rw [Scheme.topologicalKrullDim_eq_iSup_stalk]
  exact iSup_le (Scheme.smoothOfRelativeDimension_stalk_dimension_le
    K (pullback t η) (pullback.snd t η) 1)

/-- The actual binary-form pullback supplies a finite surjection onto any
original closed projective subscheme and a closed embedding into the same
native product. The base triangle is the original pullback equation. -/
theorem exists_finiteSurjective_closedProductCover
    {X : Scheme.{u}} (n : ℕ)
    (j : X ⟶ ProjectiveSpace R (ULift.{u} (Fin (n + 1)))) [IsClosedImmersion j] :
    ∃ (Z : Scheme.{u}) (p : Z ⟶ X) (i : Z ⟶ source R n),
      IsFinite p ∧ Surjective p ∧ IsClosedImmersion i ∧
      i ≫ structureMap R n = p ≫ j ≫ toSpec R (ULift.{u} (Fin (n + 1))) := by
  refine ⟨pullback (multiplication R n) j, pullback.snd _ _, pullback.fst _ _,
    inferInstance, inferInstance, inferInstance, ?_⟩
  rw [← multiplication_over R n, ← Category.assoc, pullback.condition,
    Category.assoc]

end AlgebraicGeometry.ProjectiveSpace.BinaryFormProduct
