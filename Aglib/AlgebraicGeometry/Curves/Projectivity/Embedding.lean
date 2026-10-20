/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.ProjectiveSpace.FiniteEmbedding
public import Aglib.AlgebraicGeometry.Curves.Projectivity.FiniteMap

/-!
# Projective embeddings of the original proper curve

The actual finite map from the original normal integral proper curve to P1,
combined with the generic finite-cover embedding theorem, constructs a closed
immersion into standard finite polynomial projective space over the original
field. The exact `Properties` application derives all geometric hypotheses
from the existing native suppliers. No projectivity datum or new theorem family
is supplied to either construction.

This file proves the normal integral dimension-one case and its smooth-curve
application. The integral singular extension is being constructed separately.
No claim about arbitrary reducible or nonreduced proper curves, canonical-line
identification, trace duality, or numerical canonical degree follows here.
-/




@[expose] public section

noncomputable section
open AlgebraicGeometry.Scheme.ProjectiveLine.TwoChart
open AlgebraicGeometry.Scheme

open CategoryTheory AlgebraicGeometry
open _root_.AlgebraicGeometry.Scheme.OverField (FScheme)
open AlgebraicGeometry.Scheme.OverField.Curve

universe u

namespace AlgebraicGeometry.Scheme.OverField.Curve.Projectivity

variable {K : Type u} [Field K]

/-- Every normal integral proper dimension-one field scheme admits an actual
closed projective embedding commuting with its original structure morphism. -/
theorem exists_projectiveEmbedding_of_normal
    (X : FScheme K) [IsIntegral X.left] [IsProper X.hom]
    (hN : Scheme.NormalStalks X.left) (hdim : topologicalKrullDim X.left = 1) :
    ∃ (n : ℕ) (i : X.left ⟶ ProjectiveSpace K (ULift.{u} (Fin (n + 1)))),
      IsClosedImmersion i ∧
        i ≫ ProjectiveSpace.toSpec K (ULift.{u} (Fin (n + 1))) = X.hom := by
  obtain ⟨f, hf, _⟩ := exists_finite_dominant_map_to_nativeP1_of_normal X hN hdim
  have := hf
  obtain ⟨n, i, hi, hbase⟩ :=
    ProjectiveSpace.FiniteEmbedding.exists_closedImmersion_of_isFinite f.left
  exact ⟨n, i, hi, hbase.trans f.w⟩

/-- The existing smooth proper geometrically connected curve interface supplies
an actual closed embedding of the original curve, over its original field. -/
theorem curveProperties_exists_projectiveEmbedding
    {X : FScheme K} (hX : Properties X) :
    ∃ (n : ℕ) (i : X.left ⟶ ProjectiveSpace K (ULift.{u} (Fin (n + 1)))),
      IsClosedImmersion i ∧
        i ≫ ProjectiveSpace.toSpec K (ULift.{u} (Fin (n + 1))) = X.hom := by
  obtain ⟨f, hf, _⟩ := curveProperties_exists_finite_dominant_map_to_nativeP1 hX
  have := hf
  obtain ⟨n, i, hi, hbase⟩ :=
    ProjectiveSpace.FiniteEmbedding.exists_closedImmersion_of_isFinite f.left
  exact ⟨n, i, hi, hbase.trans f.w⟩

end AlgebraicGeometry.Scheme.OverField.Curve.Projectivity
