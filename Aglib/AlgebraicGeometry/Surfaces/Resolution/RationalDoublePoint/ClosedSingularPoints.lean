/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Surfaces.Resolution.RationalDoublePoint.FiniteSingularLocus
public import Aglib.AlgebraicGeometry.Surfaces.NormalPoints

/-!
# Actual closed singular points on normal surface models

Normal Noetherian local rings of dimension at most one are regular.
The original coheight bound makes every nonclosed point of a normal
surface regular. Singular points are therefore genuine closed points
with two-dimensional actual stalks, suitable as point-blowup centres.
-/

@[expose] public noncomputable section

open CategoryTheory TopologicalSpace

universe u

namespace AlgebraicGeometry.Scheme

/-- The singular set on the actual complete-base model is finite and closed;
each of its members is an eligible closed dimension-two point-blowup centre. -/
theorem finite_closed_singularSet_of_finiteType_complete_local
    (A : Type u) [CommRing A] [IsLocalRing A] [IsNoetherianRing A]
    [IsAdicComplete (IsLocalRing.maximalIdeal A) A]
    {X : Scheme.{u}} [IsIntegral X] [IsNoetherian X]
    (f : X ⟶ Spec (.of A)) [LocallyOfFiniteType f]
    (hdA : ringKrullDim A ≤ 2) (hX : NormalStalks X)
    (hdX : topologicalKrullDim X ≤ 2) :
    {x : X | ¬ IsRegularLocalRing (X.presheaf.stalk x)}.Finite ∧
      IsClosed {x : X | ¬ IsRegularLocalRing (X.presheaf.stalk x)} ∧
      ∀ x : X, ¬ IsRegularLocalRing (X.presheaf.stalk x) →
        IsClosed ({x} : Set X) ∧ ringKrullDim (X.presheaf.stalk x) = 2 := by
  let Z : Set X := {x | ¬ IsRegularLocalRing (X.presheaf.stalk x)}
  have hfin : Z.Finite := finite_singularSet_of_finiteType_complete_local A f hdA hX hdX
  have hpoint (x : X) (hx : x ∈ Z) : IsClosed ({x} : Set X) :=
    isClosed_singleton_of_singular_of_normal_dimension_le_two X hX hdX x hx
  have hclosed : IsClosed Z := by
    have he : (⋃ x ∈ Z, ({x} : Set X)) = Z := by
      ext x
      simp
    rw [← he]
    exact hfin.isClosed_biUnion hpoint
  refine ⟨hfin, hclosed, ?_⟩
  intro x hx
  exact ⟨hpoint x hx,
    stalk_dimension_eq_two_of_singular_of_normal_dimension_le_two X hX hdX x hx⟩

end AlgebraicGeometry.Scheme
