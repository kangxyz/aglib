/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.Finite.WholeSectionResidueMarks

/-! # Support of finite-model residue points through an affine chart

For any finite source map, every canonical residue point of its restriction
to the specified affine chart maps to the original chosen target point.
Consequently its whole image belongs to every set containing that point.
No section, Cartesian presentation of the finite map, open-immersion
hypothesis on the chart, or separable-closure hypothesis on the field is used.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Scheme.EtaleCohomology.Finite

open GeometricNeighborhood

universe u

variable (R Ω : Type u) [CommRing R] [Field Ω] [Algebra R Ω]
  {X X' : Scheme.{u}} (f : X' ⟶ X) [IsFinite f]
  (e : Spec (.of R) ⟶ X)

/-- The canonical residue mark retains the originally chosen target point,
after both projections from the actual affine restriction. -/
theorem finiteChartLimitResidueMap_basepoint
    (i : MaximalSpectrum (limitSourceRing R Ω (pullback.snd f e))) :
    ((limitResidueMap R Ω (pullback.snd f e) i ≫ pullback.fst f e) ≫ f)
      (IsLocalRing.closedPoint (IsLocalRing.ResidueField (Localization.AtPrime i.asIdeal))) =
        (Spec.algebraMap R Ω ≫ e) (IsLocalRing.closedPoint Ω) := by
  let z := limitResidueMap R Ω (pullback.snd f e) i
  have hproj : (z ≫ pullback.fst f e) ≫ f = (z ≫ pullback.snd f e) ≫ e :=
    (Category.assoc z (pullback.fst f e) f).trans
      ((congrArg (fun a : pullback f e ⟶ X => z ≫ a)
        (pullback.condition (f := f) (g := e))).trans
          (Category.assoc z (pullback.snd f e) e).symm)
  exact (congrArg (fun a :
    Spec (.of (IsLocalRing.ResidueField (Localization.AtPrime i.asIdeal))) ⟶ X =>
      a (IsLocalRing.closedPoint
        (IsLocalRing.ResidueField (Localization.AtPrime i.asIdeal)))) hproj).trans
    (congrArg e (limitResidueMap_basepoint R Ω (pullback.snd f e) i))

/-- Every set containing the original target point contains the whole image
of each canonical residue-field map. In particular, the set may be the image
of any specified morphism; it need not be a section or an open subset. -/
theorem finiteChartLimitResidueMap_range_subset
    (T : Set X) (hpoint : (Spec.algebraMap R Ω ≫ e) (IsLocalRing.closedPoint Ω) ∈ T)
    (i : MaximalSpectrum (limitSourceRing R Ω (pullback.snd f e))) :
    Set.range ((limitResidueMap R Ω (pullback.snd f e) i ≫ pullback.fst f e) ≫ f) ⊆ T := by
  rintro _ ⟨x, rfl⟩
  obtain rfl : x = IsLocalRing.closedPoint
      (IsLocalRing.ResidueField (Localization.AtPrime i.asIdeal)) := Subsingleton.elim _ _
  exact (finiteChartLimitResidueMap_basepoint R Ω f e i).symm ▸ hpoint

end AlgebraicGeometry.Scheme.EtaleCohomology.Finite
