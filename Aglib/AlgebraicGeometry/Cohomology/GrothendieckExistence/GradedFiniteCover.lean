/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Cohomology.GrothendieckExistence.GradedLocalQuotient
public import Aglib.AlgebraicGeometry.Modules.QuasiCoherent.FiniteType.Pullback
public import Mathlib.AlgebraicGeometry.Noetherian

/-! # Finiteness of the actual graded geometry and its chart cover -/

@[expose] public noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

universe u
open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry.Scheme.Modules
open AlgebraicGeometry.Scheme.Modules.Coherent

namespace AlgebraicGeometry.Scheme.Cohomology

variable {A : Type u} [CommRing A] {X : Scheme.{u}}
  (f : X ⟶ Spec (CommRingCat.of A)) (I : Ideal A)

instance formalGradedSpace_isLocallyNoetherian [IsNoetherianRing A]
    [LocallyOfFiniteType f] : IsLocallyNoetherian (formalGradedSpace f I) :=
  inferInstanceAs (IsLocallyNoetherian
    (pullback f (Spec.map (CommRingCat.ofHom (R := A) (S := I.associatedGraded)
      (algebraMap A I.associatedGraded)))))

/-- The original degree-zero pullback is coherent on the graded base change. -/
theorem formalGradedAmbient_finite [IsLocallyNoetherian X]
    (F : AdicSystem X (idealThickeningIdealSheaf f I)) :
    QuasiCoherent.affineLocallyFiniteType _ (formalGradedAmbient f I F) :=
  QuasiCoherent.affineLocallyFiniteType_pullback (formalGradedProjection f I)
    (F.gradedPiece_coherent 0)

/-- A finite actual affine cover pulls back to the literal tensor charts. -/
theorem formalGradedCharts_cover {ι : Type u} (U : ι → X.affineOpens)
    (hU : ∀ x : X, ∃ i, x ∈ (U i).val) :
    ∀ y : formalGradedSpace f I, ∃ i, y ∈ (formalGradedChart f I (U i)).opensRange := by
  intro y
  obtain ⟨i, hi⟩ := hU (formalGradedProjection f I y)
  refine ⟨i, ?_⟩
  change y ∈ Set.range (formalGradedChart f I (U i))
  rw [formalGradedChart_range, (U i).property.range_fromSpec]
  exact hi

/-- The same finite affine opens cover the original base and their tensor charts
cover the graded base change. The base witness is retained for pushforward gluing. -/
theorem exists_formalGradedChartCover_with_base [CompactSpace X] :
    ∃ (ι : Type u) (_ : Finite ι) (U : ι → X.affineOpens),
      (∀ x : X, ∃ i, x ∈ (U i).val) ∧
      (∀ y : formalGradedSpace f I, ∃ i, y ∈ (formalGradedChart f I (U i)).opensRange) := by
  let V := X.affineCover.finiteSubcover
  let U : V.I₀ → X.affineOpens := fun i =>
    ⟨(V.f i).opensRange, by
      let : IsAffine (V.X i) := by
        change IsAffine (X.affineCover.X (X.affineCover.idx i.val))
        infer_instance
      exact isAffineOpen_opensRange (V.f i)⟩
  have hU : ∀ x : X, ∃ i, x ∈ (U i).val := by
    intro x
    obtain ⟨i, y, hy⟩ := V.exists_eq x
    exact ⟨i, ⟨y, hy⟩⟩
  exact ⟨V.I₀, inferInstance, U, hU, formalGradedCharts_cover f I U hU⟩

/-- Quasi-compactness supplies a finite cover by the actual tensor charts,
without choosing unrelated local affine spectra on the graded space. -/
theorem exists_formalGradedChartCover [CompactSpace X] :
    ∃ (ι : Type u) (_ : Finite ι) (U : ι → X.affineOpens),
      ∀ y : formalGradedSpace f I, ∃ i, y ∈ (formalGradedChart f I (U i)).opensRange := by
  obtain ⟨ι, hι, U, _, hU⟩ := exists_formalGradedChartCover_with_base f I
  exact ⟨ι, hι, U, hU⟩

end AlgebraicGeometry.Scheme.Cohomology
