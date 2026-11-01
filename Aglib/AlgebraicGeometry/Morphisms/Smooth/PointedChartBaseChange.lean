/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Mathlib.AlgebraicGeometry.Pullbacks
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Mathlib.AlgebraicGeometry.Geometrically.Connected
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated

/-! # The original open-chart base-change inclusion

The native pullback map and symmetry insert an original source chart over an
original open base chart into the final base change. Its exact projections
and open-immersion property are retained without quasi-separatedness of the
ambient base. An actual open restriction is transported through its native
open image, retaining the original chosen point and structural properties.
-/

@[expose] public noncomputable section
open CategoryTheory Limits

namespace AlgebraicGeometry.Scheme
universe u

private theorem property_of_original_image_iso
    (P : MorphismProperty Scheme.{u}) [hP : P.IsStableUnderBaseChange]
    {A B T : Scheme.{u}} (qA : A ⟶ T) (qB : B ⟶ T) (e : A ≅ B)
    (h : e.hom ≫ qB = qA) (hq : P qA) : P qB := by
  have hr : e.inv ≫ qA = qB := by
    rw [← h, ← Category.assoc, e.inv_hom_id, Category.id_comp]
  have H : IsPullback e.inv qB qA (𝟙 T) :=
    IsPullback.of_horiz_isIso ⟨hr.trans (Category.comp_id qB).symm⟩
  exact hP.of_isPullback H hq

variable {X S U V T : Scheme.{u}} (f : X ⟶ S) (f₀ : U ⟶ V)
  (i : U ⟶ X) (j : V ⟶ S) (h : f₀ ≫ j = i ≫ f) (c : T ⟶ V)

/-- The original chart inclusion into the final base change, in base-first
orientation, uses only the native pullback map and native symmetry. -/
def pointedChartBaseChangeMap : pullback f₀ c ⟶ pullback (c ≫ j) f :=
  pullback.map f₀ c f (c ≫ j) i (𝟙 T) j h (by rw [Category.id_comp]) ≫
    (pullbackSymmetry f (c ≫ j)).hom

@[reassoc]
lemma pointedChartBaseChangeMap_fst :
    pointedChartBaseChangeMap f f₀ i j h c ≫ pullback.fst (c ≫ j) f =
      pullback.snd f₀ c := by
  rw [pointedChartBaseChangeMap, Category.assoc, pullbackSymmetry_hom_comp_fst]
  exact (pullback.lift_snd _ _ _).trans (Category.comp_id _)

@[reassoc]
lemma pointedChartBaseChangeMap_snd :
    pointedChartBaseChangeMap f f₀ i j h c ≫ pullback.snd (c ≫ j) f =
      pullback.fst f₀ c ≫ i := by
  rw [pointedChartBaseChangeMap, Category.assoc, pullbackSymmetry_hom_comp_snd]
  exact pullback.lift_fst _ _ _

instance [IsOpenImmersion i] [IsOpenImmersion j] :
    IsOpenImmersion (pointedChartBaseChangeMap f f₀ i j h c) := by
  dsimp [pointedChartBaseChangeMap]
  infer_instance

/-- The actual open image of a proven chart restriction retains all original
structural properties and the same prescribed point. This is only transport:
the section-component construction supplies the restriction in applications. -/
theorem exists_pointedChart_open_image [IsOpenImmersion i] [IsOpenImmersion j]
    (A : (pullback f₀ c : Scheme.{u}).Opens) (n : ℕ)
    [SmoothOfRelativeDimension n (A.ι ≫ pullback.snd f₀ c)]
    [QuasiCompact (A.ι ≫ pullback.snd f₀ c)]
    [QuasiSeparated (A.ι ≫ pullback.snd f₀ c)]
    [GeometricallyConnected (A.ι ≫ pullback.snd f₀ c)]
    (a : A.toScheme) (x : X) (hx : (A.ι ≫ pullback.fst f₀ c ≫ i) a = x) :
    ∃ (W : (pullback (c ≫ j) f : Scheme.{u}).Opens) (w : W.toScheme)
      (e : A.toScheme ≅ W.toScheme),
      e.hom ≫ W.ι = A.ι ≫ pointedChartBaseChangeMap f f₀ i j h c ∧
      (W.ι ≫ pullback.snd (c ≫ j) f) w = x ∧
      SmoothOfRelativeDimension n (W.ι ≫ pullback.fst (c ≫ j) f) ∧
      QuasiCompact (W.ι ≫ pullback.fst (c ≫ j) f) ∧
      QuasiSeparated (W.ι ≫ pullback.fst (c ≫ j) f) ∧
      GeometricallyConnected (W.ι ≫ pullback.fst (c ≫ j) f) := by
  let α := pointedChartBaseChangeMap f f₀ i j h c
  let m := A.ι ≫ α
  let W := m.opensRange
  let e : A.toScheme ≅ W.toScheme := m.isoOpensRange
  have he : e.hom ≫ W.ι = A.ι ≫ α := m.isoOpensRange_hom_ι
  have heq : e.hom ≫ (W.ι ≫ pullback.fst (c ≫ j) f) = A.ι ≫ pullback.snd f₀ c := by
    rw [← Category.assoc, he, Category.assoc, pointedChartBaseChangeMap_fst]
  have heX : e.hom ≫ (W.ι ≫ pullback.snd (c ≫ j) f) =
      A.ι ≫ pullback.fst f₀ c ≫ i := by
    rw [← Category.assoc, he, Category.assoc, pointedChartBaseChangeMap_snd]
  have hp : (W.ι ≫ pullback.snd (c ≫ j) f) (e.hom a) = x := by
    exact (congrArg (fun z : A.toScheme ⟶ X => z a) heX).trans hx
  let : MorphismProperty.IsStableUnderBaseChange
      (@SmoothOfRelativeDimension n : MorphismProperty Scheme.{u}) :=
    smoothOfRelativeDimension_isStableUnderBaseChange n
  let : MorphismProperty.IsStableUnderBaseChange
      (@QuasiCompact : MorphismProperty Scheme.{u}) := quasiCompact_isStableUnderBaseChange
  let : MorphismProperty.IsStableUnderBaseChange
      (@QuasiSeparated : MorphismProperty Scheme.{u}) := quasiSeparated_isStableUnderBaseChange
  let : MorphismProperty.IsStableUnderBaseChange
      (@GeometricallyConnected : MorphismProperty Scheme.{u}) := inferInstance
  refine ⟨W, e.hom a, e, he, hp, ?_, ?_, ?_, ?_⟩
  · exact property_of_original_image_iso
      (@SmoothOfRelativeDimension n : MorphismProperty Scheme.{u})
      _ _ e heq inferInstance
  · exact property_of_original_image_iso (@QuasiCompact : MorphismProperty Scheme.{u})
      _ _ e heq inferInstance
  · exact property_of_original_image_iso (@QuasiSeparated : MorphismProperty Scheme.{u})
      _ _ e heq inferInstance
  · exact property_of_original_image_iso (@GeometricallyConnected : MorphismProperty Scheme.{u})
      _ _ e heq inferInstance

end AlgebraicGeometry.Scheme
