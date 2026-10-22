/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Cohomology.GrothendieckExistence.FormalModificationAdjunction
public import Aglib.AlgebraicGeometry.Cohomology.GrothendieckExistence.FormalPullbackCompletion
public import Aglib.AlgebraicGeometry.Cohomology.GrothendieckExistence.ProperAlgebraicComparison
public import Aglib.AlgebraicGeometry.Cohomology.GrothendieckExistence.FormalPullbackCompletionUnits

/-! # The original completion-to-pushforward comparison diagram

Completion of the coherent proper pushforward maps to the ambient pushforward
of the upstairs completion. This latter diagram is not asserted to be adic.
The comparison preserves the original quotient units, even though its stages
need not be injective or invertible.
-/

@[expose] public noncomputable section
open CategoryTheory Opposite
namespace AlgebraicGeometry.Scheme.Modules.Coherent
universe u
variable {A : Type u} [CommRing A] {X Y : Scheme.{u}}
  [IsLocallyNoetherian X] [IsLocallyNoetherian Y]
  (p : Y ⟶ X) [IsProper p] (f : X ⟶ Spec (CommRingCat.of A)) (I : Ideal A)
  (G : Y.CoherentSheaf)

/-- The actual degree-zero proper pushforward as a coherent sheaf. -/
def properPushforwardCoefficient : X.CoherentSheaf :=
  ⟨(pushforward p).obj G.obj, properPushforward_coherent p G.obj G.property⟩

/-- The actual counit, forgetting no coefficient map in the coherent category. -/
def properPushforwardCounit :
    (coherentPullback p).obj (properPushforwardCoefficient p G) ⟶ G :=
  ObjectProperty.homMk ((pullbackPushforwardAdjunction p).counit.app G.obj)

/-- Adjunction of a whole original unit-compatible diagram. All projections
and adjunction computations happen before geometric specialization. -/
def adjointDiagramComparison
    {C D : Type*} [Category C] [Category D]
    {L : C ⥤ D} {R : D ⥤ C} (adj : L ⊣ R)
    (N : D) (F : ℕᵒᵖ ⥤ C) (H V : ℕᵒᵖ ⥤ D)
    (u : ∀ n, R.obj N ⟶ F.obj (op n))
    (w : ∀ n, L.obj (R.obj N) ⟶ H.obj (op n))
    (v : ∀ n, N ⟶ V.obj (op n))
    (c : {e : F ⋙ L ≅ H // ∀ n, L.map (u n) ≫ e.hom.app (op n) = w n})
    (d : {ε : H ⟶ V // ∀ n, w n ≫ ε.app (op n) = adj.counit.app N ≫ v n}) :
    {ψ : F ⟶ V ⋙ R // ∀ n, u n ≫ ψ.app (op n) = R.map (v n)} := by
  refine ⟨((adj.whiskerRight ℕᵒᵖ).homEquiv F V) (c.val.hom ≫ d.val), ?_⟩
  intro n
  change u n ≫ (((adj.whiskerRight ℕᵒᵖ).unit.app F).app (op n) ≫
    R.map (c.val.hom.app (op n) ≫ d.val.app (op n))) = _
  rw [Adjunction.whiskerRight_unit_app_app]
  change u n ≫ adj.homEquiv _ _ (c.val.hom.app (op n) ≫ d.val.app (op n)) = _
  rw [← adj.homEquiv_naturality_left, ← Category.assoc, c.property n,
    d.property n, adj.homEquiv_naturality_right]
  have hε : adj.homEquiv _ _ (adj.counit.app N) = 𝟙 _ := by
    rw [← adj.homEquiv_symm_id]
    exact (adj.homEquiv _ _).apply_symm_apply _
  rw [hε, Category.id_comp]

/-- The original map on quotient towers, with its entire quotient-unit naturality certificate. -/
def quotientTowerMapComparison {Z : Scheme.{u}} (K : Z.IdealSheafData)
    {M N : Z.Modules} (a : M ⟶ N) :
    {ε : idealSheafQuotientTower Z K M ⟶ idealSheafQuotientTower Z K N //
      ∀ n, (idealSheafQuotientUnit Z (K ^ n)).app M ≫ ε.app (op n) =
        a ≫ (idealSheafQuotientUnit Z (K ^ n)).app N} :=
  ⟨idealSheafQuotientTowerHom Z K a,
    fun n => ((idealSheafQuotientUnit Z (K ^ n)).naturality a).symm⟩

/-- The proper pushforward tower comparison with all original quotient-unit equations. -/
def formalPushforwardComparisonData :
    {ψ : idealSheafQuotientTower X (idealThickeningIdealSheaf f I)
        ((pushforward p).obj G.obj) ⟶
      idealSheafQuotientTower Y (idealThickeningIdealSheaf (p ≫ f) I) G.obj ⋙ pushforward p //
      ∀ n, (idealSheafQuotientUnit X (idealThickeningIdealSheaf f I ^ n)).app
        ((pushforward p).obj G.obj) ≫ ψ.app (op n) =
          (pushforward p).map
            ((idealSheafQuotientUnit Y (idealThickeningIdealSheaf (p ≫ f) I ^ n)).app G.obj)} :=
  adjointDiagramComparison (pullbackPushforwardAdjunction p) G.obj
    (idealSheafQuotientTower X (idealThickeningIdealSheaf f I) ((pushforward p).obj G.obj))
    (idealSheafQuotientTower Y (idealThickeningIdealSheaf (p ≫ f) I)
      ((pullback p).obj ((pushforward p).obj G.obj)))
    (idealSheafQuotientTower Y (idealThickeningIdealSheaf (p ≫ f) I) G.obj)
    (fun n => (idealSheafQuotientUnit X (idealThickeningIdealSheaf f I ^ n)).app
      ((pushforward p).obj G.obj))
    (fun n => (idealSheafQuotientUnit Y (idealThickeningIdealSheaf (p ≫ f) I ^ n)).app
      ((pullback p).obj ((pushforward p).obj G.obj)))
    (fun n => (idealSheafQuotientUnit Y (idealThickeningIdealSheaf (p ≫ f) I ^ n)).app G.obj)
    (pullbackCompletionDiagramComparison p f I (properPushforwardCoefficient p G))
    (quotientTowerMapComparison (idealThickeningIdealSheaf (p ≫ f) I)
      ((pullbackPushforwardAdjunction p).counit.app G.obj))

/-- Original comparison into the ambient pushforward completion tower. -/
def formalPushforwardComparison :
    ((completionFunctor X (idealThickeningIdealSheaf f I)).obj
      (properPushforwardCoefficient p G)).obj ⟶
        ((completionFunctor Y (idealThickeningIdealSheaf (p ≫ f) I)).obj G).obj ⋙
          pushforward p :=
  (formalPushforwardComparisonData p f I G).val

/-- The bundled map is the literal original formal adjoint, not an isomorphic
replacement or a newly chosen stagewise map. -/
theorem formalPushforwardComparison_eq_adjoint :
    formalPushforwardComparison p f I G =
      formalModificationAdjoint p f I _ _
        ((baseIdealPullbackCompletionIso p f I (properPushforwardCoefficient p G)).hom ≫
          (completionFunctor Y (idealThickeningIdealSheaf (p ≫ f) I)).map
            (properPushforwardCounit p G)) := by
  unfold formalPushforwardComparison formalPushforwardComparisonData
  change ((pullbackPushforwardAdjunction p).whiskerRight ℕᵒᵖ).homEquiv _ _
    ((pullbackCompletionDiagramComparison p f I (properPushforwardCoefficient p G)).val.hom ≫
      idealSheafQuotientTowerHom Y (idealThickeningIdealSheaf (p ≫ f) I)
        ((pullbackPushforwardAdjunction p).counit.app G.obj)) = _
  rw [pullbackCompletionDiagramComparison_val]
  rfl

/-- The original quotient unit followed by the comparison is exactly
pushforward of the original upstairs quotient unit. -/
theorem formalPushforwardComparison_unit (n : ℕ) :
    (idealSheafQuotientUnit X (idealThickeningIdealSheaf f I ^ n)).app
        ((pushforward p).obj G.obj) ≫
      (formalPushforwardComparison p f I G).app (op n) =
        (pushforward p).map
          ((idealSheafQuotientUnit Y (idealThickeningIdealSheaf (p ≫ f) I ^ n)).app G.obj) :=
  (formalPushforwardComparisonData p f I G).property n

end AlgebraicGeometry.Scheme.Modules.Coherent
