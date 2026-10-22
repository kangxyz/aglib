/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Cohomology.GrothendieckExistence.FormalPullbackCompletion
public import Aglib.AlgebraicGeometry.Modules.Coherent.AdicSystem.UnitComparisons

/-! # Whole original completion comparisons and structural-index transport -/

@[expose] public noncomputable section
open CategoryTheory Opposite
namespace AlgebraicGeometry.Scheme.Modules.Coherent
universe u
variable {A : Type u} [CommRing A] {X Y : Scheme.{u}}
  [IsLocallyNoetherian X] [IsLocallyNoetherian Y]
  (p : Y ⟶ X) (f : X ⟶ Spec (CommRingCat.of A)) (I : Ideal A)

/-- The whole pullback comparison, together with all original quotient-unit equations. -/
def pullbackCompletionDiagramComparison (M : X.CoherentSheaf) :
    {e : idealSheafQuotientTower X (idealThickeningIdealSheaf f I) M.obj ⋙ pullback p ≅
      idealSheafQuotientTower Y (idealThickeningIdealSheaf (p ≫ f) I)
        ((pullback p).obj M.obj) //
      ∀ n, (pullback p).map
        ((idealSheafQuotientUnit X (idealThickeningIdealSheaf f I ^ n)).app M.obj) ≫
        e.hom.app (op n) =
          (idealSheafQuotientUnit Y (idealThickeningIdealSheaf (p ≫ f) I ^ n)).app
            ((pullback p).obj M.obj)} := by
  let : M.obj.IsQuasicoherent :=
    QuasiCoherent.quasicoherent_of_affineCharts _ (fun B j _ => (M.property B j).1)
  exact diagramComparisonOfComponents
    (idealSheafQuotientTower X (idealThickeningIdealSheaf f I) M.obj ⋙ pullback p)
    (idealSheafQuotientTower Y (idealThickeningIdealSheaf (p ≫ f) I)
      ((pullback p).obj M.obj)) ((pullback p).obj M.obj)
    (fun n => (pullback p).map
      ((idealSheafQuotientUnit X (idealThickeningIdealSheaf f I ^ n)).app M.obj))
    (fun n => (idealSheafQuotientUnit Y (idealThickeningIdealSheaf (p ≫ f) I ^ n)).app
      ((pullback p).obj M.obj))
    (fun n => baseIdealPullbackQuotientComparison p f I M.obj n)
    (fun a => baseIdealPullbackQuotientIso_transition p f I M (leOfHom a.unop))

omit [IsLocallyNoetherian Y] in
theorem pullbackCompletionDiagramComparison_val (M : X.CoherentSheaf) :
    (pullbackCompletionDiagramComparison p f I M).val =
      baseIdealPullbackCompletionDiagramIso p f I M := by
  let : M.obj.IsQuasicoherent :=
    QuasiCoherent.quasicoherent_of_affineCharts _ (fun B j _ => (M.property B j).1)
  exact diagramComparisonOfComponents_val
    (idealSheafQuotientTower X (idealThickeningIdealSheaf f I) M.obj ⋙ pullback p)
    (idealSheafQuotientTower Y (idealThickeningIdealSheaf (p ≫ f) I)
      ((pullback p).obj M.obj)) ((pullback p).obj M.obj)
    (fun n => (pullback p).map
      ((idealSheafQuotientUnit X (idealThickeningIdealSheaf f I ^ n)).app M.obj))
    (fun n => (idealSheafQuotientUnit Y (idealThickeningIdealSheaf (p ≫ f) I ^ n)).app
      ((pullback p).obj M.obj))
    (fun n => baseIdealPullbackQuotientComparison p f I M.obj n)
    (fun a => baseIdealPullbackQuotientIso_transition p f I M (leOfHom a.unop))

/-- Transport the whole original diagram and unit certificate together. -/
def transportDiagramUnitComparison {C : Type*} [Category C] {T : Type*}
    (Q : T → ℕᵒᵖ ⥤ C) (F : ℕᵒᵖ ⥤ C) (U : C)
    (a : ∀ n, U ⟶ F.obj (op n)) (η : ∀ t n, U ⟶ (Q t).obj (op n))
    {k l : T} (h : k = l)
    (c : {e : F ≅ Q k // ∀ n, a n ≫ e.hom.app (op n) = η k n}) :
    {e : F ≅ Q l // ∀ n, a n ≫ e.hom.app (op n) = η l n} := by
  refine ⟨c.val ≪≫ eqToIso (congrArg Q h), ?_⟩
  subst l
  intro n
  change a n ≫ (c.val.hom.app (op n) ≫ 𝟙 _) = η k n
  rw [Category.comp_id]
  exact c.property n

/-- Lift the whole original raw iso and its certificate before specializing geometry. -/
def formalIsoComparisonOfDiagram {C : Type*} [Category C]
    (P : ObjectProperty C) (F G : P.FullSubcategory)
    (q : (F.obj ⟶ G.obj) → Prop) (c : {e : F.obj ≅ G.obj // q e.hom}) :
    {e : F ≅ G // q e.hom.hom} :=
  ⟨ObjectProperty.isoMk _ c.val, c.property⟩

/-- Native base-change assembly with the original stage certificate.
Stage agreement follows from the original epimorphic units, never injectivity. -/
def originalModificationDiagramComparison
    {C D C' D' : Type*} [Category C] [Category D] [Category C'] [Category D']
    (F : ℕᵒᵖ ⥤ C) (P : C ⥤ D) (T : C ⥤ C') (H : D ⥤ D') (S : C' ⥤ D')
    (sq : T ⋙ S ≅ P ⋙ H) (V : ℕᵒᵖ ⥤ D) (β : F ⋙ P ≅ V)
    (W : ℕᵒᵖ ⥤ D') (U : D')
    (a : ∀ n, U ⟶ H.obj (V.obj (op n))) (b : ∀ n, U ⟶ W.obj (op n))
    (c : {e : V ⋙ H ≅ W // ∀ n, a n ≫ e.hom.app (op n) = b n})
    (d : ∀ n, {e : H.obj (V.obj (op n)) ≅ W.obj (op n) // a n ≫ e.hom = b n})
    (hu : ∀ n, Epi (a n)) :
    {e : (F ⋙ T) ⋙ S ≅ W // ∀ n,
      e.hom.app (op n) = sq.hom.app (F.obj (op n)) ≫
        H.map (β.hom.app (op n)) ≫ (d n).val.hom} := by
  refine ⟨Functor.associator F T S ≪≫ Functor.isoWhiskerLeft F sq ≪≫
    (Functor.associator F P H).symm ≪≫ Functor.isoWhiskerRight β H ≪≫ c.val, ?_⟩
  intro n
  let := hu n
  have hd : c.val.hom.app (op n) = (d n).val.hom :=
    (cancel_epi (a n)).mp ((c.property n).trans (d n).property.symm)
  change (𝟙 _ ≫ sq.hom.app (F.obj (op n)) ≫ 𝟙 _ ≫
    H.map (β.hom.app (op n)) ≫ c.val.hom.app (op n)) = _
  rw [Category.id_comp, Category.id_comp, hd]

end AlgebraicGeometry.Scheme.Modules.Coherent
