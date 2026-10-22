/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Cohomology.GrothendieckExistence.ReconstructionChart
public import Aglib.AlgebraicGeometry.Cohomology.GrothendieckExistence.ReconstructionSubobject
public import Aglib.AlgebraicGeometry.Modules.Locality.Exactness

/-! # Local identification of the original global reconstruction comparison

The comparison of a coherent subobject with its actual chart coefficient is
required to preserve the original ambient inclusion. This equation identifies
the canonical global completion map, not merely an unspecified isomorphism.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.Scheme.Modules.Coherent

/-- Functorial transport of the original unit equation before specialization. -/
theorem mappedOriginalUnitEquation {C D : Type*} [Category C] [Category D]
    (T : C ⥤ D) {U V W Z : C} (u : U ⟶ V) (f : V ⟶ W)
    (s : U ⟶ Z) (r : Z ⟶ W) (h : u ≫ f = s ≫ r) :
    T.map u ≫ T.map f = T.map s ≫ T.map r := by
  rw [← T.map_comp, h, T.map_comp]

/-- Original quotient-unit naturality without an identity-functor wrapper. -/
theorem originalUnitNaturality {C : Type*} [Category C] (Q : C ⥤ C)
    (u : 𝟭 C ⟶ Q) {M N : C} (f : M ⟶ N) :
    u.app M ≫ Q.map f = f ≫ u.app N := by
  simpa only [Functor.id_map] using (u.naturality f).symm

/-- Identify the original formal map from all original unit and ambient-stage
certificates, while the objects and arrows are still abstract. -/
theorem formalMap_eq_comparison_of_units {C : Type*} [Category C]
    {P : ObjectProperty (ℕᵒᵖ ⥤ C)} {F₀ F₁ F₂ F₃ : P.FullSubcategory}
    (f : F₀ ⟶ F₃) (e : F₀ ⟶ F₁) (k : F₁ ⟶ F₂) (g : F₂ ⟶ F₃)
    {U V Z : C} (s : U ⟶ Z) (c : U ⟶ V) (l : V ⟶ Z)
    (r : ∀ n, Z ⟶ F₃.obj.obj (op n)) (v : ∀ n, V ⟶ F₃.obj.obj (op n))
    (u₀ : ∀ n, U ⟶ F₀.obj.obj (op n)) (u₁ : ∀ n, U ⟶ F₁.obj.obj (op n))
    (u₂ : ∀ n, V ⟶ F₂.obj.obj (op n)) [∀ n, Epi (u₀ n)]
    (hf : ∀ n, u₀ n ≫ f.hom.app (op n) = s ≫ r n)
    (he : ∀ n, u₀ n ≫ e.hom.app (op n) = u₁ n)
    (hk : ∀ n, u₁ n ≫ k.hom.app (op n) = c ≫ u₂ n)
    (hg : ∀ n, u₂ n ≫ g.hom.app (op n) = v n)
    (hc : s = c ≫ l) (hl : ∀ n, l ≫ r n = v n) : f = e ≫ k ≫ g := by
  apply ObjectProperty.hom_ext
  apply NatTrans.ext
  funext n
  rcases n with ⟨n⟩
  change f.hom.app (op n) = e.hom.app (op n) ≫ k.hom.app (op n) ≫ g.hom.app (op n)
  apply (cancel_epi (u₀ n)).mp
  calc
    u₀ n ≫ f.hom.app (op n) = s ≫ r n := hf n
    _ = c ≫ v n := by rw [hc, Category.assoc, hl]
    _ = u₀ n ≫ (e.hom.app (op n) ≫ k.hom.app (op n) ≫ g.hom.app (op n)) := by
      rw [← Category.assoc, he, ← Category.assoc, hk, Category.assoc, hg]

universe u v
variable {X : Scheme.{u}} [IsLocallyNoetherian X]
  {B : CommRingCat.{u}} [IsNoetherianRing B]
  (p : Spec B ⟶ X) [IsOpenImmersion p]
  {K : X.IdealSheafData} {F : AdicSystem X K} {H G : X.CoherentSheaf}
  (α : F ⟶ (completionFunctor X K).obj H)
  (t : ℕ) (h : AdicSystem.DefectsKilled K t α)
  (s : G.obj ⟶ reconstructionPullback α)
  (c : (coherentPullback p).obj G ≅ reconstructionChart p α t h)
  (hc : (pullback p).map s = c.hom.hom ≫ reconstructionChartLift p α t h)

include hc in
/-- The original global comparison, on an affine chart, is the actual affine
bounded reconstruction comparison through the specified original local map. -/
theorem reconstructionSubobjectCompletionMap_chart :
    (openIdealPullbackFunctor p K).map (reconstructionSubobjectCompletionMap α s) =
      (openIdealPullbackCompletionIso p K G).hom ≫
        (completionFunctor (Spec B) (K.comap p)).map c.hom ≫
          (affineReconstructionCompletionIso (openReconstructionComparison p α) t
            (openReconstructionComparison_defectsKilled p α K t h)).hom := by
  apply formalMap_eq_comparison_of_units
    ((openIdealPullbackFunctor p K).map (reconstructionSubobjectCompletionMap α s))
    (openIdealPullbackCompletionIso p K G).hom
    ((completionFunctor (Spec B) (K.comap p)).map c.hom)
    (affineReconstructionCompletionIso (openReconstructionComparison p α) t
      (openReconstructionComparison_defectsKilled p α K t h)).hom
    ((pullback p).map s) c.hom.hom (reconstructionChartLift p α t h)
    (fun n => (pullback p).map (reconstructionToStage α (op n)))
    (fun n => (reconstructionChartStages p α t h).app (op n))
    (fun n => (pullback p).map ((idealSheafQuotientUnit X (K ^ n)).app G.obj))
    (fun n => (idealSheafQuotientUnit (Spec B) (K.comap p ^ n)).app
      ((pullback p).obj G.obj))
    (fun n => (idealSheafQuotientUnit (Spec B) (K.comap p ^ n)).app
      (reconstructionChart p α t h).obj)
  · intro n
    exact mappedOriginalUnitEquation (pullback p)
      ((idealSheafQuotientUnit X (K ^ n)).app G.obj)
      ((reconstructionSubobjectCompletionMap α s).hom.app (op n))
      s (reconstructionToStage α (op n))
      (reconstructionSubobjectCompletionMap_unit α s (op n))
  · exact openIdealPullbackCompletionIso_unit p K G
  · intro n
    exact originalUnitNaturality (idealSheafQuotientFunctor (Spec B) (K.comap p ^ n))
      (idealSheafQuotientUnit (Spec B) (K.comap p ^ n)) c.hom.hom
  · intro n
    exact idealSheafQuotientUnit_desc (Spec B) (K.comap p ^ n)
      ((reconstructionChartStages p α t h).app (op n))
      (((openIdealPullbackFunctor p K).obj F).property.annihilated n)
  · exact hc
  · intro n
    exact reconstructionChartLift_toStage p α t h (op n)

include hc in
/-- Consequently every original pulled completion-stage map is invertible. -/
theorem reconstructionSubobjectCompletionMap_chart_isIso (n : ℕᵒᵖ) :
    IsIso ((pullback p).map ((reconstructionSubobjectCompletionMap α s).hom.app n)) := by
  have he := congrArg (fun f => f.hom.app n)
    (reconstructionSubobjectCompletionMap_chart p α t h s c hc)
  change (pullback p).map ((reconstructionSubobjectCompletionMap α s).hom.app n) =
    (openIdealPullbackCompletionIso p K G).hom.hom.app n ≫
      ((completionFunctor (Spec B) (K.comap p)).map c.hom).hom.app n ≫
        (affineReconstructionCompletionIso (openReconstructionComparison p α) t
          (openReconstructionComparison_defectsKilled p α K t h)).hom.hom.app n at he
  rw [he]
  infer_instance

end AlgebraicGeometry.Scheme.Modules.Coherent
