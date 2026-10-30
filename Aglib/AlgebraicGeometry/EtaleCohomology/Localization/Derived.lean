/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.CategoryTheory.Triangulated.LocalizationTriangle
public import Aglib.AlgebraicGeometry.EtaleCohomology.Localization.DerivedComparison

/-!
# Functorial module localization on the original bounded-below derived category

The actual complex-triangle functor inverts quasi-isomorphisms and descends by
the native localization universal property. The native factorization isomorphism
and descended vertex comparisons retain the original complex localization data.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated

namespace AlgebraicGeometry.Scheme.EtaleCohomology

open Coefficients

universe u wU wZ wX

variable {U Z X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j]
  (Λ : Type (u + 1)) [Ring Λ] (i : Z ⟶ X) [IsClosedImmersion i]
  (hcomp : Set.range j = (Set.range i)ᶜ)
  [HasDerivedCategory.{wU} (ModuleSheaf U Λ)]
  [HasDerivedCategory.{wZ} (ModuleSheaf Z Λ)]
  [HasDerivedCategory.{wX} (ModuleSheaf X Λ)]

/-- The first vertex comparison is a natural isomorphism of the actual complex functors. -/
def moduleLocalizationComplexFirstNatIso :
    moduleLocalizationComplexTriangleFunctor j Λ i hcomp ⋙ Triangle.π₁ ≅
      DerivedCategory.Plus.Q ⋙ moduleDerivedInverseImage Λ j ⋙ moduleDerivedLowerShriek j Λ :=
  Functor.isoOfSourceMap (moduleLocalizationFirstVertexNatIso j Λ) rfl (by
    apply heq_of_eq
    funext K L a
    exact DerivedCategory.Plus.triangleOfSESPlusMap_hom₁ _ _ _)

/-- The middle vertex remains the original localization functor. -/
def moduleLocalizationComplexMiddleNatIso :
    moduleLocalizationComplexTriangleFunctor j Λ i hcomp ⋙ Triangle.π₂ ≅
      DerivedCategory.Plus.Q :=
  NatIso.ofComponents (fun _ ↦ Iso.refl _) (by
    intro K L a
    change (moduleLocalizationComplexTriangleMap j Λ i hcomp a).hom₂ ≫ 𝟙 _ =
      𝟙 _ ≫ DerivedCategory.Plus.Q.map a
    rw [Category.comp_id, Category.id_comp]
    exact DerivedCategory.Plus.triangleOfSESPlusMap_hom₂ _ _ _)

/-- The third vertex is the actual separately derived closed composite, naturally. -/
def moduleLocalizationComplexThirdNatIso :
    moduleLocalizationComplexTriangleFunctor j Λ i hcomp ⋙ Triangle.π₃ ≅
      DerivedCategory.Plus.Q ⋙ moduleDerivedInverseImage Λ i ⋙ moduleDerivedDirectImage Λ i :=
  Functor.isoOfSourceMap (moduleLocalizationThirdVertexNatIso Λ i) rfl (by
    apply heq_of_eq
    funext K L a
    exact DerivedCategory.Plus.triangleOfSESPlusMap_hom₃ _ _ _)

/-- The original complex-triangle functor inverts the original quasi-isomorphisms. -/
theorem moduleLocalizationComplexTriangleFunctor_inverts :
    (CochainComplex.Plus.quasiIso (ModuleSheaf X Λ)).IsInvertedBy
      (moduleLocalizationComplexTriangleFunctor j Λ i hcomp) := by
  exact Localization.triangleFunctor_inverts DerivedCategory.Plus.Q
    (CochainComplex.Plus.quasiIso (ModuleSheaf X Λ))
    (moduleLocalizationComplexTriangleFunctor j Λ i hcomp)
    (moduleDerivedInverseImage Λ j ⋙ moduleDerivedLowerShriek j Λ) (𝟭 _)
    (moduleDerivedInverseImage Λ i ⋙ moduleDerivedDirectImage Λ i)
    (moduleLocalizationComplexFirstNatIso j Λ i hcomp)
    (moduleLocalizationComplexMiddleNatIso j Λ i hcomp ≪≫ (Functor.rightUnitor _).symm)
    (moduleLocalizationComplexThirdNatIso j Λ i hcomp)

/-- The native localization of the actual complex-triangle functor. -/
def moduleLocalizationTriangleFunctor :
    DerivedCategory.Plus (ModuleSheaf X Λ) ⥤
      Triangle (DerivedCategory.Plus (ModuleSheaf X Λ)) :=
  Localization.liftTriangleFunctor DerivedCategory.Plus.Q
    (CochainComplex.Plus.quasiIso (ModuleSheaf X Λ))
    (moduleLocalizationComplexTriangleFunctor j Λ i hcomp)
    (moduleDerivedInverseImage Λ j ⋙ moduleDerivedLowerShriek j Λ) (𝟭 _)
    (moduleDerivedInverseImage Λ i ⋙ moduleDerivedDirectImage Λ i)
    (moduleLocalizationComplexFirstNatIso j Λ i hcomp)
    (moduleLocalizationComplexMiddleNatIso j Λ i hcomp ≪≫ (Functor.rightUnitor _).symm)
    (moduleLocalizationComplexThirdNatIso j Λ i hcomp)

/-- The shared constructor retains the original native localization value. -/
theorem moduleLocalizationTriangleFunctor_eq_original :
    moduleLocalizationTriangleFunctor j Λ i hcomp =
      Localization.lift (moduleLocalizationComplexTriangleFunctor j Λ i hcomp)
        (moduleLocalizationComplexTriangleFunctor_inverts j Λ i hcomp) DerivedCategory.Plus.Q := rfl

/-- The original native factorization comparison on bounded-below complexes. -/
def moduleLocalizationTriangleFunctorFac :
    DerivedCategory.Plus.Q ⋙ moduleLocalizationTriangleFunctor j Λ i hcomp ≅
      moduleLocalizationComplexTriangleFunctor j Λ i hcomp :=
  Localization.liftTriangleFunctorFac DerivedCategory.Plus.Q
    (CochainComplex.Plus.quasiIso (ModuleSheaf X Λ))
    (moduleLocalizationComplexTriangleFunctor j Λ i hcomp)
    (moduleDerivedInverseImage Λ j ⋙ moduleDerivedLowerShriek j Λ) (𝟭 _)
    (moduleDerivedInverseImage Λ i ⋙ moduleDerivedDirectImage Λ i)
    (moduleLocalizationComplexFirstNatIso j Λ i hcomp)
    (moduleLocalizationComplexMiddleNatIso j Λ i hcomp ≪≫ (Functor.rightUnitor _).symm)
    (moduleLocalizationComplexThirdNatIso j Λ i hcomp)

/-- Descended triangles are distinguished; representatives only prove this property. -/
theorem moduleLocalizationTriangleFunctor_distinguished
    (M : DerivedCategory.Plus (ModuleSheaf X Λ)) :
    (moduleLocalizationTriangleFunctor j Λ i hcomp).obj M ∈
      distTriang (DerivedCategory.Plus (ModuleSheaf X Λ)) := by
  exact Localization.liftTriangleFunctor_distinguished DerivedCategory.Plus.Q
    (CochainComplex.Plus.quasiIso (ModuleSheaf X Λ))
    (moduleLocalizationComplexTriangleFunctor j Λ i hcomp)
    (moduleDerivedInverseImage Λ j ⋙ moduleDerivedLowerShriek j Λ) (𝟭 _)
    (moduleDerivedInverseImage Λ i ⋙ moduleDerivedDirectImage Λ i)
    (moduleLocalizationComplexFirstNatIso j Λ i hcomp)
    (moduleLocalizationComplexMiddleNatIso j Λ i hcomp ≪≫ (Functor.rightUnitor _).symm)
    (moduleLocalizationComplexThirdNatIso j Λ i hcomp)
    (moduleLocalizationComplexTriangle_distinguished j Λ i hcomp) M

/-- The descended first vertex is naturally the genuine derived open composite. -/
def moduleLocalizationFirstNatIso :
    moduleLocalizationTriangleFunctor j Λ i hcomp ⋙ Triangle.π₁ ≅
      moduleDerivedInverseImage Λ j ⋙ moduleDerivedLowerShriek j Λ :=
  Localization.liftTriangleVertexIso DerivedCategory.Plus.Q
    (CochainComplex.Plus.quasiIso (ModuleSheaf X Λ))
    (moduleLocalizationComplexTriangleFunctor j Λ i hcomp)
    (moduleDerivedInverseImage Λ j ⋙ moduleDerivedLowerShriek j Λ) (𝟭 _)
    (moduleDerivedInverseImage Λ i ⋙ moduleDerivedDirectImage Λ i)
    (moduleLocalizationComplexFirstNatIso j Λ i hcomp)
    (moduleLocalizationComplexMiddleNatIso j Λ i hcomp ≪≫ (Functor.rightUnitor _).symm)
    (moduleLocalizationComplexThirdNatIso j Λ i hcomp)
    Triangle.π₁ (moduleDerivedInverseImage Λ j ⋙ moduleDerivedLowerShriek j Λ)
      (moduleLocalizationComplexFirstNatIso j Λ i hcomp)

/-- The descended middle vertex is naturally the identity on the original derived category. -/
def moduleLocalizationMiddleNatIso :
    moduleLocalizationTriangleFunctor j Λ i hcomp ⋙ Triangle.π₂ ≅
      𝟭 (DerivedCategory.Plus (ModuleSheaf X Λ)) :=
  Localization.liftTriangleVertexIso DerivedCategory.Plus.Q
    (CochainComplex.Plus.quasiIso (ModuleSheaf X Λ))
    (moduleLocalizationComplexTriangleFunctor j Λ i hcomp)
    (moduleDerivedInverseImage Λ j ⋙ moduleDerivedLowerShriek j Λ) (𝟭 _)
    (moduleDerivedInverseImage Λ i ⋙ moduleDerivedDirectImage Λ i)
    (moduleLocalizationComplexFirstNatIso j Λ i hcomp)
    (moduleLocalizationComplexMiddleNatIso j Λ i hcomp ≪≫ (Functor.rightUnitor _).symm)
    (moduleLocalizationComplexThirdNatIso j Λ i hcomp)
    Triangle.π₂ (𝟭 _)
      (moduleLocalizationComplexMiddleNatIso j Λ i hcomp ≪≫ (Functor.rightUnitor _).symm)

/-- The descended third vertex is naturally the genuine derived closed composite. -/
def moduleLocalizationThirdNatIso :
    moduleLocalizationTriangleFunctor j Λ i hcomp ⋙ Triangle.π₃ ≅
      moduleDerivedInverseImage Λ i ⋙ moduleDerivedDirectImage Λ i :=
  Localization.liftTriangleVertexIso DerivedCategory.Plus.Q
    (CochainComplex.Plus.quasiIso (ModuleSheaf X Λ))
    (moduleLocalizationComplexTriangleFunctor j Λ i hcomp)
    (moduleDerivedInverseImage Λ j ⋙ moduleDerivedLowerShriek j Λ) (𝟭 _)
    (moduleDerivedInverseImage Λ i ⋙ moduleDerivedDirectImage Λ i)
    (moduleLocalizationComplexFirstNatIso j Λ i hcomp)
    (moduleLocalizationComplexMiddleNatIso j Λ i hcomp ≪≫ (Functor.rightUnitor _).symm)
    (moduleLocalizationComplexThirdNatIso j Λ i hcomp)
    Triangle.π₃ (moduleDerivedInverseImage Λ i ⋙ moduleDerivedDirectImage Λ i)
      (moduleLocalizationComplexThirdNatIso j Λ i hcomp)

/-- The descended first comparison retains its original factorization on complexes. -/
@[simp]
theorem moduleLocalizationFirstNatIso_hom_app
    (K : CochainComplex.Plus (ModuleSheaf X Λ)) :
    (moduleLocalizationFirstNatIso j Λ i hcomp).hom.app (DerivedCategory.Plus.Q.obj K) =
      ((moduleLocalizationTriangleFunctorFac j Λ i hcomp).hom.app K).hom₁ ≫
        (moduleLocalizationFirstVertexIso j Λ K).hom := by
  have h :=
    Localization.liftTriangleVertexIso_hom_app DerivedCategory.Plus.Q
      (CochainComplex.Plus.quasiIso (ModuleSheaf X Λ))
      (moduleLocalizationComplexTriangleFunctor j Λ i hcomp)
      (moduleDerivedInverseImage Λ j ⋙ moduleDerivedLowerShriek j Λ) (𝟭 _)
      (moduleDerivedInverseImage Λ i ⋙ moduleDerivedDirectImage Λ i)
      (moduleLocalizationComplexFirstNatIso j Λ i hcomp)
      (moduleLocalizationComplexMiddleNatIso j Λ i hcomp ≪≫ (Functor.rightUnitor _).symm)
      (moduleLocalizationComplexThirdNatIso j Λ i hcomp)
      Triangle.π₁ (moduleDerivedInverseImage Λ j ⋙ moduleDerivedLowerShriek j Λ)
        (moduleLocalizationComplexFirstNatIso j Λ i hcomp) K
  change (moduleLocalizationFirstNatIso j Λ i hcomp).hom.app
      (DerivedCategory.Plus.Q.obj K) =
    ((moduleLocalizationTriangleFunctorFac j Λ i hcomp).hom.app K).hom₁ ≫
      (moduleLocalizationComplexFirstNatIso j Λ i hcomp).hom.app K at h
  have hv := Functor.isoOfSourceMap_hom_app
    (T := moduleLocalizationComplexTriangleFunctor j Λ i hcomp ⋙ Triangle.π₁)
    (moduleLocalizationFirstVertexNatIso j Λ) rfl (by
      apply heq_of_eq
      funext A B a
      exact DerivedCategory.Plus.triangleOfSESPlusMap_hom₁ _ _ _) K
  have hc : (moduleLocalizationComplexFirstNatIso j Λ i hcomp).hom.app K =
      (moduleLocalizationFirstVertexIso j Λ K).hom :=
    hv.trans (Category.id_comp _)
  exact h.trans (congrArg (fun z =>
    ((moduleLocalizationTriangleFunctorFac j Λ i hcomp).hom.app K).hom₁ ≫ z) hc)

/-- The descended middle comparison is the original factorization component. -/
@[simp]
theorem moduleLocalizationMiddleNatIso_hom_app
    (K : CochainComplex.Plus (ModuleSheaf X Λ)) :
    (moduleLocalizationMiddleNatIso j Λ i hcomp).hom.app (DerivedCategory.Plus.Q.obj K) =
      ((moduleLocalizationTriangleFunctorFac j Λ i hcomp).hom.app K).hom₂ := by
  have h :=
    Localization.liftTriangleVertexIso_hom_app DerivedCategory.Plus.Q
      (CochainComplex.Plus.quasiIso (ModuleSheaf X Λ))
      (moduleLocalizationComplexTriangleFunctor j Λ i hcomp)
      (moduleDerivedInverseImage Λ j ⋙ moduleDerivedLowerShriek j Λ) (𝟭 _)
      (moduleDerivedInverseImage Λ i ⋙ moduleDerivedDirectImage Λ i)
      (moduleLocalizationComplexFirstNatIso j Λ i hcomp)
      (moduleLocalizationComplexMiddleNatIso j Λ i hcomp ≪≫ (Functor.rightUnitor _).symm)
      (moduleLocalizationComplexThirdNatIso j Λ i hcomp)
      Triangle.π₂ (𝟭 _)
        (moduleLocalizationComplexMiddleNatIso j Λ i hcomp ≪≫ (Functor.rightUnitor _).symm) K
  change (moduleLocalizationMiddleNatIso j Λ i hcomp).hom.app (DerivedCategory.Plus.Q.obj K) =
    ((moduleLocalizationTriangleFunctorFac j Λ i hcomp).hom.app K).hom₂ ≫
      (𝟙 _ ≫ 𝟙 _) at h
  simpa only [Category.comp_id] using h

/-- The descended closed comparison retains its original factorization on complexes. -/
@[simp]
theorem moduleLocalizationThirdNatIso_hom_app
    (K : CochainComplex.Plus (ModuleSheaf X Λ)) :
    (moduleLocalizationThirdNatIso j Λ i hcomp).hom.app (DerivedCategory.Plus.Q.obj K) =
      ((moduleLocalizationTriangleFunctorFac j Λ i hcomp).hom.app K).hom₃ ≫
        (moduleLocalizationThirdVertexIso Λ i K).hom := by
  have h :=
    Localization.liftTriangleVertexIso_hom_app DerivedCategory.Plus.Q
      (CochainComplex.Plus.quasiIso (ModuleSheaf X Λ))
      (moduleLocalizationComplexTriangleFunctor j Λ i hcomp)
      (moduleDerivedInverseImage Λ j ⋙ moduleDerivedLowerShriek j Λ) (𝟭 _)
      (moduleDerivedInverseImage Λ i ⋙ moduleDerivedDirectImage Λ i)
      (moduleLocalizationComplexFirstNatIso j Λ i hcomp)
      (moduleLocalizationComplexMiddleNatIso j Λ i hcomp ≪≫ (Functor.rightUnitor _).symm)
      (moduleLocalizationComplexThirdNatIso j Λ i hcomp)
      Triangle.π₃ (moduleDerivedInverseImage Λ i ⋙ moduleDerivedDirectImage Λ i)
        (moduleLocalizationComplexThirdNatIso j Λ i hcomp) K
  change (moduleLocalizationThirdNatIso j Λ i hcomp).hom.app
      (DerivedCategory.Plus.Q.obj K) =
    ((moduleLocalizationTriangleFunctorFac j Λ i hcomp).hom.app K).hom₃ ≫
      (moduleLocalizationComplexThirdNatIso j Λ i hcomp).hom.app K at h
  have hv := Functor.isoOfSourceMap_hom_app
    (T := moduleLocalizationComplexTriangleFunctor j Λ i hcomp ⋙ Triangle.π₃)
    (moduleLocalizationThirdVertexNatIso Λ i) rfl (by
      apply heq_of_eq
      funext A B a
      exact DerivedCategory.Plus.triangleOfSESPlusMap_hom₃ _ _ _) K
  have hc : (moduleLocalizationComplexThirdNatIso j Λ i hcomp).hom.app K =
      (moduleLocalizationThirdVertexIso Λ i K).hom :=
    hv.trans (Category.id_comp _)
  exact h.trans (congrArg (fun z =>
    ((moduleLocalizationTriangleFunctorFac j Λ i hcomp).hom.app K).hom₃ ≫ z) hc)

/-- The first descended arrow is the original derived adjunction counit, naturally. -/
theorem moduleLocalization_counit_comparison :
    Functor.whiskerLeft (moduleLocalizationTriangleFunctor j Λ i hcomp) Triangle.π₁Toπ₂ ≫
      (moduleLocalizationMiddleNatIso j Λ i hcomp).hom =
    (moduleLocalizationFirstNatIso j Λ i hcomp).hom ≫
      (moduleDerivedLowerShriekAdjunction j Λ).counit := by
  apply Localization.natTrans_ext DerivedCategory.Plus.Q
    (CochainComplex.Plus.quasiIso (ModuleSheaf X Λ))
  intro K
  dsimp only [NatTrans.comp_app, Functor.whiskerLeft_app, Triangle.π₁Toπ₂_app]
  rw [moduleLocalizationFirstNatIso_hom_app, moduleLocalizationMiddleNatIso_hom_app]
  erw [Category.assoc, moduleLocalizationFirstVertexIso_counit]
  exact ((moduleLocalizationTriangleFunctorFac j Λ i hcomp).hom.app K).comm₁

/-- The second descended arrow is the original derived adjunction unit, naturally. -/
theorem moduleLocalization_unit_comparison :
    Functor.whiskerLeft (moduleLocalizationTriangleFunctor j Λ i hcomp) Triangle.π₂Toπ₃ ≫
      (moduleLocalizationThirdNatIso j Λ i hcomp).hom =
    (moduleLocalizationMiddleNatIso j Λ i hcomp).hom ≫
      (moduleDerivedAdjunction Λ i).unit := by
  apply Localization.natTrans_ext DerivedCategory.Plus.Q
    (CochainComplex.Plus.quasiIso (ModuleSheaf X Λ))
  intro K
  dsimp only [NatTrans.comp_app, Functor.whiskerLeft_app, Triangle.π₂Toπ₃_app]
  rw [moduleLocalizationThirdNatIso_hom_app, moduleLocalizationMiddleNatIso_hom_app]
  erw [← Category.assoc, ((moduleLocalizationTriangleFunctorFac j Λ i hcomp).hom.app K).comm₂,
    Category.assoc]
  change _ ≫ (DerivedCategory.Plus.Q.map
      ((moduleInverseImageAdjunction i Λ).mapCochainComplexPlus.unit.app K) ≫
      (moduleLocalizationThirdVertexIso Λ i K).hom) = _
  rw [moduleLocalizationThirdVertexIso_unit]

/-- Localization on any original derived object, with the actual derived unit and counit. -/
def moduleDerivedLocalizationTriangle (M : DerivedCategory.Plus (ModuleSheaf X Λ)) :
    Triangle (DerivedCategory.Plus (ModuleSheaf X Λ)) :=
  (Triangle.normalizeFunctor (moduleLocalizationTriangleFunctor j Λ i hcomp)
    (moduleLocalizationFirstNatIso j Λ i hcomp)
    (moduleLocalizationThirdNatIso j Λ i hcomp)
    (moduleDerivedLowerShriekAdjunction j Λ).counit (moduleDerivedAdjunction Λ i).unit).obj M

/-- The normalization is a genuine triangle isomorphism, not a changed third vertex label. -/
def moduleDerivedLocalizationTriangleIso (M : DerivedCategory.Plus (ModuleSheaf X Λ)) :
    (moduleLocalizationTriangleFunctor j Λ i hcomp).obj M ≅
      moduleDerivedLocalizationTriangle j Λ i hcomp M :=
  (Triangle.normalizeFunctorIso (moduleLocalizationTriangleFunctor j Λ i hcomp)
    (moduleLocalizationFirstNatIso j Λ i hcomp)
    (moduleLocalizationMiddleNatIso j Λ i hcomp)
    (moduleLocalizationThirdNatIso j Λ i hcomp)
    (moduleDerivedLowerShriekAdjunction j Λ).counit (moduleDerivedAdjunction Λ i).unit
    (moduleLocalization_counit_comparison j Λ i hcomp)
      (moduleLocalization_unit_comparison j Λ i hcomp)).app M

/-- The actual localization triangle is distinguished for every original bounded-below object. -/
theorem moduleDerivedLocalizationTriangle_distinguished
    (M : DerivedCategory.Plus (ModuleSheaf X Λ)) :
    moduleDerivedLocalizationTriangle j Λ i hcomp M ∈
      distTriang (DerivedCategory.Plus (ModuleSheaf X Λ)) := by
  exact Triangle.normalizeFunctor_distinguished (moduleLocalizationTriangleFunctor j Λ i hcomp)
    (moduleLocalizationFirstNatIso j Λ i hcomp)
    (moduleLocalizationMiddleNatIso j Λ i hcomp)
    (moduleLocalizationThirdNatIso j Λ i hcomp)
    (moduleDerivedLowerShriekAdjunction j Λ).counit (moduleDerivedAdjunction Λ i).unit
    (moduleLocalization_counit_comparison j Λ i hcomp)
      (moduleLocalization_unit_comparison j Λ i hcomp)
    (moduleLocalizationTriangleFunctor_distinguished j Λ i hcomp) M

/-- The actual derived localization triangles form a functor on all of the original D+. -/
def moduleDerivedLocalizationTriangleFunctor :
    DerivedCategory.Plus (ModuleSheaf X Λ) ⥤
      Triangle (DerivedCategory.Plus (ModuleSheaf X Λ)) :=
  Triangle.normalizeFunctor (moduleLocalizationTriangleFunctor j Λ i hcomp)
    (moduleLocalizationFirstNatIso j Λ i hcomp)
    (moduleLocalizationThirdNatIso j Λ i hcomp)
    (moduleDerivedLowerShriekAdjunction j Λ).counit (moduleDerivedAdjunction Λ i).unit


/-- The shared normalized functor retains the original conjugated triangle map. -/
theorem moduleDerivedLocalizationTriangleFunctor_map_eq_original
    {M N : DerivedCategory.Plus (ModuleSheaf X Λ)} (a : M ⟶ N) :
    (moduleDerivedLocalizationTriangleFunctor j Λ i hcomp).map a =
      (moduleDerivedLocalizationTriangleIso j Λ i hcomp M).inv ≫
        (moduleLocalizationTriangleFunctor j Λ i hcomp).map a ≫
        (moduleDerivedLocalizationTriangleIso j Λ i hcomp N).hom := by
  exact Triangle.normalizeFunctor_map_eq_original (moduleLocalizationTriangleFunctor j Λ i hcomp)
    (moduleLocalizationFirstNatIso j Λ i hcomp)
    (moduleLocalizationMiddleNatIso j Λ i hcomp)
    (moduleLocalizationThirdNatIso j Λ i hcomp)
    (moduleDerivedLowerShriekAdjunction j Λ).counit (moduleDerivedAdjunction Λ i).unit
    (moduleLocalization_counit_comparison j Λ i hcomp)
      (moduleLocalization_unit_comparison j Λ i hcomp) a

end AlgebraicGeometry.Scheme.EtaleCohomology
