/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.CategoryTheory.Triangulated.LocalizationTriangle
public import Aglib.AlgebraicGeometry.EtaleCohomology.Localization.UnboundedComparison

/-!
# Functorial module localization on the original unbounded derived category

The actual arbitrary-cochain triangle functor inverts quasi-isomorphisms and
descends through the native unbounded localization. Its vertex comparisons
retain the original open counit, closed unit, and mapping-cone connecting map.
The resulting distinguished triangle is functorial on all native derived
objects. No boundedness, finite cohomological dimension, or PBC premise is used.
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
def moduleUnboundedLocalizationComplexFirstNatIso :
    moduleUnboundedLocalizationComplexTriangleFunctor j Λ i hcomp ⋙ Triangle.π₁ ≅
      DerivedCategory.Q ⋙ moduleUnboundedDerivedInverseImage Λ j ⋙
        moduleUnboundedDerivedLowerShriek j Λ :=
  Functor.isoOfSourceMap (moduleUnboundedLocalizationFirstVertexNatIso j Λ) rfl (by
    apply heq_of_eq
    funext K L a
    exact moduleUnboundedLocalizationComplexTriangleMap_hom₁ j Λ i hcomp a)

/-- The middle vertex remains the original localization functor. -/
def moduleUnboundedLocalizationComplexMiddleNatIso :
    moduleUnboundedLocalizationComplexTriangleFunctor j Λ i hcomp ⋙ Triangle.π₂ ≅
      DerivedCategory.Q :=
  NatIso.ofComponents (fun _ ↦ Iso.refl _) (by
    intro K L a
    change (moduleUnboundedLocalizationComplexTriangleMap j Λ i hcomp a).hom₂ ≫ 𝟙 _ =
      𝟙 _ ≫ DerivedCategory.Q.map a
    rw [Category.comp_id, Category.id_comp]
    exact moduleUnboundedLocalizationComplexTriangleMap_hom₂ j Λ i hcomp a)

/-- The third vertex is the actual separately derived closed composite, naturally. -/
def moduleUnboundedLocalizationComplexThirdNatIso :
    moduleUnboundedLocalizationComplexTriangleFunctor j Λ i hcomp ⋙ Triangle.π₃ ≅
      DerivedCategory.Q ⋙ moduleUnboundedDerivedInverseImage Λ i ⋙
        moduleUnboundedDerivedDirectImage Λ i :=
  Functor.isoOfSourceMap (moduleUnboundedLocalizationThirdVertexNatIso Λ i) rfl (by
    apply heq_of_eq
    funext K L a
    exact moduleUnboundedLocalizationComplexTriangleMap_hom₃ j Λ i hcomp a)

/-- The original complex-triangle functor inverts the original quasi-isomorphisms. -/
theorem moduleUnboundedLocalizationComplexTriangleFunctor_inverts :
    (HomologicalComplex.quasiIso (ModuleSheaf X Λ) (.up ℤ)).IsInvertedBy
      (moduleUnboundedLocalizationComplexTriangleFunctor j Λ i hcomp) := by
  exact Localization.triangleFunctor_inverts DerivedCategory.Q
    (HomologicalComplex.quasiIso (ModuleSheaf X Λ) (.up ℤ))
    (moduleUnboundedLocalizationComplexTriangleFunctor j Λ i hcomp)
    (moduleUnboundedDerivedInverseImage Λ j ⋙ moduleUnboundedDerivedLowerShriek j Λ) (𝟭 _)
    (moduleUnboundedDerivedInverseImage Λ i ⋙ moduleUnboundedDerivedDirectImage Λ i)
    (moduleUnboundedLocalizationComplexFirstNatIso j Λ i hcomp)
    (moduleUnboundedLocalizationComplexMiddleNatIso j Λ i hcomp ≪≫ (Functor.rightUnitor _).symm)
    (moduleUnboundedLocalizationComplexThirdNatIso j Λ i hcomp)

/-- The native localization of the actual complex-triangle functor. -/
def moduleUnboundedLocalizationTriangleFunctor :
    DerivedCategory (ModuleSheaf X Λ) ⥤
      Triangle (DerivedCategory (ModuleSheaf X Λ)) :=
  Localization.liftTriangleFunctor DerivedCategory.Q
    (HomologicalComplex.quasiIso (ModuleSheaf X Λ) (.up ℤ))
    (moduleUnboundedLocalizationComplexTriangleFunctor j Λ i hcomp)
    (moduleUnboundedDerivedInverseImage Λ j ⋙ moduleUnboundedDerivedLowerShriek j Λ) (𝟭 _)
    (moduleUnboundedDerivedInverseImage Λ i ⋙ moduleUnboundedDerivedDirectImage Λ i)
    (moduleUnboundedLocalizationComplexFirstNatIso j Λ i hcomp)
    (moduleUnboundedLocalizationComplexMiddleNatIso j Λ i hcomp ≪≫ (Functor.rightUnitor _).symm)
    (moduleUnboundedLocalizationComplexThirdNatIso j Λ i hcomp)

/-- The shared constructor retains the original native localization value. -/
theorem moduleUnboundedLocalizationTriangleFunctor_eq_original :
    moduleUnboundedLocalizationTriangleFunctor j Λ i hcomp =
      Localization.lift (moduleUnboundedLocalizationComplexTriangleFunctor j Λ i hcomp)
        (moduleUnboundedLocalizationComplexTriangleFunctor_inverts j Λ i hcomp) DerivedCategory.Q :=
  rfl

/-- The original native factorization comparison on arbitrary cochain complexes. -/
def moduleUnboundedLocalizationTriangleFunctorFac :
    DerivedCategory.Q ⋙ moduleUnboundedLocalizationTriangleFunctor j Λ i hcomp ≅
      moduleUnboundedLocalizationComplexTriangleFunctor j Λ i hcomp :=
  Localization.liftTriangleFunctorFac DerivedCategory.Q
    (HomologicalComplex.quasiIso (ModuleSheaf X Λ) (.up ℤ))
    (moduleUnboundedLocalizationComplexTriangleFunctor j Λ i hcomp)
    (moduleUnboundedDerivedInverseImage Λ j ⋙ moduleUnboundedDerivedLowerShriek j Λ) (𝟭 _)
    (moduleUnboundedDerivedInverseImage Λ i ⋙ moduleUnboundedDerivedDirectImage Λ i)
    (moduleUnboundedLocalizationComplexFirstNatIso j Λ i hcomp)
    (moduleUnboundedLocalizationComplexMiddleNatIso j Λ i hcomp ≪≫ (Functor.rightUnitor _).symm)
    (moduleUnboundedLocalizationComplexThirdNatIso j Λ i hcomp)

/-- Descended triangles are distinguished; representatives only prove this property. -/
theorem moduleUnboundedLocalizationTriangleFunctor_distinguished
    (M : DerivedCategory (ModuleSheaf X Λ)) :
    (moduleUnboundedLocalizationTriangleFunctor j Λ i hcomp).obj M ∈
      distTriang (DerivedCategory (ModuleSheaf X Λ)) := by
  exact Localization.liftTriangleFunctor_distinguished DerivedCategory.Q
    (HomologicalComplex.quasiIso (ModuleSheaf X Λ) (.up ℤ))
    (moduleUnboundedLocalizationComplexTriangleFunctor j Λ i hcomp)
    (moduleUnboundedDerivedInverseImage Λ j ⋙ moduleUnboundedDerivedLowerShriek j Λ) (𝟭 _)
    (moduleUnboundedDerivedInverseImage Λ i ⋙ moduleUnboundedDerivedDirectImage Λ i)
    (moduleUnboundedLocalizationComplexFirstNatIso j Λ i hcomp)
    (moduleUnboundedLocalizationComplexMiddleNatIso j Λ i hcomp ≪≫ (Functor.rightUnitor _).symm)
    (moduleUnboundedLocalizationComplexThirdNatIso j Λ i hcomp)
    (moduleUnboundedLocalizationComplexTriangle_distinguished j Λ i hcomp) M

/-- The descended first vertex is naturally the genuine derived open composite. -/
def moduleUnboundedLocalizationFirstNatIso :
    moduleUnboundedLocalizationTriangleFunctor j Λ i hcomp ⋙ Triangle.π₁ ≅
      moduleUnboundedDerivedInverseImage Λ j ⋙ moduleUnboundedDerivedLowerShriek j Λ :=
  Localization.liftTriangleVertexIso DerivedCategory.Q
    (HomologicalComplex.quasiIso (ModuleSheaf X Λ) (.up ℤ))
    (moduleUnboundedLocalizationComplexTriangleFunctor j Λ i hcomp)
    (moduleUnboundedDerivedInverseImage Λ j ⋙ moduleUnboundedDerivedLowerShriek j Λ) (𝟭 _)
    (moduleUnboundedDerivedInverseImage Λ i ⋙ moduleUnboundedDerivedDirectImage Λ i)
    (moduleUnboundedLocalizationComplexFirstNatIso j Λ i hcomp)
    (moduleUnboundedLocalizationComplexMiddleNatIso j Λ i hcomp ≪≫ (Functor.rightUnitor _).symm)
    (moduleUnboundedLocalizationComplexThirdNatIso j Λ i hcomp)
    Triangle.π₁ (moduleUnboundedDerivedInverseImage Λ j ⋙ moduleUnboundedDerivedLowerShriek j Λ)
      (moduleUnboundedLocalizationComplexFirstNatIso j Λ i hcomp)

/-- The descended middle vertex is naturally the identity on the original derived category. -/
def moduleUnboundedLocalizationMiddleNatIso :
    moduleUnboundedLocalizationTriangleFunctor j Λ i hcomp ⋙ Triangle.π₂ ≅
      𝟭 (DerivedCategory (ModuleSheaf X Λ)) :=
  Localization.liftTriangleVertexIso DerivedCategory.Q
    (HomologicalComplex.quasiIso (ModuleSheaf X Λ) (.up ℤ))
    (moduleUnboundedLocalizationComplexTriangleFunctor j Λ i hcomp)
    (moduleUnboundedDerivedInverseImage Λ j ⋙ moduleUnboundedDerivedLowerShriek j Λ) (𝟭 _)
    (moduleUnboundedDerivedInverseImage Λ i ⋙ moduleUnboundedDerivedDirectImage Λ i)
    (moduleUnboundedLocalizationComplexFirstNatIso j Λ i hcomp)
    (moduleUnboundedLocalizationComplexMiddleNatIso j Λ i hcomp ≪≫ (Functor.rightUnitor _).symm)
    (moduleUnboundedLocalizationComplexThirdNatIso j Λ i hcomp)
    Triangle.π₂ (𝟭 _)
      (moduleUnboundedLocalizationComplexMiddleNatIso j Λ i hcomp ≪≫ (Functor.rightUnitor _).symm)

/-- The descended third vertex is naturally the genuine derived closed composite. -/
def moduleUnboundedLocalizationThirdNatIso :
    moduleUnboundedLocalizationTriangleFunctor j Λ i hcomp ⋙ Triangle.π₃ ≅
      moduleUnboundedDerivedInverseImage Λ i ⋙ moduleUnboundedDerivedDirectImage Λ i :=
  Localization.liftTriangleVertexIso DerivedCategory.Q
    (HomologicalComplex.quasiIso (ModuleSheaf X Λ) (.up ℤ))
    (moduleUnboundedLocalizationComplexTriangleFunctor j Λ i hcomp)
    (moduleUnboundedDerivedInverseImage Λ j ⋙ moduleUnboundedDerivedLowerShriek j Λ) (𝟭 _)
    (moduleUnboundedDerivedInverseImage Λ i ⋙ moduleUnboundedDerivedDirectImage Λ i)
    (moduleUnboundedLocalizationComplexFirstNatIso j Λ i hcomp)
    (moduleUnboundedLocalizationComplexMiddleNatIso j Λ i hcomp ≪≫ (Functor.rightUnitor _).symm)
    (moduleUnboundedLocalizationComplexThirdNatIso j Λ i hcomp)
    Triangle.π₃ (moduleUnboundedDerivedInverseImage Λ i ⋙ moduleUnboundedDerivedDirectImage Λ i)
      (moduleUnboundedLocalizationComplexThirdNatIso j Λ i hcomp)

/-- The descended first comparison retains its original factorization on complexes. -/
@[simp]
theorem moduleUnboundedLocalizationFirstNatIso_hom_app
    (K : CochainComplex (ModuleSheaf X Λ) ℤ) :
    (moduleUnboundedLocalizationFirstNatIso j Λ i hcomp).hom.app (DerivedCategory.Q.obj K) =
      ((moduleUnboundedLocalizationTriangleFunctorFac j Λ i hcomp).hom.app K).hom₁ ≫
        (moduleUnboundedLocalizationFirstVertexIso j Λ K).hom := by
  have h :=
    Localization.liftTriangleVertexIso_hom_app DerivedCategory.Q
      (HomologicalComplex.quasiIso (ModuleSheaf X Λ) (.up ℤ))
      (moduleUnboundedLocalizationComplexTriangleFunctor j Λ i hcomp)
      (moduleUnboundedDerivedInverseImage Λ j ⋙ moduleUnboundedDerivedLowerShriek j Λ) (𝟭 _)
      (moduleUnboundedDerivedInverseImage Λ i ⋙ moduleUnboundedDerivedDirectImage Λ i)
      (moduleUnboundedLocalizationComplexFirstNatIso j Λ i hcomp)
      (moduleUnboundedLocalizationComplexMiddleNatIso j Λ i hcomp ≪≫ (Functor.rightUnitor _).symm)
      (moduleUnboundedLocalizationComplexThirdNatIso j Λ i hcomp)
      Triangle.π₁ (moduleUnboundedDerivedInverseImage Λ j ⋙ moduleUnboundedDerivedLowerShriek j Λ)
        (moduleUnboundedLocalizationComplexFirstNatIso j Λ i hcomp) K
  change (moduleUnboundedLocalizationFirstNatIso j Λ i hcomp).hom.app
      (DerivedCategory.Q.obj K) =
    ((moduleUnboundedLocalizationTriangleFunctorFac j Λ i hcomp).hom.app K).hom₁ ≫
      (moduleUnboundedLocalizationComplexFirstNatIso j Λ i hcomp).hom.app K at h
  have hv := Functor.isoOfSourceMap_hom_app
    (T := moduleUnboundedLocalizationComplexTriangleFunctor j Λ i hcomp ⋙ Triangle.π₁)
    (moduleUnboundedLocalizationFirstVertexNatIso j Λ) rfl (by
      apply heq_of_eq
      funext A B a
      exact moduleUnboundedLocalizationComplexTriangleMap_hom₁ j Λ i hcomp a) K
  have hc : (moduleUnboundedLocalizationComplexFirstNatIso j Λ i hcomp).hom.app K =
      (moduleUnboundedLocalizationFirstVertexIso j Λ K).hom :=
    hv.trans (Category.id_comp _)
  exact h.trans (congrArg (fun z =>
    ((moduleUnboundedLocalizationTriangleFunctorFac j Λ i hcomp).hom.app K).hom₁ ≫ z) hc)

/-- The descended middle comparison is the original factorization component. -/
@[simp]
theorem moduleUnboundedLocalizationMiddleNatIso_hom_app
    (K : CochainComplex (ModuleSheaf X Λ) ℤ) :
    (moduleUnboundedLocalizationMiddleNatIso j Λ i hcomp).hom.app (DerivedCategory.Q.obj K) =
      ((moduleUnboundedLocalizationTriangleFunctorFac j Λ i hcomp).hom.app K).hom₂ := by
  have h :=
    Localization.liftTriangleVertexIso_hom_app DerivedCategory.Q
      (HomologicalComplex.quasiIso (ModuleSheaf X Λ) (.up ℤ))
      (moduleUnboundedLocalizationComplexTriangleFunctor j Λ i hcomp)
      (moduleUnboundedDerivedInverseImage Λ j ⋙ moduleUnboundedDerivedLowerShriek j Λ) (𝟭 _)
      (moduleUnboundedDerivedInverseImage Λ i ⋙ moduleUnboundedDerivedDirectImage Λ i)
      (moduleUnboundedLocalizationComplexFirstNatIso j Λ i hcomp)
      (moduleUnboundedLocalizationComplexMiddleNatIso j Λ i hcomp ≪≫ (Functor.rightUnitor _).symm)
      (moduleUnboundedLocalizationComplexThirdNatIso j Λ i hcomp)
      Triangle.π₂ (𝟭 _)
        (moduleUnboundedLocalizationComplexMiddleNatIso j Λ i hcomp ≪≫
          (Functor.rightUnitor _).symm) K
  change (moduleUnboundedLocalizationMiddleNatIso j Λ i hcomp).hom.app (DerivedCategory.Q.obj K) =
    ((moduleUnboundedLocalizationTriangleFunctorFac j Λ i hcomp).hom.app K).hom₂ ≫
      (𝟙 _ ≫ 𝟙 _) at h
  simpa only [Category.comp_id] using h

/-- The descended closed comparison retains its original factorization on complexes. -/
@[simp]
theorem moduleUnboundedLocalizationThirdNatIso_hom_app
    (K : CochainComplex (ModuleSheaf X Λ) ℤ) :
    (moduleUnboundedLocalizationThirdNatIso j Λ i hcomp).hom.app (DerivedCategory.Q.obj K) =
      ((moduleUnboundedLocalizationTriangleFunctorFac j Λ i hcomp).hom.app K).hom₃ ≫
        (moduleUnboundedLocalizationThirdVertexIso Λ i K).hom := by
  have h :=
    Localization.liftTriangleVertexIso_hom_app DerivedCategory.Q
      (HomologicalComplex.quasiIso (ModuleSheaf X Λ) (.up ℤ))
      (moduleUnboundedLocalizationComplexTriangleFunctor j Λ i hcomp)
      (moduleUnboundedDerivedInverseImage Λ j ⋙ moduleUnboundedDerivedLowerShriek j Λ) (𝟭 _)
      (moduleUnboundedDerivedInverseImage Λ i ⋙ moduleUnboundedDerivedDirectImage Λ i)
      (moduleUnboundedLocalizationComplexFirstNatIso j Λ i hcomp)
      (moduleUnboundedLocalizationComplexMiddleNatIso j Λ i hcomp ≪≫ (Functor.rightUnitor _).symm)
      (moduleUnboundedLocalizationComplexThirdNatIso j Λ i hcomp)
      Triangle.π₃ (moduleUnboundedDerivedInverseImage Λ i ⋙ moduleUnboundedDerivedDirectImage Λ i)
        (moduleUnboundedLocalizationComplexThirdNatIso j Λ i hcomp) K
  change (moduleUnboundedLocalizationThirdNatIso j Λ i hcomp).hom.app
      (DerivedCategory.Q.obj K) =
    ((moduleUnboundedLocalizationTriangleFunctorFac j Λ i hcomp).hom.app K).hom₃ ≫
      (moduleUnboundedLocalizationComplexThirdNatIso j Λ i hcomp).hom.app K at h
  have hv := Functor.isoOfSourceMap_hom_app
    (T := moduleUnboundedLocalizationComplexTriangleFunctor j Λ i hcomp ⋙ Triangle.π₃)
    (moduleUnboundedLocalizationThirdVertexNatIso Λ i) rfl (by
      apply heq_of_eq
      funext A B a
      exact moduleUnboundedLocalizationComplexTriangleMap_hom₃ j Λ i hcomp a) K
  have hc : (moduleUnboundedLocalizationComplexThirdNatIso j Λ i hcomp).hom.app K =
      (moduleUnboundedLocalizationThirdVertexIso Λ i K).hom :=
    hv.trans (Category.id_comp _)
  exact h.trans (congrArg (fun z =>
    ((moduleUnboundedLocalizationTriangleFunctorFac j Λ i hcomp).hom.app K).hom₃ ≫ z) hc)

/-- The first descended arrow is the original derived adjunction counit, naturally. -/
theorem moduleUnboundedLocalization_counit_comparison :
    Functor.whiskerLeft (moduleUnboundedLocalizationTriangleFunctor j Λ i hcomp) Triangle.π₁Toπ₂ ≫
      (moduleUnboundedLocalizationMiddleNatIso j Λ i hcomp).hom =
    (moduleUnboundedLocalizationFirstNatIso j Λ i hcomp).hom ≫
      (moduleUnboundedDerivedLowerShriekAdjunction j Λ).counit := by
  apply Localization.natTrans_ext DerivedCategory.Q
    (HomologicalComplex.quasiIso (ModuleSheaf X Λ) (.up ℤ))
  intro K
  dsimp only [NatTrans.comp_app, Functor.whiskerLeft_app, Triangle.π₁Toπ₂_app]
  rw [moduleUnboundedLocalizationFirstNatIso_hom_app,
    moduleUnboundedLocalizationMiddleNatIso_hom_app]
  erw [Category.assoc, moduleUnboundedLocalizationFirstVertexIso_counit]
  exact ((moduleUnboundedLocalizationTriangleFunctorFac j Λ i hcomp).hom.app K).comm₁

/-- The second descended arrow is the original derived adjunction unit, naturally. -/
theorem moduleUnboundedLocalization_unit_comparison :
    Functor.whiskerLeft (moduleUnboundedLocalizationTriangleFunctor j Λ i hcomp) Triangle.π₂Toπ₃ ≫
      (moduleUnboundedLocalizationThirdNatIso j Λ i hcomp).hom =
    (moduleUnboundedLocalizationMiddleNatIso j Λ i hcomp).hom ≫
      (moduleUnboundedDerivedAdjunction Λ i).unit := by
  apply Localization.natTrans_ext DerivedCategory.Q
    (HomologicalComplex.quasiIso (ModuleSheaf X Λ) (.up ℤ))
  intro K
  dsimp only [NatTrans.comp_app, Functor.whiskerLeft_app, Triangle.π₂Toπ₃_app]
  rw [moduleUnboundedLocalizationThirdNatIso_hom_app,
    moduleUnboundedLocalizationMiddleNatIso_hom_app]
  erw [← Category.assoc,
    ((moduleUnboundedLocalizationTriangleFunctorFac j Λ i hcomp).hom.app K).comm₂,
    Category.assoc]
  change _ ≫ (DerivedCategory.Q.map
      (((moduleInverseImageAdjunction i Λ).mapHomologicalComplex (.up ℤ)).unit.app K) ≫
      (moduleUnboundedLocalizationThirdVertexIso Λ i K).hom) = _
  rw [moduleUnboundedLocalizationThirdVertexIso_unit]

/-- Localization on any original derived object, with the actual derived unit and counit. -/
def moduleUnboundedDerivedLocalizationTriangle (M : DerivedCategory (ModuleSheaf X Λ)) :
    Triangle (DerivedCategory (ModuleSheaf X Λ)) :=
  (Triangle.normalizeFunctor (moduleUnboundedLocalizationTriangleFunctor j Λ i hcomp)
    (moduleUnboundedLocalizationFirstNatIso j Λ i hcomp)
    (moduleUnboundedLocalizationThirdNatIso j Λ i hcomp)
    (moduleUnboundedDerivedLowerShriekAdjunction j Λ).counit
      (moduleUnboundedDerivedAdjunction Λ i).unit).obj M

/-- The normalization is a genuine triangle isomorphism, not a changed third vertex label. -/
def moduleUnboundedDerivedLocalizationTriangleIso (M : DerivedCategory (ModuleSheaf X Λ)) :
    (moduleUnboundedLocalizationTriangleFunctor j Λ i hcomp).obj M ≅
      moduleUnboundedDerivedLocalizationTriangle j Λ i hcomp M :=
  (Triangle.normalizeFunctorIso (moduleUnboundedLocalizationTriangleFunctor j Λ i hcomp)
    (moduleUnboundedLocalizationFirstNatIso j Λ i hcomp)
    (moduleUnboundedLocalizationMiddleNatIso j Λ i hcomp)
    (moduleUnboundedLocalizationThirdNatIso j Λ i hcomp)
    (moduleUnboundedDerivedLowerShriekAdjunction j Λ).counit
      (moduleUnboundedDerivedAdjunction Λ i).unit
    (moduleUnboundedLocalization_counit_comparison j Λ i hcomp)
      (moduleUnboundedLocalization_unit_comparison j Λ i hcomp)).app M

/-- The actual localization triangle is distinguished for every native derived object. -/
theorem moduleUnboundedDerivedLocalizationTriangle_distinguished
    (M : DerivedCategory (ModuleSheaf X Λ)) :
    moduleUnboundedDerivedLocalizationTriangle j Λ i hcomp M ∈
      distTriang (DerivedCategory (ModuleSheaf X Λ)) := by
  exact Triangle.normalizeFunctor_distinguished
    (moduleUnboundedLocalizationTriangleFunctor j Λ i hcomp)
    (moduleUnboundedLocalizationFirstNatIso j Λ i hcomp)
    (moduleUnboundedLocalizationMiddleNatIso j Λ i hcomp)
    (moduleUnboundedLocalizationThirdNatIso j Λ i hcomp)
    (moduleUnboundedDerivedLowerShriekAdjunction j Λ).counit
      (moduleUnboundedDerivedAdjunction Λ i).unit
    (moduleUnboundedLocalization_counit_comparison j Λ i hcomp)
      (moduleUnboundedLocalization_unit_comparison j Λ i hcomp)
    (moduleUnboundedLocalizationTriangleFunctor_distinguished j Λ i hcomp) M

/-- The actual localization triangles form a functor on the whole native derived category. -/
def moduleUnboundedDerivedLocalizationTriangleFunctor :
    DerivedCategory (ModuleSheaf X Λ) ⥤
      Triangle (DerivedCategory (ModuleSheaf X Λ)) :=
  Triangle.normalizeFunctor (moduleUnboundedLocalizationTriangleFunctor j Λ i hcomp)
    (moduleUnboundedLocalizationFirstNatIso j Λ i hcomp)
    (moduleUnboundedLocalizationThirdNatIso j Λ i hcomp)
    (moduleUnboundedDerivedLowerShriekAdjunction j Λ).counit
      (moduleUnboundedDerivedAdjunction Λ i).unit


/-- The shared normalized functor retains the original conjugated triangle map. -/
theorem moduleUnboundedDerivedLocalizationTriangleFunctor_map_eq_original
    {M N : DerivedCategory (ModuleSheaf X Λ)} (a : M ⟶ N) :
    (moduleUnboundedDerivedLocalizationTriangleFunctor j Λ i hcomp).map a =
      (moduleUnboundedDerivedLocalizationTriangleIso j Λ i hcomp M).inv ≫
        (moduleUnboundedLocalizationTriangleFunctor j Λ i hcomp).map a ≫
        (moduleUnboundedDerivedLocalizationTriangleIso j Λ i hcomp N).hom := by
  exact Triangle.normalizeFunctor_map_eq_original
    (moduleUnboundedLocalizationTriangleFunctor j Λ i hcomp)
    (moduleUnboundedLocalizationFirstNatIso j Λ i hcomp)
    (moduleUnboundedLocalizationMiddleNatIso j Λ i hcomp)
    (moduleUnboundedLocalizationThirdNatIso j Λ i hcomp)
    (moduleUnboundedDerivedLowerShriekAdjunction j Λ).counit
      (moduleUnboundedDerivedAdjunction Λ i).unit
    (moduleUnboundedLocalization_counit_comparison j Λ i hcomp)
      (moduleUnboundedLocalization_unit_comparison j Λ i hcomp) a

end AlgebraicGeometry.Scheme.EtaleCohomology
