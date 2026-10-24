/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

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
  NatIso.ofComponents (moduleUnboundedLocalizationFirstVertexIso j Λ) (by
    intro K L a
    change (moduleUnboundedLocalizationComplexTriangleMap j Λ i hcomp a).hom₁ ≫ _ = _
    rw [show (moduleUnboundedLocalizationComplexTriangleMap j Λ i hcomp a).hom₁ =
      DerivedCategory.Q.map (((moduleLowerShriek j Λ).mapHomologicalComplex (.up ℤ)).map
        (((moduleInverseImage j Λ).mapHomologicalComplex (.up ℤ)).map a)) from
      moduleUnboundedLocalizationComplexTriangleMap_hom₁ j Λ i hcomp a]
    exact moduleUnboundedLocalizationFirstVertexIso_naturality j Λ a)

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
  NatIso.ofComponents (moduleUnboundedLocalizationThirdVertexIso Λ i) (by
    intro K L a
    change (moduleUnboundedLocalizationComplexTriangleMap j Λ i hcomp a).hom₃ ≫ _ = _
    rw [show (moduleUnboundedLocalizationComplexTriangleMap j Λ i hcomp a).hom₃ =
      DerivedCategory.Q.map (((moduleDirectImage i Λ).mapHomologicalComplex (.up ℤ)).map
        (((moduleInverseImage i Λ).mapHomologicalComplex (.up ℤ)).map a)) from
      moduleUnboundedLocalizationComplexTriangleMap_hom₃ j Λ i hcomp a]
    exact moduleUnboundedLocalizationThirdVertexIso_naturality Λ i a)

/-- The original complex-triangle functor inverts the original quasi-isomorphisms. -/
theorem moduleUnboundedLocalizationComplexTriangleFunctor_inverts :
    (HomologicalComplex.quasiIso (ModuleSheaf X Λ) (.up ℤ)).IsInvertedBy
      (moduleUnboundedLocalizationComplexTriangleFunctor j Λ i hcomp) := by
  intro K L a ha
  let : IsIso (DerivedCategory.Q.map a) :=
    Localization.inverts DerivedCategory.Q
      (HomologicalComplex.quasiIso (ModuleSheaf X Λ) (.up ℤ)) a ha
  apply Triangle.isIso_of_isIsos
  · apply (NatIso.isIso_map_iff (moduleUnboundedLocalizationComplexFirstNatIso j Λ i hcomp) a).mpr
    change IsIso ((moduleUnboundedDerivedLowerShriek j Λ).map
      ((moduleUnboundedDerivedInverseImage Λ j).map (DerivedCategory.Q.map a)))
    infer_instance
  · exact (NatIso.isIso_map_iff (moduleUnboundedLocalizationComplexMiddleNatIso j Λ i hcomp) a).mpr
      inferInstance
  · apply (NatIso.isIso_map_iff (moduleUnboundedLocalizationComplexThirdNatIso j Λ i hcomp) a).mpr
    change IsIso ((moduleUnboundedDerivedDirectImage Λ i).map
      ((moduleUnboundedDerivedInverseImage Λ i).map (DerivedCategory.Q.map a)))
    infer_instance

/-- The native localization of the actual complex-triangle functor. -/
def moduleUnboundedLocalizationTriangleFunctor :
    DerivedCategory (ModuleSheaf X Λ) ⥤
      Triangle (DerivedCategory (ModuleSheaf X Λ)) :=
  Localization.lift (moduleUnboundedLocalizationComplexTriangleFunctor j Λ i hcomp)
    (moduleUnboundedLocalizationComplexTriangleFunctor_inverts j Λ i hcomp) DerivedCategory.Q

/-- The original native factorization comparison on arbitrary cochain complexes. -/
def moduleUnboundedLocalizationTriangleFunctorFac :
    DerivedCategory.Q ⋙ moduleUnboundedLocalizationTriangleFunctor j Λ i hcomp ≅
      moduleUnboundedLocalizationComplexTriangleFunctor j Λ i hcomp :=
  Localization.fac (moduleUnboundedLocalizationComplexTriangleFunctor j Λ i hcomp)
    (moduleUnboundedLocalizationComplexTriangleFunctor_inverts j Λ i hcomp) DerivedCategory.Q

/-- Descended triangles are distinguished; representatives only prove this property. -/
theorem moduleUnboundedLocalizationTriangleFunctor_distinguished
    (M : DerivedCategory (ModuleSheaf X Λ)) :
    (moduleUnboundedLocalizationTriangleFunctor j Λ i hcomp).obj M ∈
      distTriang (DerivedCategory (ModuleSheaf X Λ)) := by
  let Q := DerivedCategory.Q (C := ModuleSheaf X Λ)
  let : Q.EssSurj := Localization.essSurj Q
    (HomologicalComplex.quasiIso (ModuleSheaf X Λ) (.up ℤ))
  let K := Q.objPreimage M
  let e : (moduleUnboundedLocalizationTriangleFunctor j Λ i hcomp).obj M ≅
      moduleUnboundedLocalizationComplexTriangle j Λ i hcomp K :=
    (moduleUnboundedLocalizationTriangleFunctor j Λ i hcomp).mapIso (Q.objObjPreimageIso M).symm ≪≫
      (moduleUnboundedLocalizationTriangleFunctorFac j Λ i hcomp).app K
  exact isomorphic_distinguished _
    (moduleUnboundedLocalizationComplexTriangle_distinguished j Λ i hcomp K) _ e

/-- The descended first vertex is naturally the genuine derived open composite. -/
def moduleUnboundedLocalizationFirstNatIso :
    moduleUnboundedLocalizationTriangleFunctor j Λ i hcomp ⋙ Triangle.π₁ ≅
      moduleUnboundedDerivedInverseImage Λ j ⋙ moduleUnboundedDerivedLowerShriek j Λ :=
  Localization.liftNatIso DerivedCategory.Q
    (HomologicalComplex.quasiIso (ModuleSheaf X Λ) (.up ℤ)) _ _ _ _
    ((Functor.associator _ _ _).symm ≪≫
      Functor.isoWhiskerRight
        (moduleUnboundedLocalizationTriangleFunctorFac j Λ i hcomp) Triangle.π₁ ≪≫
      moduleUnboundedLocalizationComplexFirstNatIso j Λ i hcomp)

/-- The descended middle vertex is naturally the identity on the original derived category. -/
def moduleUnboundedLocalizationMiddleNatIso :
    moduleUnboundedLocalizationTriangleFunctor j Λ i hcomp ⋙ Triangle.π₂ ≅
      𝟭 (DerivedCategory (ModuleSheaf X Λ)) :=
  Localization.liftNatIso DerivedCategory.Q
    (HomologicalComplex.quasiIso (ModuleSheaf X Λ) (.up ℤ)) _ _ _ _
    ((Functor.associator _ _ _).symm ≪≫
      Functor.isoWhiskerRight
        (moduleUnboundedLocalizationTriangleFunctorFac j Λ i hcomp) Triangle.π₂ ≪≫
      moduleUnboundedLocalizationComplexMiddleNatIso j Λ i hcomp ≪≫
      (Functor.rightUnitor _).symm)

/-- The descended third vertex is naturally the genuine derived closed composite. -/
def moduleUnboundedLocalizationThirdNatIso :
    moduleUnboundedLocalizationTriangleFunctor j Λ i hcomp ⋙ Triangle.π₃ ≅
      moduleUnboundedDerivedInverseImage Λ i ⋙ moduleUnboundedDerivedDirectImage Λ i :=
  Localization.liftNatIso DerivedCategory.Q
    (HomologicalComplex.quasiIso (ModuleSheaf X Λ) (.up ℤ)) _ _ _ _
    ((Functor.associator _ _ _).symm ≪≫
      Functor.isoWhiskerRight
        (moduleUnboundedLocalizationTriangleFunctorFac j Λ i hcomp) Triangle.π₃ ≪≫
      moduleUnboundedLocalizationComplexThirdNatIso j Λ i hcomp)

/-- The descended first comparison retains its original factorization on complexes. -/
@[simp]
theorem moduleUnboundedLocalizationFirstNatIso_hom_app
    (K : CochainComplex (ModuleSheaf X Λ) ℤ) :
    (moduleUnboundedLocalizationFirstNatIso j Λ i hcomp).hom.app (DerivedCategory.Q.obj K) =
      ((moduleUnboundedLocalizationTriangleFunctorFac j Λ i hcomp).hom.app K).hom₁ ≫
        (moduleUnboundedLocalizationFirstVertexIso j Λ K).hom := by
  simp [moduleUnboundedLocalizationFirstNatIso, Localization.liftNatIso,
    Localization.liftNatTrans_app, Localization.Lifting.iso,
    moduleUnboundedLocalizationComplexFirstNatIso]
  rfl

/-- The descended middle comparison is the original factorization component. -/
@[simp]
theorem moduleUnboundedLocalizationMiddleNatIso_hom_app
    (K : CochainComplex (ModuleSheaf X Λ) ℤ) :
    (moduleUnboundedLocalizationMiddleNatIso j Λ i hcomp).hom.app (DerivedCategory.Q.obj K) =
      ((moduleUnboundedLocalizationTriangleFunctorFac j Λ i hcomp).hom.app K).hom₂ := by
  dsimp only [moduleUnboundedLocalizationMiddleNatIso, Localization.liftNatIso]
  rw [Localization.liftNatTrans_app]
  change 𝟙 _ ≫ (𝟙 _ ≫
    ((moduleUnboundedLocalizationTriangleFunctorFac j Λ i hcomp).hom.app K).hom₂ ≫
      𝟙 _ ≫ 𝟙 _) ≫ 𝟙 _ = _
  erw [Category.id_comp, Category.id_comp, Category.comp_id,
    Category.comp_id, Category.comp_id]

/-- The descended closed comparison retains its original factorization on complexes. -/
@[simp]
theorem moduleUnboundedLocalizationThirdNatIso_hom_app
    (K : CochainComplex (ModuleSheaf X Λ) ℤ) :
    (moduleUnboundedLocalizationThirdNatIso j Λ i hcomp).hom.app (DerivedCategory.Q.obj K) =
      ((moduleUnboundedLocalizationTriangleFunctorFac j Λ i hcomp).hom.app K).hom₃ ≫
        (moduleUnboundedLocalizationThirdVertexIso Λ i K).hom := by
  simp [moduleUnboundedLocalizationThirdNatIso, Localization.liftNatIso,
    Localization.liftNatTrans_app, Localization.Lifting.iso,
    moduleUnboundedLocalizationComplexThirdNatIso]
  rfl

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
  Triangle.mk ((moduleUnboundedDerivedLowerShriekAdjunction j Λ).counit.app M)
    ((moduleUnboundedDerivedAdjunction Λ i).unit.app M)
    ((moduleUnboundedLocalizationThirdNatIso j Λ i hcomp).inv.app M ≫
      ((moduleUnboundedLocalizationTriangleFunctor j Λ i hcomp).obj M).mor₃ ≫
      (shiftFunctor _ (1 : ℤ)).map ((moduleUnboundedLocalizationFirstNatIso j Λ i hcomp).hom.app M))

/-- The normalization is a genuine triangle isomorphism, not a changed third vertex label. -/
def moduleUnboundedDerivedLocalizationTriangleIso (M : DerivedCategory (ModuleSheaf X Λ)) :
    (moduleUnboundedLocalizationTriangleFunctor j Λ i hcomp).obj M ≅
      moduleUnboundedDerivedLocalizationTriangle j Λ i hcomp M := by
  refine Triangle.isoMk _ _ ((moduleUnboundedLocalizationFirstNatIso j Λ i hcomp).app M)
    ((moduleUnboundedLocalizationMiddleNatIso j Λ i hcomp).app M)
    ((moduleUnboundedLocalizationThirdNatIso j Λ i hcomp).app M) ?_ ?_ ?_
  · exact NatTrans.congr_app (moduleUnboundedLocalization_counit_comparison j Λ i hcomp) M
  · exact NatTrans.congr_app (moduleUnboundedLocalization_unit_comparison j Λ i hcomp) M
  · dsimp only [moduleUnboundedDerivedLocalizationTriangle, Triangle.mk_mor₃]
    change _ ≫ (shiftFunctor _ (1 : ℤ)).map
      ((moduleUnboundedLocalizationFirstNatIso j Λ i hcomp).hom.app M) =
      (moduleUnboundedLocalizationThirdNatIso j Λ i hcomp).hom.app M ≫
      ((moduleUnboundedLocalizationThirdNatIso j Λ i hcomp).inv.app M ≫ _)
    rw [← Category.assoc, Iso.hom_inv_id_app, Category.id_comp]
    rfl

/-- The actual localization triangle is distinguished for every native derived object. -/
theorem moduleUnboundedDerivedLocalizationTriangle_distinguished
    (M : DerivedCategory (ModuleSheaf X Λ)) :
    moduleUnboundedDerivedLocalizationTriangle j Λ i hcomp M ∈
      distTriang (DerivedCategory (ModuleSheaf X Λ)) :=
  isomorphic_distinguished _
    (moduleUnboundedLocalizationTriangleFunctor_distinguished j Λ i hcomp M)
    _ (moduleUnboundedDerivedLocalizationTriangleIso j Λ i hcomp M).symm

/-- The actual localization triangles form a functor on the whole native derived category. -/
def moduleUnboundedDerivedLocalizationTriangleFunctor :
    DerivedCategory (ModuleSheaf X Λ) ⥤
      Triangle (DerivedCategory (ModuleSheaf X Λ)) where
  obj := moduleUnboundedDerivedLocalizationTriangle j Λ i hcomp
  map {M N} a := (moduleUnboundedDerivedLocalizationTriangleIso j Λ i hcomp M).inv ≫
    (moduleUnboundedLocalizationTriangleFunctor j Λ i hcomp).map a ≫
      (moduleUnboundedDerivedLocalizationTriangleIso j Λ i hcomp N).hom
  map_id M := by
    simp only [CategoryTheory.Functor.map_id, Category.id_comp, Iso.inv_hom_id]
  map_comp a b := by
    simp only [CategoryTheory.Functor.map_comp, Category.assoc, Iso.hom_inv_id_assoc]

end AlgebraicGeometry.Scheme.EtaleCohomology
