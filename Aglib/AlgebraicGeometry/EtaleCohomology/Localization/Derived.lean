/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

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
  NatIso.ofComponents (moduleLocalizationFirstVertexIso j Λ) (by
    intro K L a
    change (moduleLocalizationComplexTriangleMap j Λ i hcomp a).hom₁ ≫ _ = _
    rw [show (moduleLocalizationComplexTriangleMap j Λ i hcomp a).hom₁ =
      DerivedCategory.Plus.Q.map ((moduleLowerShriek j Λ).mapCochainComplexPlus.map
        ((moduleInverseImage j Λ).mapCochainComplexPlus.map a)) from
      DerivedCategory.Plus.triangleOfSESPlusMap_hom₁ _ _ _]
    exact moduleLocalizationFirstVertexIso_naturality j Λ a)

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
  NatIso.ofComponents (moduleLocalizationThirdVertexIso Λ i) (by
    intro K L a
    change (moduleLocalizationComplexTriangleMap j Λ i hcomp a).hom₃ ≫ _ = _
    rw [show (moduleLocalizationComplexTriangleMap j Λ i hcomp a).hom₃ =
      DerivedCategory.Plus.Q.map ((moduleDirectImage i Λ).mapCochainComplexPlus.map
        ((moduleInverseImage i Λ).mapCochainComplexPlus.map a)) from
      DerivedCategory.Plus.triangleOfSESPlusMap_hom₃ _ _ _]
    exact moduleLocalizationThirdVertexIso_naturality Λ i a)

/-- The original complex-triangle functor inverts the original quasi-isomorphisms. -/
theorem moduleLocalizationComplexTriangleFunctor_inverts :
    (CochainComplex.Plus.quasiIso (ModuleSheaf X Λ)).IsInvertedBy
      (moduleLocalizationComplexTriangleFunctor j Λ i hcomp) := by
  intro K L a ha
  let : IsIso (DerivedCategory.Plus.Q.map a) :=
    Localization.inverts DerivedCategory.Plus.Q
      (CochainComplex.Plus.quasiIso (ModuleSheaf X Λ)) a ha
  apply Triangle.isIso_of_isIsos
  · apply (NatIso.isIso_map_iff (moduleLocalizationComplexFirstNatIso j Λ i hcomp) a).mpr
    change IsIso ((moduleDerivedLowerShriek j Λ).map
      ((moduleDerivedInverseImage Λ j).map (DerivedCategory.Plus.Q.map a)))
    infer_instance
  · exact (NatIso.isIso_map_iff (moduleLocalizationComplexMiddleNatIso j Λ i hcomp) a).mpr
      inferInstance
  · apply (NatIso.isIso_map_iff (moduleLocalizationComplexThirdNatIso j Λ i hcomp) a).mpr
    change IsIso ((moduleDerivedDirectImage Λ i).map
      ((moduleDerivedInverseImage Λ i).map (DerivedCategory.Plus.Q.map a)))
    infer_instance

/-- The native localization of the actual complex-triangle functor. -/
def moduleLocalizationTriangleFunctor :
    DerivedCategory.Plus (ModuleSheaf X Λ) ⥤
      Triangle (DerivedCategory.Plus (ModuleSheaf X Λ)) :=
  Localization.lift (moduleLocalizationComplexTriangleFunctor j Λ i hcomp)
    (moduleLocalizationComplexTriangleFunctor_inverts j Λ i hcomp) DerivedCategory.Plus.Q

/-- The original native factorization comparison on bounded-below complexes. -/
def moduleLocalizationTriangleFunctorFac :
    DerivedCategory.Plus.Q ⋙ moduleLocalizationTriangleFunctor j Λ i hcomp ≅
      moduleLocalizationComplexTriangleFunctor j Λ i hcomp :=
  Localization.fac (moduleLocalizationComplexTriangleFunctor j Λ i hcomp)
    (moduleLocalizationComplexTriangleFunctor_inverts j Λ i hcomp) DerivedCategory.Plus.Q

/-- Descended triangles are distinguished; representatives only prove this property. -/
theorem moduleLocalizationTriangleFunctor_distinguished
    (M : DerivedCategory.Plus (ModuleSheaf X Λ)) :
    (moduleLocalizationTriangleFunctor j Λ i hcomp).obj M ∈
      distTriang (DerivedCategory.Plus (ModuleSheaf X Λ)) := by
  let Q := DerivedCategory.Plus.Q (C := ModuleSheaf X Λ)
  let : Q.EssSurj := Localization.essSurj Q
    (CochainComplex.Plus.quasiIso (ModuleSheaf X Λ))
  let K := Q.objPreimage M
  let e : (moduleLocalizationTriangleFunctor j Λ i hcomp).obj M ≅
      moduleLocalizationComplexTriangle j Λ i hcomp K :=
    (moduleLocalizationTriangleFunctor j Λ i hcomp).mapIso (Q.objObjPreimageIso M).symm ≪≫
      (moduleLocalizationTriangleFunctorFac j Λ i hcomp).app K
  exact isomorphic_distinguished _ (moduleLocalizationComplexTriangle_distinguished j Λ i hcomp K)
    _ e

/-- The descended first vertex is naturally the genuine derived open composite. -/
def moduleLocalizationFirstNatIso :
    moduleLocalizationTriangleFunctor j Λ i hcomp ⋙ Triangle.π₁ ≅
      moduleDerivedInverseImage Λ j ⋙ moduleDerivedLowerShriek j Λ :=
  Localization.liftNatIso DerivedCategory.Plus.Q
    (CochainComplex.Plus.quasiIso (ModuleSheaf X Λ)) _ _ _ _
    ((Functor.associator _ _ _).symm ≪≫
      Functor.isoWhiskerRight (moduleLocalizationTriangleFunctorFac j Λ i hcomp) Triangle.π₁ ≪≫
      moduleLocalizationComplexFirstNatIso j Λ i hcomp)

/-- The descended middle vertex is naturally the identity on the original derived category. -/
def moduleLocalizationMiddleNatIso :
    moduleLocalizationTriangleFunctor j Λ i hcomp ⋙ Triangle.π₂ ≅
      𝟭 (DerivedCategory.Plus (ModuleSheaf X Λ)) :=
  Localization.liftNatIso DerivedCategory.Plus.Q
    (CochainComplex.Plus.quasiIso (ModuleSheaf X Λ)) _ _ _ _
    ((Functor.associator _ _ _).symm ≪≫
      Functor.isoWhiskerRight (moduleLocalizationTriangleFunctorFac j Λ i hcomp) Triangle.π₂ ≪≫
      moduleLocalizationComplexMiddleNatIso j Λ i hcomp ≪≫
      (Functor.rightUnitor _).symm)

/-- The descended third vertex is naturally the genuine derived closed composite. -/
def moduleLocalizationThirdNatIso :
    moduleLocalizationTriangleFunctor j Λ i hcomp ⋙ Triangle.π₃ ≅
      moduleDerivedInverseImage Λ i ⋙ moduleDerivedDirectImage Λ i :=
  Localization.liftNatIso DerivedCategory.Plus.Q
    (CochainComplex.Plus.quasiIso (ModuleSheaf X Λ)) _ _ _ _
    ((Functor.associator _ _ _).symm ≪≫
      Functor.isoWhiskerRight (moduleLocalizationTriangleFunctorFac j Λ i hcomp) Triangle.π₃ ≪≫
      moduleLocalizationComplexThirdNatIso j Λ i hcomp)

/-- The descended first comparison retains its original factorization on complexes. -/
@[simp]
theorem moduleLocalizationFirstNatIso_hom_app
    (K : CochainComplex.Plus (ModuleSheaf X Λ)) :
    (moduleLocalizationFirstNatIso j Λ i hcomp).hom.app (DerivedCategory.Plus.Q.obj K) =
      ((moduleLocalizationTriangleFunctorFac j Λ i hcomp).hom.app K).hom₁ ≫
        (moduleLocalizationFirstVertexIso j Λ K).hom := by
  simp [moduleLocalizationFirstNatIso, Localization.liftNatIso,
    Localization.liftNatTrans_app, Localization.Lifting.iso,
    moduleLocalizationComplexFirstNatIso]
  rfl

/-- The descended middle comparison is the original factorization component. -/
@[simp]
theorem moduleLocalizationMiddleNatIso_hom_app
    (K : CochainComplex.Plus (ModuleSheaf X Λ)) :
    (moduleLocalizationMiddleNatIso j Λ i hcomp).hom.app (DerivedCategory.Plus.Q.obj K) =
      ((moduleLocalizationTriangleFunctorFac j Λ i hcomp).hom.app K).hom₂ := by
  dsimp only [moduleLocalizationMiddleNatIso, Localization.liftNatIso]
  rw [Localization.liftNatTrans_app]
  change 𝟙 _ ≫ (𝟙 _ ≫
    ((moduleLocalizationTriangleFunctorFac j Λ i hcomp).hom.app K).hom₂ ≫
      𝟙 _ ≫ 𝟙 _) ≫ 𝟙 _ = _
  erw [Category.id_comp, Category.id_comp, Category.comp_id,
    Category.comp_id, Category.comp_id]

/-- The descended closed comparison retains its original factorization on complexes. -/
@[simp]
theorem moduleLocalizationThirdNatIso_hom_app
    (K : CochainComplex.Plus (ModuleSheaf X Λ)) :
    (moduleLocalizationThirdNatIso j Λ i hcomp).hom.app (DerivedCategory.Plus.Q.obj K) =
      ((moduleLocalizationTriangleFunctorFac j Λ i hcomp).hom.app K).hom₃ ≫
        (moduleLocalizationThirdVertexIso Λ i K).hom := by
  simp [moduleLocalizationThirdNatIso, Localization.liftNatIso,
    Localization.liftNatTrans_app, Localization.Lifting.iso,
    moduleLocalizationComplexThirdNatIso]
  rfl

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
  Triangle.mk ((moduleDerivedLowerShriekAdjunction j Λ).counit.app M)
    ((moduleDerivedAdjunction Λ i).unit.app M)
    ((moduleLocalizationThirdNatIso j Λ i hcomp).inv.app M ≫
      ((moduleLocalizationTriangleFunctor j Λ i hcomp).obj M).mor₃ ≫
      (shiftFunctor _ (1 : ℤ)).map ((moduleLocalizationFirstNatIso j Λ i hcomp).hom.app M))

/-- The normalization is a genuine triangle isomorphism, not a changed third vertex label. -/
def moduleDerivedLocalizationTriangleIso (M : DerivedCategory.Plus (ModuleSheaf X Λ)) :
    (moduleLocalizationTriangleFunctor j Λ i hcomp).obj M ≅
      moduleDerivedLocalizationTriangle j Λ i hcomp M := by
  refine Triangle.isoMk _ _ ((moduleLocalizationFirstNatIso j Λ i hcomp).app M)
    ((moduleLocalizationMiddleNatIso j Λ i hcomp).app M)
    ((moduleLocalizationThirdNatIso j Λ i hcomp).app M) ?_ ?_ ?_
  · exact NatTrans.congr_app (moduleLocalization_counit_comparison j Λ i hcomp) M
  · exact NatTrans.congr_app (moduleLocalization_unit_comparison j Λ i hcomp) M
  · dsimp only [moduleDerivedLocalizationTriangle, Triangle.mk_mor₃]
    change _ ≫ (shiftFunctor _ (1 : ℤ)).map
      ((moduleLocalizationFirstNatIso j Λ i hcomp).hom.app M) =
      (moduleLocalizationThirdNatIso j Λ i hcomp).hom.app M ≫
      ((moduleLocalizationThirdNatIso j Λ i hcomp).inv.app M ≫ _)
    rw [← Category.assoc, Iso.hom_inv_id_app, Category.id_comp]
    rfl

/-- The actual localization triangle is distinguished for every original bounded-below object. -/
theorem moduleDerivedLocalizationTriangle_distinguished
    (M : DerivedCategory.Plus (ModuleSheaf X Λ)) :
    moduleDerivedLocalizationTriangle j Λ i hcomp M ∈
      distTriang (DerivedCategory.Plus (ModuleSheaf X Λ)) :=
  isomorphic_distinguished _ (moduleLocalizationTriangleFunctor_distinguished j Λ i hcomp M)
    _ (moduleDerivedLocalizationTriangleIso j Λ i hcomp M).symm

/-- The actual derived localization triangles form a functor on all of the original D+. -/
def moduleDerivedLocalizationTriangleFunctor :
    DerivedCategory.Plus (ModuleSheaf X Λ) ⥤
      Triangle (DerivedCategory.Plus (ModuleSheaf X Λ)) where
  obj := moduleDerivedLocalizationTriangle j Λ i hcomp
  map {M N} a := (moduleDerivedLocalizationTriangleIso j Λ i hcomp M).inv ≫
    (moduleLocalizationTriangleFunctor j Λ i hcomp).map a ≫
      (moduleDerivedLocalizationTriangleIso j Λ i hcomp N).hom
  map_id M := by
    simp only [CategoryTheory.Functor.map_id, Category.id_comp, Iso.inv_hom_id]
  map_comp a b := by
    simp only [CategoryTheory.Functor.map_comp, Category.assoc, Iso.hom_inv_id_assoc]

end AlgebraicGeometry.Scheme.EtaleCohomology
