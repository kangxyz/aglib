/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Cohomology.StructureSheaf.ExternalProduct.Ext
public import Aglib.AlgebraicGeometry.Cohomology.Modules.Ext.MayerVietoris
public import Aglib.AlgebraicGeometry.Modules.Generators.Pullback
public import Mathlib.Algebra.Homology.CommSq
public import Mathlib.CategoryTheory.Square

/-!
# The original external product and the Mayer–Vietoris source class

The original open-free pullback comparison gives an actual morphism of the
two module Mayer–Vietoris sequences. The genuine biexact external Ext product
then carries the unsigned source connecting class in the second factor with
sign (-1)^p. The final equation uses the original native H' connecting map.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian
open MonoidalCategory CartesianMonoidalCategory AlgebraicGeometry TopologicalSpace Opposite
open AlgebraicGeometry.Scheme.OverField AlgebraicGeometry.Scheme.Modules

universe u u₁ u₂ u₃ v₁ v₂ v₃ w₁ w₂ w₃

namespace CategoryTheory.Square

variable {C : Type u₁} [Category.{v₁} C] [Preadditive C]
  {D : Type u₂} [Category.{v₂} D] [Preadditive D]
  (F : C ⥤ D) [F.Additive] (S : Square C) (T : Square D)
  [HasBinaryBiproduct S.X₂ S.X₃] [HasBinaryBiproduct T.X₂ T.X₃]

/-- The original commuting cube gives the original difference/sum short-complex
morphism after any additive functor. Preservation of biproducts is not an input. -/
@[simps]
def shortComplexMapOfMap (τ : T ⟶ S.map F) :
    T.commSq.shortComplex ⟶ S.commSq.shortComplex.map F where
  τ₁ := τ.τ₁
  τ₂ := biprod.desc (τ.τ₂ ≫ F.map biprod.inl) (τ.τ₃ ≫ F.map biprod.inr)
  τ₃ := τ.τ₄
  comm₁₂ := by
    change τ.τ₁ ≫ F.map (biprod.lift S.f₁₂ (-S.f₁₃)) =
      biprod.lift T.f₁₂ (-T.f₁₃) ≫
        biprod.desc (τ.τ₂ ≫ F.map biprod.inl) (τ.τ₃ ≫ F.map biprod.inr)
    rw [biprod.lift_desc]
    simp only [biprod.lift_eq, CategoryTheory.Functor.map_add,
      CategoryTheory.Functor.map_comp, CategoryTheory.Functor.map_neg,
      Preadditive.comp_add, Preadditive.comp_neg, Preadditive.neg_comp, ← Category.assoc]
    rw [τ.comm₁₂, τ.comm₁₃]
    rfl
  comm₂₃ := by
    change biprod.desc (τ.τ₂ ≫ F.map biprod.inl) (τ.τ₃ ≫ F.map biprod.inr) ≫
        F.map (biprod.desc S.f₂₄ S.f₃₄) = biprod.desc T.f₂₄ T.f₃₄ ≫ τ.τ₄
    apply biprod.hom_ext'
    · simp only [biprod.inl_desc_assoc, Category.assoc,
        ← CategoryTheory.Functor.map_comp, biprod.inl_desc]
      exact τ.comm₂₄.symm
    · simp only [biprod.inr_desc_assoc, Category.assoc,
        ← CategoryTheory.Functor.map_comp, biprod.inr_desc]
      exact τ.comm₃₄.symm

end CategoryTheory.Square

namespace CategoryTheory

private theorem additive_preservesZeroMorphisms_at
    {C : Type u₁} [Category.{v₁} C] [Preadditive C]
    {D : Type u₂} [Category.{v₂} D] [Preadditive D]
    (F : C ⥤ D) [F.Additive] (sourceZero : HasZeroMorphisms C)
    (targetZero : HasZeroMorphisms D) :
    @Functor.PreservesZeroMorphisms C inferInstance D inferInstance sourceZero targetZero F := by
  let nativeSourceZero : HasZeroMorphisms C :=
    @Preadditive.preadditiveHasZeroMorphisms C inferInstance inferInstance
  let nativeTargetZero : HasZeroMorphisms D :=
    @Preadditive.preadditiveHasZeroMorphisms D inferInstance inferInstance
  let preserves (s : HasZeroMorphisms C) (t : HasZeroMorphisms D) : Prop :=
    @Functor.PreservesZeroMorphisms C inferInstance D inferInstance s t F
  have native : preserves nativeSourceZero nativeTargetZero :=
    ⟨fun A B => (F.mapAddHom (X := A) (Y := B)).map_zero⟩
  exact Eq.mp (congrArg₂ preserves (Subsingleton.elim nativeSourceZero sourceZero)
    (Subsingleton.elim nativeTargetZero targetZero)) native

end CategoryTheory

namespace CategoryTheory.Abelian.Ext

private theorem endpoint_zsmul
    {E : Type u₃} [Category.{v₃} E] [Abelian E] [HasExt.{w₃} E]
    {U A B V : E} (s : U ⟶ A) (t : B ⟶ V) {n : ℕ} (c : ℤ) (z : Ext A B n) :
    ((Ext.mk₀ s).comp (c • z) (Nat.zero_add n)).comp (Ext.mk₀ t) (Nat.add_zero n) =
      c • (((Ext.mk₀ s).comp z (Nat.zero_add n)).comp (Ext.mk₀ t) (Nat.add_zero n)) :=
  _root_.map_zsmul (((Ext.mk₀ t).postcomp U (Nat.add_zero n)).comp
    ((Ext.mk₀ s).precomp B (Nat.zero_add n))) c z

private theorem sourceClass_precomp_postcomp
    {E : Type u₃} [Category.{v₃} E] [Abelian E] [HasExt.{w₃} E]
    {S T : ShortComplex E} (hS : S.ShortExact) (hT : T.ShortExact) (τ : T ⟶ S)
    {V W : E} {n n' : ℕ} (h : 1 + n = n') (z : Ext S.X₁ V n) (t : V ⟶ W) :
    ((Ext.mk₀ τ.τ₃).comp (hS.extClass.comp z h) (Nat.zero_add n')).comp
        (Ext.mk₀ t) (Nat.add_zero n') =
      hT.extClass.comp
        (((Ext.mk₀ τ.τ₁).comp z (Nat.zero_add n)).comp (Ext.mk₀ t) (Nat.add_zero n)) h := by
  rw [← Ext.comp_assoc (Ext.mk₀ τ.τ₃) hS.extClass z (Nat.zero_add 1) h (by omega),
    ← hT.extClass_naturality hS τ, Ext.comp_assoc_of_second_deg_zero,
    Ext.comp_assoc_of_third_deg_zero]

end CategoryTheory.Abelian.Ext

namespace CategoryTheory.Functor

variable {C : Type u₁} [Category.{v₁} C] [Abelian C] [HasExt.{w₁} C]
  {D : Type u₂} [Category.{v₂} D] [Abelian D] [HasExt.{w₂} D]
  {E : Type u₃} [Category.{v₃} E] [Abelian E] [HasExt.{w₃} E]
  (F : C ⥤ D ⥤ E) [F.Additive] [∀ X, (F.obj X).Additive]
  [∀ X, PreservesFiniteLimits (F.obj X)] [∀ X, PreservesFiniteColimits (F.obj X)]
  [∀ Y, PreservesFiniteLimits (F.flip.obj Y)]
  [∀ Y, PreservesFiniteColimits (F.flip.obj Y)]

/-- The original external Ext product with actual source and coefficient arrows.
The entire construction is the original biadditive map and native Ext composition. -/
def extBifunctorWithMaps {X₀ X₁ : C} {Y₀ Y₁ : D} {U V : E}
    (s : U ⟶ (F.obj X₀).obj Y₀) (t : (F.obj X₁).obj Y₁ ⟶ V)
    {p q n : ℕ} (h : p + q = n) :
    Ext.{w₁} X₀ X₁ p →+ Ext.{w₂} Y₀ Y₁ q →+ Ext.{w₃} U V n :=
  (F.extBifunctorHom X₀ X₁ Y₀ Y₁ p q n h).compr₂
    (((Ext.mk₀ t).postcomp U (Nat.add_zero n)).comp
      ((Ext.mk₀ s).precomp ((F.obj X₁).obj Y₁) (Nat.zero_add n)))

@[simp]
theorem extBifunctorWithMaps_apply {X₀ X₁ : C} {Y₀ Y₁ : D} {U V : E}
    (s : U ⟶ (F.obj X₀).obj Y₀) (t : (F.obj X₁).obj Y₁ ⟶ V)
    {p q n : ℕ} (h : p + q = n) (x : Ext.{w₁} X₀ X₁ p) (y : Ext.{w₂} Y₀ Y₁ q) :
    F.extBifunctorWithMaps s t h x y =
      ((Ext.mk₀ s).comp (F.extBifunctor x y h) (Nat.zero_add n)).comp
        (Ext.mk₀ t) (Nat.add_zero n) := rfl

/-- An actual morphism of the original source sequences gives the signed
second-source boundary law, with the original unsigned extension classes. -/
theorem extBifunctorWithMaps_source_extClass_right
    {X₀ X₁ : C} {S : ShortComplex D} (hS : S.ShortExact)
    {T : ShortComplex E} (hT : T.ShortExact) (τ : T ⟶ S.map (F.obj X₀))
    {Y₁ : D} {V : E} (t : (F.obj X₁).obj Y₁ ⟶ V)
    {p q n : ℕ} (h : p + q = n)
    (x : Ext.{w₁} X₀ X₁ p) (y : Ext.{w₂} S.X₁ Y₁ q) :
    F.extBifunctorWithMaps τ.τ₃ t (show p + (q + 1) = n + 1 by omega) x
        (hS.extClass.comp y (Nat.add_comm 1 q)) =
      ((-1 : ℤ) ^ p) • hT.extClass.comp
        (F.extBifunctorWithMaps τ.τ₁ t h x y) (Nat.add_comm 1 n) := by
  simp only [extBifunctorWithMaps_apply]
  rw [F.extBifunctor_extClass_comp_right hS x y (Nat.add_comm 1 q) h (by omega),
    Ext.endpoint_zsmul]
  exact congrArg (((-1 : ℤ) ^ p) • ·)
    (Ext.sourceClass_precomp_postcomp (hS.map_of_exact (F.obj X₀)) hT τ
      (Nat.add_comm 1 n) (F.extBifunctor x y h) t)

end CategoryTheory.Functor

namespace AlgebraicGeometry.Scheme.Cohomology

attribute [local instance] Over.cartesianMonoidalCategory

variable {k : Type u} [Field k] (X Y : FScheme k)

local instance externalTensorUnit_preservesZeroMorphisms
    [sourceZero : HasZeroMorphisms Y.left.Modules]
    [targetZero : HasZeroMorphisms (X ⊗ Y).left.Modules] :
    @Functor.PreservesZeroMorphisms Y.left.Modules inferInstance (X ⊗ Y).left.Modules
      inferInstance sourceZero targetZero
        ((externalTensor X.hom Y.hom).obj (SheafOfModules.unit X.left.ringCatSheaf)) := by
  exact additive_preservesZeroMorphisms_at
    ((externalTensor X.hom Y.hom).obj (SheafOfModules.unit X.left.ringCatSheaf))
    sourceZero targetZero

/-- One whole comparison of the actual external tensor with an open-free
second factor and the original free module on the inverse-image open. -/
def structureExternalOpenSourceIso :
    openFreeFunctor Y.left ⋙
        (externalTensor X.hom Y.hom).obj (SheafOfModules.unit X.left.ringCatSheaf) ≅
      Opens.map (snd X Y).left.base ⋙ openFreeFunctor (X ⊗ Y).left :=
  Functor.isoWhiskerLeft (openFreeFunctor Y.left) (externalTensorLeftUnitIso X.hom Y.hom) ≪≫
    openFreePullbackNatIso (snd X Y).left

/-- The actual inverse source comparisons form the commuting cube of open-free modules. -/
def structureExternalMayerVietorisSquareMap (U V : Y.left.Opens) :
    ((Opens.mayerVietorisSquare ((snd X Y).left ⁻¹ᵁ U) ((snd X Y).left ⁻¹ᵁ V)).toSquare.map
      (openFreeFunctor (X ⊗ Y).left)) ⟶
        (((Opens.mayerVietorisSquare U V).toSquare.map (openFreeFunctor Y.left)).map
          ((externalTensor X.hom Y.hom).obj (SheafOfModules.unit X.left.ringCatSheaf))) :=
  (NatTrans.mapSquare (structureExternalOpenSourceIso X Y).inv).app
    (Opens.mayerVietorisSquare U V).toSquare

/-- The actual source Mayer–Vietoris short-complex morphism for the external tensor.
Its middle arrow is the canonical sum of the two original coefficient arrows. -/
def structureExternalMayerVietorisMap (U V : Y.left.Opens) :
    moduleOpenMayerVietorisShortComplex (X ⊗ Y).left
        ((snd X Y).left ⁻¹ᵁ U) ((snd X Y).left ⁻¹ᵁ V) ⟶
      (moduleOpenMayerVietorisShortComplex Y.left U V).map
        ((externalTensor X.hom Y.hom).obj (SheafOfModules.unit X.left.ringCatSheaf)) :=
  Square.shortComplexMapOfMap
    ((externalTensor X.hom Y.hom).obj (SheafOfModules.unit X.left.ringCatSheaf))
    ((Opens.mayerVietorisSquare U V).toSquare.map (openFreeFunctor Y.left))
    ((Opens.mayerVietorisSquare ((snd X Y).left ⁻¹ᵁ U) ((snd X Y).left ⁻¹ᵁ V)).toSquare.map
      (openFreeFunctor (X ⊗ Y).left))
    (structureExternalMayerVietorisSquareMap X Y U V)

@[simp]
theorem structureExternalMayerVietorisMap_τ₁ (U V : Y.left.Opens) :
    (structureExternalMayerVietorisMap X Y U V).τ₁ =
      ((structureExternalOpenSourceIso X Y).app (U ⊓ V)).inv := rfl

@[simp]
theorem structureExternalMayerVietorisMap_τ₃ (U V : Y.left.Opens) :
    (structureExternalMayerVietorisMap X Y U V).τ₃ =
      ((structureExternalOpenSourceIso X Y).app (U ⊔ V)).inv := rfl

/-- The genuine external Ext pairing with the original open-free source and
original structure-module target, normalized by the actual two source/unit maps. -/
def structureExternalOpenExt (U : Y.left.Opens) {p q n : ℕ} (h : p + q = n) :
    Ext.{u + 1} (C := X.left.Modules) (SheafOfModules.unit X.left.ringCatSheaf)
        (SheafOfModules.unit X.left.ringCatSheaf) p →+
      Ext.{u + 1} (C := Y.left.Modules) (openFree Y.left U)
        (SheafOfModules.unit Y.left.ringCatSheaf) q →+
        Ext.{u + 1} (C := (X ⊗ Y).left.Modules) (openFree (X ⊗ Y).left ((snd X Y).left ⁻¹ᵁ U))
          (SheafOfModules.unit (X ⊗ Y).left.ringCatSheaf) n :=
  (externalTensor X.hom Y.hom).extBifunctorWithMaps
    (X₀ := SheafOfModules.unit X.left.ringCatSheaf)
    (X₁ := SheafOfModules.unit X.left.ringCatSheaf)
    (Y₀ := openFree Y.left U) (Y₁ := SheafOfModules.unit Y.left.ringCatSheaf)
    ((structureExternalOpenSourceIso X Y).app U).inv (externalTensorUnitIso X.hom Y.hom).hom h

/-- The actual module-open Mayer–Vietoris source boundary crosses degree p
with exactly (-1)^p. No signed-Ext-delta convention is substituted. -/
theorem structureExternalOpenExt_mayerVietoris (U V : Y.left.Opens)
    {p q n : ℕ} (h : p + q = n)
    (x : Ext.{u + 1} (C := X.left.Modules) (SheafOfModules.unit X.left.ringCatSheaf)
      (SheafOfModules.unit X.left.ringCatSheaf) p)
    (y : Ext.{u + 1} (C := Y.left.Modules) (openFree Y.left (U ⊓ V))
      (SheafOfModules.unit Y.left.ringCatSheaf) q) :
    structureExternalOpenExt X Y (U ⊔ V) (show p + (q + 1) = n + 1 by omega) x
        ((moduleOpenMayerVietoris_shortExact Y.left U V).extClass.comp y (Nat.add_comm 1 q)) =
      ((-1 : ℤ) ^ p) •
        (moduleOpenMayerVietoris_shortExact (X ⊗ Y).left
          ((snd X Y).left ⁻¹ᵁ U) ((snd X Y).left ⁻¹ᵁ V)).extClass.comp
          (structureExternalOpenExt X Y (U ⊓ V) h x y) (Nat.add_comm 1 n) :=
  (externalTensor X.hom Y.hom).extBifunctorWithMaps_source_extClass_right
    (moduleOpenMayerVietoris_shortExact Y.left U V)
    (moduleOpenMayerVietoris_shortExact (X ⊗ Y).left
      ((snd X Y).left ⁻¹ᵁ U) ((snd X Y).left ⁻¹ᵁ V))
    (structureExternalMayerVietorisMap X Y U V) (externalTensorUnitIso X.hom Y.hom).hom h x y

/-- The same equation is about the actual original H' connecting map on the
product opens, with the native unsigned source convention and its Koszul factor. -/
theorem structureExternalOpenExt_mayerVietoris_cohomology (U V : Y.left.Opens)
    {p q n : ℕ} (h : p + q = n)
    (x : Ext.{u + 1} (C := X.left.Modules) (SheafOfModules.unit X.left.ringCatSheaf)
      (SheafOfModules.unit X.left.ringCatSheaf) p)
    (y : Ext.{u + 1} (C := Y.left.Modules) (openFree Y.left (U ⊓ V))
      (SheafOfModules.unit Y.left.ringCatSheaf) q) :
    moduleOpenExtCohomologyMap (X ⊗ Y).left ((snd X Y).left ⁻¹ᵁ (U ⊔ V))
        (SheafOfModules.unit (X ⊗ Y).left.ringCatSheaf) (n + 1)
        (structureExternalOpenExt X Y (U ⊔ V) (show p + (q + 1) = n + 1 by omega) x
          ((moduleOpenMayerVietoris_shortExact Y.left U V).extClass.comp y
            (Nat.add_comm 1 q))) =
      ((-1 : ℤ) ^ p) •
        (Opens.mayerVietorisSquare ((snd X Y).left ⁻¹ᵁ U) ((snd X Y).left ⁻¹ᵁ V)).δ
          (moduleAddSheaf (X ⊗ Y).left (SheafOfModules.unit (X ⊗ Y).left.ringCatSheaf))
          n (n + 1) rfl
          (moduleOpenExtCohomologyMap (X ⊗ Y).left ((snd X Y).left ⁻¹ᵁ (U ⊓ V))
            (SheafOfModules.unit (X ⊗ Y).left.ringCatSheaf) n
            (structureExternalOpenExt X Y (U ⊓ V) h x y)) := by
  have hmap := congrArg
    (moduleOpenExtCohomologyMap (X ⊗ Y).left ((snd X Y).left ⁻¹ᵁ (U ⊔ V))
      (SheafOfModules.unit (X ⊗ Y).left.ringCatSheaf) (n + 1))
    (structureExternalOpenExt_mayerVietoris X Y U V h x y)
  rw [map_zsmul] at hmap
  have hdelta := moduleOpenExtCohomologyMap_mayerVietorisDelta (X ⊗ Y).left
    ((snd X Y).left ⁻¹ᵁ U) ((snd X Y).left ⁻¹ᵁ V)
    (SheafOfModules.unit (X ⊗ Y).left.ringCatSheaf) n
    (structureExternalOpenExt X Y (U ⊓ V) h x y)
  exact hmap.trans (congrArg (((-1 : ℤ) ^ p) • ·) hdelta)

end AlgebraicGeometry.Scheme.Cohomology
