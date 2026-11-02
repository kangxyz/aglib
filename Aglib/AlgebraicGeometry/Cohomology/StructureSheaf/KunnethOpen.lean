/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Cohomology.StructureSheaf.ExternalProduct.MayerVietoris
public import Aglib.AlgebraicGeometry.Modules.Tensor.ExternalLinear
public import Aglib.Algebra.Homology.DerivedCategory.Ext.Bifunctor.Linear
public import Aglib.AlgebraicGeometry.Cohomology.MayerVietoris.Scalars
public import Aglib.AlgebraicGeometry.Cohomology.Modules.Ext.OpenPullback
public import Aglib.AlgebraicGeometry.Cohomology.StructureSheaf.KunnethAffineComparison

/-!
# The original mixed-open Künneth map

The ambient schemes and original product stay fixed as the second open
varies. The source is the original structure cohomology of the first factor
and the native open cohomology of the second. The target is native open
cohomology on the original inverse-image open of that same product.
The whole pairing is the original external Ext map with its actual source
and coefficient comparisons, using the original structural scalar actions.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian
open MonoidalCategory CartesianMonoidalCategory AlgebraicGeometry TopologicalSpace Opposite
open AlgebraicGeometry.Scheme.OverField AlgebraicGeometry.Scheme.Modules
open scoped TensorProduct DirectSum

universe u

universe u₁ v₁ u₂ v₂ u₃ v₃ w₁ w₂ w₃

namespace CategoryTheory.Functor

/-- Original source-arrow naturality as a whole operator before geometric specialization. -/
private theorem extBifunctorWithMaps_precomp_right
    {C : Type u₁} [Category.{v₁} C] [Abelian C] [HasExt.{w₁} C]
    {D : Type u₂} [Category.{v₂} D] [Abelian D] [HasExt.{w₂} D]
    {E : Type u₃} [Category.{v₃} E] [Abelian E] [HasExt.{w₃} E]
    (F : C ⥤ D ⥤ E) [F.Additive] [∀ A, (F.obj A).Additive]
    [∀ A, PreservesFiniteLimits (F.obj A)] [∀ A, PreservesFiniteColimits (F.obj A)]
    [∀ B, PreservesFiniteLimits (F.flip.obj B)]
    [∀ B, PreservesFiniteColimits (F.flip.obj B)]
    {X₀ X₁ : C} {Y' Y₀ Y₁ : D} {U' U V : E}
    (s : U ⟶ (F.obj X₀).obj Y₀) (s' : U' ⟶ (F.obj X₀).obj Y')
    (t : (F.obj X₁).obj Y₁ ⟶ V) (a : Y' ⟶ Y₀) (b : U' ⟶ U)
    (hs : b ≫ s = s' ≫ (F.obj X₀).map a) {p q n : ℕ} (h : p + q = n) :
    (fun (x : Ext.{w₁} X₀ X₁ p) (y : Ext.{w₂} Y₀ Y₁ q) =>
      F.extBifunctorWithMaps s' t h x ((Ext.mk₀ a).comp y (Nat.zero_add q))) =
      fun x y => (Ext.mk₀ b).comp (F.extBifunctorWithMaps s t h x y) (Nat.zero_add n) := by
  funext x y
  simp only [extBifunctorWithMaps_apply]
  rw [F.extBifunctor_mk₀_comp_right, Ext.mk₀_comp_mk₀_assoc, ← hs,
    ← Ext.comp_assoc_of_third_deg_zero, Ext.mk₀_comp_mk₀_assoc]

end CategoryTheory.Functor

namespace AlgebraicGeometry.Scheme.Cohomology

attribute [local instance] Over.cartesianMonoidalCategory

variable {k : Type u} [Field k]

/-- The existing native open cohomology object with its original structural action. -/
abbrev structureOpenCohomology (X : FScheme k) (U : X.left.Opens) (n : ℕ) : Type (u + 1) :=
  (moduleHPrimePresheaf X.left (constants X)
    (SheafOfModules.unit X.left.ringCatSheaf) n).obj (op U)

/-- The original module-open Ext comparison with the original scalar action. -/
def structureOpenExtLinearEquiv (X : FScheme k) (U : X.left.Opens) (n : ℕ) :
    letI := moduleCategoryLinearOfHom X.left (constants X)
    Ext.{u + 1} (C := X.left.Modules) (openFree X.left U)
      (SheafOfModules.unit X.left.ringCatSheaf) n ≃ₗ[k] structureOpenCohomology X U n :=
  moduleOpenExtCohomologyLinearEquiv X.left U (constants X)
    (SheafOfModules.unit X.left.ringCatSheaf) n

/-- The unchanged original native restriction map, linearly over structural constants. -/
abbrev structureOpenRestriction (X : FScheme k) {U V : X.left.Opens}
    (i : U ⟶ V) (n : ℕ) : structureOpenCohomology X V n →ₗ[k] structureOpenCohomology X U n :=
  ((moduleHPrimePresheaf X.left (constants X)
    (SheafOfModules.unit X.left.ringCatSheaf) n).map i.op).hom

/-- The unchanged original unsigned native Mayer–Vietoris boundary. -/
abbrev structureOpenMayerVietorisDelta (X : FScheme k) (U V : X.left.Opens) (n : ℕ) :
    structureOpenCohomology X (U ⊓ V) n →ₗ[k] structureOpenCohomology X (U ⊔ V) (n + 1) :=
  (moduleMayerVietorisDelta X.left (constants X)
    (SheafOfModules.unit X.left.ringCatSheaf) U V n).hom

variable (X Y : FScheme k)

/-- The whole original open-source coefficient arrow is exactly the native
pullback coefficient arrow, through the same original unit comparisons. -/
theorem structureExternalOpenSourceIso_coefficient (U : Y.left.Opens)
    (g : openFree Y.left U ⟶ SheafOfModules.unit Y.left.ringCatSheaf) :
    ((structureExternalOpenSourceIso X Y).app U).inv ≫
        ((externalTensor X.hom Y.hom).obj (SheafOfModules.unit X.left.ringCatSheaf)).map g ≫
          (externalTensorUnitIso X.hom Y.hom).hom =
      (openFreePullbackIso (snd X Y).left U).inv ≫
        (Scheme.Modules.pullback (snd X Y).left).map g ≫
          (pullbackUnitIso (snd X Y).left).hom := by
  let L := externalTensorLeftUnitIso X.hom Y.hom
  let c := openFreePullbackIso (snd X Y).left U
  have hs : ((structureExternalOpenSourceIso X Y).app U).inv =
      c.inv ≫ L.inv.app (openFree Y.left U) := rfl
  have he : (externalTensorUnitIso X.hom Y.hom).hom =
      L.hom.app (SheafOfModules.unit Y.left.ringCatSheaf) ≫
        (pullbackUnitIso (snd X Y).left).hom := rfl
  have hn := L.inv.naturality g
  change (Scheme.Modules.pullback (snd X Y).left).map g ≫
      L.inv.app (SheafOfModules.unit Y.left.ringCatSheaf) =
    L.inv.app (openFree Y.left U) ≫
      ((externalTensor X.hom Y.hom).obj (SheafOfModules.unit X.left.ringCatSheaf)).map g at hn
  rw [hs, he]
  calc
    _ = c.inv ≫
        (L.inv.app (openFree Y.left U) ≫
          ((externalTensor X.hom Y.hom).obj (SheafOfModules.unit X.left.ringCatSheaf)).map g) ≫
        L.hom.app (SheafOfModules.unit Y.left.ringCatSheaf) ≫
        (pullbackUnitIso (snd X Y).left).hom := by simp only [Category.assoc]
    _ = c.inv ≫
        ((Scheme.Modules.pullback (snd X Y).left).map g ≫
          L.inv.app (SheafOfModules.unit Y.left.ringCatSheaf)) ≫
        L.hom.app (SheafOfModules.unit Y.left.ringCatSheaf) ≫
        (pullbackUnitIso (snd X Y).left).hom := by rw [← hn]
    _ = _ := by
      simp only [Category.assoc, Iso.inv_hom_id_app_assoc]
      rfl

/-- At the whole space the entire original source comparison is normalized
by the original universal map on one. -/
theorem structureExternalOpenSourceIso_top_unit :
    ((structureExternalOpenSourceIso X Y).app ⊤).inv ≫
        ((externalTensor X.hom Y.hom).obj (SheafOfModules.unit X.left.ringCatSheaf)).map
          (moduleOpenTopUnitMap Y.left) ≫
        (externalTensorUnitIso X.hom Y.hom).hom = moduleOpenTopUnitMap (X ⊗ Y).left := by
  rw [structureExternalOpenSourceIso_coefficient]
  have h := moduleOpenTopUnitMap_pullback (snd X Y).left
  rw [← h, ← Category.assoc, Iso.inv_hom_id, Category.id_comp]

/-- Original open restriction is the original precomposition on the
actual mixed external Ext operator. -/
theorem structureExternalOpenExt_restriction {U V : Y.left.Opens} (i : U ⟶ V)
    {p q n : ℕ} (h : p + q = n)
    (x : Ext.{u + 1} (C := X.left.Modules) (SheafOfModules.unit X.left.ringCatSheaf)
      (SheafOfModules.unit X.left.ringCatSheaf) p)
    (y : Ext.{u + 1} (C := Y.left.Modules) (openFree Y.left V)
      (SheafOfModules.unit Y.left.ringCatSheaf) q) :
    structureExternalOpenExt X Y U h x
        ((Ext.mk₀ ((openFreeFunctor Y.left).map i)).comp y (Nat.zero_add q)) =
      (Ext.mk₀ ((openFreeFunctor (X ⊗ Y).left).map
        ((Opens.map (snd X Y).left.base).map i))).comp
          (structureExternalOpenExt X Y V h x y) (Nat.zero_add n) := by
  have hs := (structureExternalOpenSourceIso X Y).inv.naturality i
  change (openFreeFunctor (X ⊗ Y).left).map ((Opens.map (snd X Y).left.base).map i) ≫
      ((structureExternalOpenSourceIso X Y).app V).inv =
    ((structureExternalOpenSourceIso X Y).app U).inv ≫
      ((externalTensor X.hom Y.hom).obj (SheafOfModules.unit X.left.ringCatSheaf)).map
        ((openFreeFunctor Y.left).map i) at hs
  have hOperator := (externalTensor X.hom Y.hom).extBifunctorWithMaps_precomp_right
    ((structureExternalOpenSourceIso X Y).app V).inv
    ((structureExternalOpenSourceIso X Y).app U).inv
    (externalTensorUnitIso X.hom Y.hom).hom ((openFreeFunctor Y.left).map i)
    ((openFreeFunctor (X ⊗ Y).left).map ((Opens.map (snd X Y).left.base).map i)) hs h
  exact congrFun (congrFun hOperator x) y

/-- The original mixed-open external cup, as one complete bilinear operator. -/
def structureExternalOpenCup (U : Y.left.Opens) {p q n : ℕ} (h : p + q = n) :
    structureCohomology k X p →ₗ[k] structureOpenCohomology Y U q →ₗ[k]
      structureOpenCohomology (X ⊗ Y) ((snd X Y).left ⁻¹ᵁ U) n := by
  letI := moduleCategoryLinearOfHom X.left (constants X)
  letI := moduleCategoryLinearOfHom Y.left (constants Y)
  let categoryScalars := moduleCategoryLinearOfHom (X ⊗ Y).left (constants (X ⊗ Y))
  letI : CategoryTheory.Linear k (X ⊗ Y).left.Modules := categoryScalars
  letI : CategoryTheory.Linear k (Limits.pullback X.hom Y.hom).Modules := categoryScalars
  letI (M : X.left.Modules) : ((externalTensor X.hom Y.hom).obj M).Linear k :=
    externalTensor_obj_linearOfHom X.hom Y.hom (constants Y) (constants (X ⊗ Y))
      (by ext a; exact map_constants (snd X Y) a) M
  letI (N : Y.left.Modules) : ((externalTensor X.hom Y.hom).flip.obj N).Linear k :=
    externalTensor_flip_obj_linearOfHom X.hom Y.hom (constants X) (constants (X ⊗ Y))
      (by ext a; exact map_constants (fst X Y) a) N
  exact (((externalTensor X.hom Y.hom).extBifunctorLinearMapWithMaps (R := k)
      ((structureExternalOpenSourceIso X Y).app U).inv
      (externalTensorUnitIso X.hom Y.hom).hom h).compl₁₂
    (structureExtLinearEquiv X p).symm.toLinearMap
    (structureOpenExtLinearEquiv Y U q).symm.toLinearMap).compr₂
      (structureOpenExtLinearEquiv (X ⊗ Y) ((snd X Y).left ⁻¹ᵁ U) n).toLinearMap

/-- The forward value is the original external Ext map and original open comparisons. -/
theorem structureExternalOpenCup_apply (U : Y.left.Opens) {p q n : ℕ} (h : p + q = n)
    (x : structureCohomology k X p) (y : structureOpenCohomology Y U q) :
    structureExternalOpenCup X Y U h x y =
      moduleOpenExtCohomologyMap (X ⊗ Y).left ((snd X Y).left ⁻¹ᵁ U)
        (SheafOfModules.unit (X ⊗ Y).left.ringCatSheaf) n
        (structureExternalOpenExt X Y U h ((structureExtLinearEquiv X p).symm x)
          ((structureOpenExtLinearEquiv Y U q).symm y)) := rfl

/-- The original tensor of the two original cohomology factors. -/
def structureExternalOpenTensor (U : Y.left.Opens) {p q n : ℕ} (h : p + q = n) :
    structureCohomology k X p ⊗[k] structureOpenCohomology Y U q →ₗ[k]
      structureOpenCohomology (X ⊗ Y) ((snd X Y).left ⁻¹ᵁ U) n :=
  TensorProduct.lift (structureExternalOpenCup X Y U h)

theorem structureExternalOpenTensor_tmul (U : Y.left.Opens) {p q n : ℕ} (h : p + q = n)
    (x : structureCohomology k X p) (y : structureOpenCohomology Y U q) :
    structureExternalOpenTensor X Y U h (x ⊗ₜ[k] y) =
      structureExternalOpenCup X Y U h x y := rfl

/-- The original finite-antidiagonal source with only the second open varying. -/
abbrev structureOpenKunnethSum (U : Y.left.Opens) (n : ℕ) : Type (u + 1) :=
  ⨁ s : HomologicalComplex₂.TotalDegree n,
    structureCohomology k X s.val.1 ⊗[k] structureOpenCohomology Y U s.val.2

/-- The actual mixed-open Künneth map on the original product-open target. -/
def structureOpenKunnethMap (U : Y.left.Opens) (n : ℕ) :
    structureOpenKunnethSum X Y U n →ₗ[k]
      structureOpenCohomology (X ⊗ Y) ((snd X Y).left ⁻¹ᵁ U) n :=
  DirectSum.toModule k _ _ (fun s : HomologicalComplex₂.TotalDegree n =>
    structureExternalOpenTensor X Y U s.property)

theorem structureOpenKunnethMap_lof (U : Y.left.Opens) (n : ℕ)
    (s : HomologicalComplex₂.TotalDegree n)
    (x : structureCohomology k X s.val.1 ⊗[k] structureOpenCohomology Y U s.val.2) :
    structureOpenKunnethMap X Y U n (DirectSum.lof k _ _ s x) =
      structureExternalOpenTensor X Y U s.property x := by
  classical
  exact DirectSum.toModule_lof
    (φ := fun t : HomologicalComplex₂.TotalDegree n =>
      structureExternalOpenTensor X Y U t.property) k s x

/-- The actual unsigned native source boundary crosses the first degree with (-1)^p. -/
theorem structureExternalOpenCup_mayerVietoris (U V : Y.left.Opens)
    {p q n : ℕ} (h : p + q = n) (x : structureCohomology k X p)
    (y : structureOpenCohomology Y (U ⊓ V) q) :
    structureExternalOpenCup X Y (U ⊔ V) (show p + (q + 1) = n + 1 by omega) x
        (structureOpenMayerVietorisDelta Y U V q y) =
      ((-1 : ℤ) ^ p) •
        structureOpenMayerVietorisDelta (X ⊗ Y)
          ((snd X Y).left ⁻¹ᵁ U) ((snd X Y).left ⁻¹ᵁ V) n
          (structureExternalOpenCup X Y (U ⊓ V) h x y) := by
  rw [structureExternalOpenCup_apply, structureExternalOpenCup_apply]
  change moduleOpenExtCohomologyMap (X ⊗ Y).left ((snd X Y).left ⁻¹ᵁ (U ⊔ V))
      (SheafOfModules.unit (X ⊗ Y).left.ringCatSheaf) (n + 1)
      (structureExternalOpenExt X Y (U ⊔ V) _ ((structureExtLinearEquiv X p).symm x)
        ((moduleOpenExtCohomologyAddEquiv Y.left (U ⊔ V)
          (SheafOfModules.unit Y.left.ringCatSheaf) (q + 1)).symm
            ((Opens.mayerVietorisSquare U V).δ
              (moduleAddSheaf Y.left (SheafOfModules.unit Y.left.ringCatSheaf))
              q (q + 1) rfl y))) = _
  rw [moduleOpenExtCohomologyAddEquiv_symm_mayerVietorisDelta]
  exact structureExternalOpenExt_mayerVietoris_cohomology X Y U V h
    ((structureExtLinearEquiv X p).symm x)
    ((moduleOpenExtCohomologyAddEquiv Y.left (U ⊓ V)
      (SheafOfModules.unit Y.left.ringCatSheaf) q).symm y)

end AlgebraicGeometry.Scheme.Cohomology
