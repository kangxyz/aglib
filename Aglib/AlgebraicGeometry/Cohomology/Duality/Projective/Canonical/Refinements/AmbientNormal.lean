/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Cohomology.Duality.Projective.Canonical.Refinements.NormalBase
public import Aglib.AlgebraicGeometry.Cohomology.Duality.Projective.Canonical.Refinements.OpenCoefficient.Units
public import Aglib.AlgebraicGeometry.IdealSheaf.BaseChange.Isomorphism

/-!
# Original normal classes on an ambient isomorphism square

The comparison is the original mixed pullback square followed by the
original ideal pullback map. Kernel elements are compared through their
actual ideal inclusions and the native structure-module units.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory AlgebraicGeometry Opposite
open AlgebraicGeometry.Scheme.Hom
open AlgebraicGeometry.Scheme.Modules.Differentials
open scoped TensorProduct ChangeOfRings

universe u
namespace AlgebraicGeometry.Scheme.Modules

/-- The original ideal pullback map, with open restriction as its source. -/
def canonicalIdealOpenSquareMap
    {X Y D D' : Scheme.{u}} (i : D ⟶ X) (i' : D' ⟶ Y)
    (j : Y ⟶ X) (p : D' ⟶ D) [IsOpenImmersion j]
    (h : p ≫ i = i' ≫ j) :
    (idealModule i).restrict j ⟶ idealModule i' :=
  (restrictFunctorIsoPullback j).hom.app (idealModule i) ≫
    idealPullbackMap i i' j p h

/-- The actual normal map on an open square, using the original ideal map. -/
def canonicalNormalOpenSquareMap
    {X Y D D' : Scheme.{u}} (i : D ⟶ X) (i' : D' ⟶ Y)
    (j : Y ⟶ X) (p : D' ⟶ D) [IsOpenImmersion j] [IsOpenImmersion p]
    (h : p ≫ i = i' ≫ j) :
    ((pullback i).obj (idealModule i)).restrict p ⟶
      (pullback i').obj (idealModule i') :=
  (pullbackOpenSquare p i' i j h).hom.app (idealModule i) ≫
    (pullback i').map (canonicalIdealOpenSquareMap i i' j p h)

/-- The original normal comparison is invertible on an isomorphism square. -/
def canonicalAmbientNormalIso
    {X Y D D' : Scheme.{u}} (i : D ⟶ X) (i' : D' ⟶ Y)
    (j : Y ⟶ X) (p : D' ⟶ D) [IsIso j] [IsIso p]
    (h : p ≫ i = i' ≫ j) :
    ((pullback i).obj (idealModule i)).restrict p ≅
      (pullback i').obj (idealModule i') := by
  have := idealPullbackMap_isIso_of_iso_square i i' j p h
  exact (pullbackOpenSquare p i' i j h).app (idealModule i) ≪≫
    (pullback i').mapIso ((restrictFunctorIsoPullback j).app (idealModule i) ≪≫
      asIso (idealPullbackMap i i' j p h))

/-- The ambient normal isomorphism retains the original mixed-square arrow. -/
theorem canonicalAmbientNormalIso_hom
    {X Y D D' : Scheme.{u}} (i : D ⟶ X) (i' : D' ⟶ Y)
    (j : Y ⟶ X) (p : D' ⟶ D) [IsIso j] [IsIso p]
    (h : p ≫ i = i' ≫ j) :
    (canonicalAmbientNormalIso i i' j p h).hom = canonicalNormalOpenSquareMap i i' j p h := rfl

/-- A kernel element as a morphism into the original spectral ideal module. -/
def canonicalAffineIdealSection {A B : CommRingCat.{u}} (σ : A ⟶ B)
    (x : RingHom.ker σ.hom) :
    SheafOfModules.unit (Spec A).ringCatSheaf ⟶ idealModule (Spec.map σ) :=
  canonicalAffineUnitSection (ModuleCat.of A (RingHom.ker σ.hom)) x ≫
    (affineIdealIso σ).hom

/-- Its ideal inclusion is multiplication by the original scalar section. -/
theorem canonicalAffineIdealSection_inclusion {A B : CommRingCat.{u}} (σ : A ⟶ B)
    (x : RingHom.ker σ.hom) :
    canonicalAffineIdealSection σ x ≫ idealInclusion (Spec.map σ) =
      unitMul (Spec A) ((Scheme.ΓSpecIso A).inv x) := by
  rw [canonicalAffineIdealSection, Category.assoc, affineIdealIso_hom_inclusion]
  apply (unitHomGlobalSectionsEquiv (Spec A)
    (SheafOfModules.unit (Spec A).ringCatSheaf)).injective
  change ((tilde.functor A).map (ModuleCat.ofHom (RingHom.ker σ.hom).subtype)).val.app
      (op ⊤) ((canonicalAffineUnitSection (ModuleCat.of A (RingHom.ker σ.hom)) x).val.app
        (op ⊤) (1 : Γ(Spec A, ⊤))) =
    (unitMul (Spec A) ((Scheme.ΓSpecIso A).inv x)).val.app (op ⊤)
      (1 : Γ(Spec A, ⊤))
  rw [canonicalAffineUnitSection_app]
  have ht := ConcreteCategory.congr_hom (tilde.toOpen_map_app
    (ModuleCat.ofHom (RingHom.ker σ.hom).subtype) ⊤) x
  change ((tilde.functor A).map (ModuleCat.ofHom (RingHom.ker σ.hom).subtype)).val.app
      (op ⊤) (tilde.toOpen (ModuleCat.of A (RingHom.ker σ.hom)) ⊤ x) =
    tilde.toOpen (ModuleCat.of A A) ⊤ (x : A) at ht
  apply ht.trans
  change tilde.toOpen (ModuleCat.of A A) ⊤ (x : A) =
    (1 : Γ(Spec A, ⊤)) *
      ((Spec A).presheaf.map (𝟙 (op (⊤ : (Spec A).Opens)))).hom ((Scheme.ΓSpecIso A).inv x)
  simp only [CategoryTheory.Functor.map_id, CommRingCat.id_apply, one_mul]
  rfl

/-- The original ideal map takes an actual kernel element to its image in
the new ambient ring. The proof uses the original monic ideal inclusion. -/
theorem canonicalAffineIdealSection_openSquare
    {A B A' B' : CommRingCat.{u}} (σ : A ⟶ B) (σ' : A' ⟶ B')
    (φ : A ⟶ A') (ψ : B ⟶ B') [IsOpenImmersion (Spec.map φ)]
    (h : Spec.map ψ ≫ Spec.map σ = Spec.map σ' ≫ Spec.map φ)
    (x : RingHom.ker σ.hom) (y : RingHom.ker σ'.hom) (hxy : φ (x : A) = y) :
    (restrictFunctor (Spec.map φ)).map (canonicalAffineIdealSection σ x) ≫
        canonicalIdealOpenSquareMap (Spec.map σ) (Spec.map σ') (Spec.map φ) (Spec.map ψ) h =
      (restrictUnitIso (Spec.map φ)).hom ≫ canonicalAffineIdealSection σ' y := by
  apply (cancel_mono (idealInclusion (Spec.map σ'))).mp
  have hn := (restrictFunctorIsoPullback (Spec.map φ)).hom.naturality
    (idealInclusion (Spec.map σ))
  have hu : (pullbackUnitIso (Spec.map φ)).hom =
      SheafOfModules.pullbackObjUnitToUnit (Spec.map φ).toRingCatSheafHom := rfl
  have hΓ : (Spec.map φ).appTop.hom ((Scheme.ΓSpecIso A).inv (x : A)) =
      (Scheme.ΓSpecIso A').inv (y : A') := by
    have hg := congrArg (fun f : A ⟶ (Spec A').presheaf.obj (op ⊤) => f (x : A))
      (Scheme.ΓSpecIso_inv_naturality φ).symm
    exact hg.trans (congrArg (fun z : A' => (Scheme.ΓSpecIso A').inv z) hxy)
  calc
    _ = (restrictFunctor (Spec.map φ)).map (canonicalAffineIdealSection σ x) ≫
        (restrictFunctorIsoPullback (Spec.map φ)).hom.app (idealModule (Spec.map σ)) ≫
        (pullback (Spec.map φ)).map (idealInclusion (Spec.map σ)) ≫
        (pullbackUnitIso (Spec.map φ)).hom := by
      rw [canonicalIdealOpenSquareMap, Category.assoc, Category.assoc,
        idealPullbackMap_inclusion]
      rfl
    _ = (restrictFunctor (Spec.map φ)).map
        (canonicalAffineIdealSection σ x ≫ idealInclusion (Spec.map σ)) ≫
        (restrictUnitIso (Spec.map φ)).hom := by
      rw [CategoryTheory.Functor.map_comp, Category.assoc,
        ← restrictFunctorIsoPullback_hom_unit]
      simpa only [Category.assoc, hu] using
        congrArg (fun k => (restrictFunctor (Spec.map φ)).map
          (canonicalAffineIdealSection σ x) ≫ k ≫ (pullbackUnitIso (Spec.map φ)).hom) hn.symm
    _ = (restrictFunctor (Spec.map φ)).map
        (unitMul (Spec A) ((Scheme.ΓSpecIso A).inv (x : A))) ≫
        (restrictUnitIso (Spec.map φ)).hom := by
      rw [canonicalAffineIdealSection_inclusion]
    _ = (restrictUnitIso (Spec.map φ)).hom ≫
        unitMul (Spec A') ((Scheme.ΓSpecIso A').inv (y : A')) := by
      rw [unitMul_restrict, hΓ]
    _ = _ := by rw [Category.assoc, canonicalAffineIdealSection_inclusion]

/-- The original normal section as a morphism from the actual source unit. -/
def canonicalAffineNormalSectionHom {A B : CommRingCat.{u}} (σ : A ⟶ B)
    (x : RingHom.ker σ.hom) :
    SheafOfModules.unit (Spec B).ringCatSheaf ⟶
      (pullback (Spec.map σ)).obj (idealModule (Spec.map σ)) :=
  (pullbackUnitIso (Spec.map σ)).inv ≫
    (pullback (Spec.map σ)).map (canonicalAffineIdealSection σ x)

private theorem canonicalAffineNormalSectionHom_eq {A B : CommRingCat.{u}}
    (σ : A ⟶ B) (x : RingHom.ker σ.hom) :
    canonicalAffineNormalSectionHom σ x =
      canonicalAffineUnitSection
        ((ModuleCat.extendScalars σ.hom).obj (ModuleCat.of A (RingHom.ker σ.hom)))
        ((1 : B) ⊗ₜ[A,σ.hom] x) ≫ (intrinsicConormalIso σ).inv := by
  simp only [canonicalAffineNormalSectionHom, canonicalAffineIdealSection,
    intrinsicConormalIso, Iso.trans_inv, Functor.mapIso_inv, Iso.symm_inv,
    CategoryTheory.Functor.map_comp]
  rw [← canonicalAffineUnitSection_pullback σ (ModuleCat.of A (RingHom.ker σ.hom)) x]
  rw [show (tildePullbackIso σ).hom.app (ModuleCat.of A (RingHom.ker σ.hom)) =
      ((tildePullbackIso σ).app (ModuleCat.of A (RingHom.ker σ.hom))).hom from rfl]
  simp only [Category.assoc, Iso.hom_inv_id_assoc]

/-- The actual normal-section morphism is the original intrinsic `1 tensor x`
section on every open. -/
theorem canonicalAffineNormalSectionHom_app {A B : CommRingCat.{u}}
    (σ : A ⟶ B) (x : RingHom.ker σ.hom) (U : (Spec B).Opens) :
    (canonicalAffineNormalSectionHom σ x).val.app (op U) (1 : Γ(Spec B, U)) =
      intrinsicConormalSection σ x U := by
  rw [canonicalAffineNormalSectionHom_eq]
  change (intrinsicConormalIso σ).inv.val.app (op U)
      ((canonicalAffineUnitSection
        ((ModuleCat.extendScalars σ.hom).obj (ModuleCat.of A (RingHom.ker σ.hom)))
        ((1 : B) ⊗ₜ[A,σ.hom] x)).val.app (op U) (1 : Γ(Spec B, U))) = _
  rw [canonicalAffineUnitSection_app]
  rfl

/-- The original normal section follows the original ideal element through
the actual mixed open square. -/
theorem canonicalAffineNormalSectionHom_openSquare
    {A B A' B' : CommRingCat.{u}} (σ : A ⟶ B) (σ' : A' ⟶ B')
    (φ : A ⟶ A') (ψ : B ⟶ B')
    [IsOpenImmersion (Spec.map φ)] [IsOpenImmersion (Spec.map ψ)]
    (h : Spec.map ψ ≫ Spec.map σ = Spec.map σ' ≫ Spec.map φ)
    (x : RingHom.ker σ.hom) (y : RingHom.ker σ'.hom) (hxy : φ (x : A) = y) :
    (restrictFunctor (Spec.map ψ)).map (canonicalAffineNormalSectionHom σ x) ≫
        canonicalNormalOpenSquareMap (Spec.map σ) (Spec.map σ') (Spec.map φ) (Spec.map ψ) h =
      (restrictUnitIso (Spec.map ψ)).hom ≫ canonicalAffineNormalSectionHom σ' y := by
  let E := pullbackOpenSquare (Spec.map ψ) (Spec.map σ') (Spec.map σ) (Spec.map φ) h
  have hn := E.hom.naturality (canonicalAffineIdealSection σ x)
  have hu : (restrictFunctor (Spec.map ψ)).map (pullbackUnitIso (Spec.map σ)).inv ≫
        E.hom.app (SheafOfModules.unit (Spec A).ringCatSheaf) ≫
        (pullback (Spec.map σ')).map (restrictUnitIso (Spec.map φ)).hom =
      (restrictUnitIso (Spec.map ψ)).hom ≫ (pullbackUnitIso (Spec.map σ')).inv := by
    apply (cancel_mono (pullbackUnitIso (Spec.map σ')).hom).mp
    calc
      _ = (restrictFunctor (Spec.map ψ)).map (pullbackUnitIso (Spec.map σ)).inv ≫
          (restrictFunctor (Spec.map ψ)).map (pullbackUnitIso (Spec.map σ)).hom ≫
          (restrictUnitIso (Spec.map ψ)).hom := by
        simpa only [Category.assoc] using congrArg
          (fun k => (restrictFunctor (Spec.map ψ)).map (pullbackUnitIso (Spec.map σ)).inv ≫ k)
          (canonicalOpenPullbackSquare_unit
            (Spec.map ψ) (Spec.map σ') (Spec.map σ) (Spec.map φ) h)
      _ = _ := by
        rw [← CategoryTheory.Functor.map_comp_assoc, Iso.inv_hom_id,
          CategoryTheory.Functor.map_id, Category.id_comp, Category.assoc,
          Iso.inv_hom_id, Category.comp_id]
  calc
    _ = (restrictFunctor (Spec.map ψ)).map (pullbackUnitIso (Spec.map σ)).inv ≫
        E.hom.app (SheafOfModules.unit (Spec A).ringCatSheaf) ≫
        (pullback (Spec.map σ')).map
          ((restrictFunctor (Spec.map φ)).map (canonicalAffineIdealSection σ x) ≫
            canonicalIdealOpenSquareMap (Spec.map σ) (Spec.map σ')
              (Spec.map φ) (Spec.map ψ) h) := by
      simp only [canonicalAffineNormalSectionHom, canonicalNormalOpenSquareMap,
        CategoryTheory.Functor.map_comp, Category.assoc]
      simpa only [Functor.comp_map, Category.assoc] using congrArg
        (fun k => (restrictFunctor (Spec.map ψ)).map (pullbackUnitIso (Spec.map σ)).inv ≫
          k ≫ (pullback (Spec.map σ')).map (canonicalIdealOpenSquareMap
            (Spec.map σ) (Spec.map σ') (Spec.map φ) (Spec.map ψ) h)) hn
    _ = (restrictFunctor (Spec.map ψ)).map (pullbackUnitIso (Spec.map σ)).inv ≫
        E.hom.app (SheafOfModules.unit (Spec A).ringCatSheaf) ≫
        (pullback (Spec.map σ')).map (restrictUnitIso (Spec.map φ)).hom ≫
        (pullback (Spec.map σ')).map (canonicalAffineIdealSection σ' y) := by
      rw [canonicalAffineIdealSection_openSquare σ σ' φ ψ h x y hxy,
        CategoryTheory.Functor.map_comp]
    _ = _ := by
      simpa only [canonicalAffineNormalSectionHom, Category.assoc] using
        congrArg (fun k => k ≫
          (pullback (Spec.map σ')).map (canonicalAffineIdealSection σ' y)) hu

private theorem unitSection_openSquare_apply
    {X Y : Scheme.{u}} (j : X ⟶ Y) [IsOpenImmersion j]
    {M : Y.Modules} {N : X.Modules}
    (f : SheafOfModules.unit Y.ringCatSheaf ⟶ M)
    (g : SheafOfModules.unit X.ringCatSheaf ⟶ N) (k : M.restrict j ⟶ N)
    (h : (restrictFunctor j).map f ≫ k = (restrictUnitIso j).hom ≫ g)
    (U : X.Opens) :
    k.val.app (op U) (f.val.app (op (j ''ᵁ U)) (1 : Γ(Y, j ''ᵁ U))) =
      g.val.app (op U) (1 : Γ(X, U)) := by
  have ht := congrArg (fun t => t.val.app (op U) (1 : Γ(Y, j ''ᵁ U))) h
  change k.val.app (op U) (f.val.app (op (j ''ᵁ U)) (1 : Γ(Y, j ''ᵁ U))) =
    g.val.app (op U) ((j.appIso U).hom (1 : Γ(Y, j ''ᵁ U))) at ht
  rw [(j.appIso U).hom.hom.map_one] at ht
  exact ht

/-- The native mixed-square normal map carries the original kernel class
section to the section of its actual ambient-ring image. -/
theorem intrinsicConormalSection_openSquare
    {A B A' B' : CommRingCat.{u}} (σ : A ⟶ B) (σ' : A' ⟶ B')
    (φ : A ⟶ A') (ψ : B ⟶ B')
    [IsOpenImmersion (Spec.map φ)] [IsOpenImmersion (Spec.map ψ)]
    (h : Spec.map ψ ≫ Spec.map σ = Spec.map σ' ≫ Spec.map φ)
    (x : RingHom.ker σ.hom) (y : RingHom.ker σ'.hom) (hxy : φ (x : A) = y)
    (U : (Spec B').Opens) :
    (canonicalNormalOpenSquareMap (Spec.map σ) (Spec.map σ')
      (Spec.map φ) (Spec.map ψ) h).val.app (op U)
        (intrinsicConormalSection σ x ((Spec.map ψ) ''ᵁ U)) =
      intrinsicConormalSection σ' y U := by
  rw [← canonicalAffineNormalSectionHom_app σ x ((Spec.map ψ) ''ᵁ U),
    ← canonicalAffineNormalSectionHom_app σ' y U]
  exact unitSection_openSquare_apply (Spec.map ψ)
    (canonicalAffineNormalSectionHom σ x) (canonicalAffineNormalSectionHom σ' y)
    (canonicalNormalOpenSquareMap (Spec.map σ) (Spec.map σ')
      (Spec.map φ) (Spec.map ψ) h)
    (canonicalAffineNormalSectionHom_openSquare σ σ' φ ψ h x y hxy) U

/-- The same transport law in any two original relative conormal descriptions.
The base rings and their maps are arbitrary. -/
theorem relativeConormalIdealClass_openSquare
    {R R' A B A' B' : CommRingCat.{u}} (α : R ⟶ A) (α' : R' ⟶ A')
    (σ : A ⟶ B) (σ' : A' ⟶ B') (hσ : Function.Surjective σ)
    (hσ' : Function.Surjective σ') (φ : A ⟶ A') (ψ : B ⟶ B')
    [IsOpenImmersion (Spec.map φ)] [IsOpenImmersion (Spec.map ψ)]
    (h : Spec.map ψ ≫ Spec.map σ = Spec.map σ' ≫ Spec.map φ)
    (x : RingHom.ker σ.hom) (y : RingHom.ker σ'.hom) (hxy : φ (x : A) = y)
    (U : (Spec B').Opens) :
    (canonicalNormalOpenSquareMap (Spec.map σ) (Spec.map σ')
      (Spec.map φ) (Spec.map ψ) h).val.app (op U)
        ((relativeConormalAffineIdealPullbackIso α σ hσ).inv.val.app
          (op ((Spec.map ψ) ''ᵁ U))
          (tilde.toOpen (relativeConormalAffineModule α σ hσ)
            ((Spec.map ψ) ''ᵁ U) (relativeConormalAffineClass α σ hσ x))) =
      (relativeConormalAffineIdealPullbackIso α' σ' hσ').inv.val.app (op U)
        (tilde.toOpen (relativeConormalAffineModule α' σ' hσ') U
          (relativeConormalAffineClass α' σ' hσ' y)) := by
  rw [relativeConormalIdealClass_intrinsic α σ hσ x ((Spec.map ψ) ''ᵁ U),
    relativeConormalIdealClass_intrinsic α' σ' hσ' y U]
  exact intrinsicConormalSection_openSquare σ σ' φ ψ h x y hxy U

end AlgebraicGeometry.Scheme.Modules
