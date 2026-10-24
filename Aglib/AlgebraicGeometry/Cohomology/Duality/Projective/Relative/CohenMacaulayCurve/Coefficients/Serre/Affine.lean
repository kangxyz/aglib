/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Cohomology.Duality.Projective.Relative.CohenMacaulayCurve.Serre.Trace
public import Aglib.AlgebraicGeometry.Cohomology.Duality.Projective.Relative.CohenMacaulayCurve.Serre.Pairing

/-!
# Original affine model for coefficient-valued curve Serre duality

The coefficient is the actual tilde module of an arbitrary field module.
The affine target uses the inverse original single unit, and the original
module-Hom comparison preserves shifted source action and structural-unit
evaluation. No dimension, CM, rank or coefficient orientation is required.
-/

@[expose] public noncomputable section

universe u v w u' v' w'

open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian AlgebraicGeometry
open AlgebraicGeometry.ProjectiveSpace AlgebraicGeometry.Scheme.Modules
open AlgebraicGeometry.Scheme.Modules.QuasiCoherent RelativeCanonicalReindex

attribute [local instance] AlgebraicGeometry.Scheme.Modules.standardHasDerivedCategory
attribute [local instance] AlgebraicGeometry.Scheme.Modules.isQuasicoherent_unit
attribute [local instance] AlgebraicGeometry.Scheme.Modules.moduleSpecΓFunctor_additive

namespace AlgebraicGeometry.Scheme.Cohomology

/-- The standard derived-category model for modules over the coefficient ring. -/
local instance cmCurveCoefficientCoreModuleDerived (A : Type u) [CommRing A] :
    HasDerivedCategory.{u + 1} (ModuleCat.{u} A) := HasDerivedCategory.standard _

/-- Native single evaluation with distinct structural source and coefficient target. -/
structure CmCurveCoefficientEvaluationData
    {A B : Type*} [Category* A] [Category* B] [Preadditive A] [Preadditive B]
    {k : Type*} [CommRing k] [Linear k A] [Linear k B] [HasShift B ℤ]
    (S : A ⥤ B) [S.Full] [S.Faithful] [S.Additive] [S.Linear k]
    (O T : A) (X : B) (η : S.obj O ⟶ X)
    {N V : Type*} [AddCommGroup N] [Module k N] [AddCommGroup V] [Module k V]
    (U : (O ⟶ T) ≃ₗ[k] N) (c : N →ₗ[k] V) where
  /-- The original structural precomposition, single preimage and coefficient evaluation. -/
  toLinearMap : (X ⟶ (S.obj T)⟦(0 : ℤ)⟧) →ₗ[k] V
  /-- Its value is the actual native preimage, with the original zero shift. -/
  apply (φ : X ⟶ (S.obj T)⟦(0 : ℤ)⟧) :
    toLinearMap φ = c (U (S.preimage
      (η ≫ φ ≫ (shiftFunctorZero B ℤ).hom.app (S.obj T))))

/-- Construct the evaluator from actual endpoint maps, without coefficient orientation. -/
def cmCurveCoefficientEvaluationPacket
    {A B : Type*} [Category* A] [Category* B] [Preadditive A] [Preadditive B]
    {k : Type*} [CommRing k] [Linear k A] [Linear k B] [HasShift B ℤ]
    (S : A ⥤ B) [S.Full] [S.Faithful] [S.Additive] [S.Linear k]
    (O T : A) (X : B) (η : S.obj O ⟶ X)
    {N V : Type*} [AddCommGroup N] [Module k N] [AddCommGroup V] [Module k V]
    (U : (O ⟶ T) ≃ₗ[k] N) (c : N →ₗ[k] V) :
    CmCurveCoefficientEvaluationData S O T X η U c := by
  let E : (O ⟶ T) ≃ₗ[k] (S.obj O ⟶ S.obj T) :=
    LinearEquiv.ofBijective (S.mapLinearMap k) ⟨S.map_injective, S.map_surjective⟩
  let P : (X ⟶ (S.obj T)⟦(0 : ℤ)⟧) →ₗ[k] (S.obj O ⟶ S.obj T) :=
    (Linear.rightComp k (S.obj O)
      ((shiftFunctorZero B ℤ).hom.app (S.obj T))).comp
        (Linear.leftComp k ((S.obj T)⟦(0 : ℤ)⟧) η)
  refine ⟨c.comp (U.toLinearMap.comp (E.symm.toLinearMap.comp P)), ?_⟩
  intro φ
  let z : S.obj O ⟶ S.obj T :=
    η ≫ φ ≫ (shiftFunctorZero B ℤ).hom.app (S.obj T)
  have hP : P φ = z := by
    simp only [P, LinearMap.comp_apply, Linear.leftComp_apply,
      Linear.rightComp_apply, z, Category.assoc]
  have hE : E.symm z = S.preimage z := by
    apply S.map_injective
    exact (E.apply_symm_apply z).trans (S.map_preimage z).symm
  exact congrArg (fun f => c (U f)) ((congrArg E.symm hP).trans hE)

variable (k : Type u) [Field k] (ι : Type u)
    {C : Scheme.{u}} (j : C ⟶ ProjectiveSpace k ι) [IsClosedImmersion j]

/-- The original affine tilde/global-sections coefficient isomorphism. -/
def cmCurveCoefficientSerreSpecSectionsIso (V : ModuleCat.{u} k) :
    (moduleSpecΓFunctor (R := .of k)).obj (tilde V) ≅ V :=
  ((tilde.toTildeΓNatIso (R := CommRingCat.of k)).app V).symm

/-- Original homology and resolution-section transport into the specified coefficient. -/
def cmCurveCoefficientSerreHomologyTargetAddEquiv
    (V N : ModuleCat.{u} k) (eN : N ≅ V) (F : C.Modules) (i : ℕ) :
    ((DerivedCategory.homologyFunctor (ModuleCat.{u} k) (i : ℤ)).obj
        (cmCurveSerreDerivedSections k ι j F) ⟶ N) ≃+
      (cmCurveSerreCohomology k ι j F i →ₗ[k] V) := by
  let := moduleCohomologyModuleOfHom C (cmCurveSerreScalar k ι j) F i
  let E := moduleDerivedGlobalSectionsSingleCohomologyLinearEquiv C
    (cmCurveSerreScalar k ι j) (injectiveResolution F) i
  exact ((ModuleCat.homLinearEquiv (S := k)).trans
    (LinearEquiv.arrowCongr E eN.toLinearEquiv)).toAddEquiv

/-- Actual affine coefficient sections, with the original structural field action. -/
def cmCurveCoefficientSerreAffineSectionsIso (V : ModuleCat.{u} k) :
    (moduleGlobalSectionsFunctorOfHom (Spec (.of k))
      (Scheme.ΓSpecIso (.of k)).inv.hom).obj (tilde V) ≅ V :=
  ((moduleAffineGlobalSectionsIso (.of k)).symm.app (tilde V)) ≪≫
    cmCurveCoefficientSerreSpecSectionsIso k V

/-- Quasicoherent affine acyclicity makes the original single unit invertible. -/
theorem cmCurveCoefficientSerreAffineUnit_isIso (V : ModuleCat.{u} k) :
    IsIso ((moduleGlobalSectionsFunctorOfHom (Spec (.of k))
      (Scheme.ΓSpecIso (.of k)).inv.hom).rightDerivedSingleUnit (tilde V)) := by
  let T : (Spec (.of k)).Modules := tilde V
  let G := moduleGlobalSectionsFunctorOfHom (Spec (.of k)) (Scheme.ΓSpecIso (.of k)).inv.hom
  let U := moduleSpecΓFunctor (R := .of k)
  let : U.Additive := moduleSpecΓFunctor_additive (.of k)
  let : PreservesFiniteLimits U :=
    preservesFiniteLimits_of_natIso (moduleAffineGlobalSectionsIso (.of k)).symm
  let ρ := (moduleAffineGlobalSectionsIso (.of k)).symm
  let hT := AffineDerived.isZero_rightDerived_globalSections_succ T
  let E := U.rightDerivedFunctorPlusSingleIsoOfAcyclic T hT
  have hU : U.rightDerivedSingleUnit T ≫ E.hom = 𝟙 _ :=
    U.cmCurveRightDerivedSingleUnit_acyclic T hT
  have hUi : IsIso (U.rightDerivedSingleUnit T) := by
    have : IsIso (U.rightDerivedSingleUnit T ≫ E.hom) := by rw [hU]; infer_instance
    exact IsIso.of_isIso_comp_right _ E.hom
  let : IsIso (U.rightDerivedSingleUnit T) := hUi
  have hG : IsIso (G.rightDerivedSingleUnit T ≫
      (G.rightDerivedFunctorPlusIso ρ).hom.app
        ((DerivedCategory.Plus.singleFunctor (Spec (.of k)).Modules 0).obj T)) := by
    rw [G.cmCurveRightDerivedPlusIso_singleUnit U ρ T]
    infer_instance
  exact IsIso.of_isIso_comp_right _
    ((G.rightDerivedFunctorPlusIso ρ).hom.app
      ((DerivedCategory.Plus.singleFunctor (Spec (.of k)).Modules 0).obj T))

/-- The coefficient target is the inverse original single unit followed by original sections. -/
def cmCurveCoefficientSerreAffineTargetIso (V : ModuleCat.{u} k) :
    (moduleGlobalSectionsFunctorOfHom (Spec (.of k))
      (Scheme.ΓSpecIso (.of k)).inv.hom).rightDerivedFunctorPlus.obj
        ((DerivedCategory.Plus.singleFunctor (Spec (.of k)).Modules 0).obj (tilde V)) ≅
      (DerivedCategory.Plus.singleFunctor (ModuleCat.{u} k) 0).obj V := by
  let := cmCurveCoefficientSerreAffineUnit_isIso k V
  exact (asIso ((moduleGlobalSectionsFunctorOfHom (Spec (.of k))
    (Scheme.ΓSpecIso (.of k)).inv.hom).rightDerivedSingleUnit (tilde V))).symm ≪≫
      (DerivedCategory.Plus.singleFunctor (ModuleCat.{u} k) 0).mapIso
        (cmCurveCoefficientSerreAffineSectionsIso k V)

/-- Its normalization is proved from the same original unit, without a compatibility premise. -/
theorem cmCurveCoefficientSerreAffineTargetIso_unit (V : ModuleCat.{u} k) :
    (moduleGlobalSectionsFunctorOfHom (Spec (.of k))
      (Scheme.ΓSpecIso (.of k)).inv.hom).rightDerivedSingleUnit (tilde V) ≫
        (cmCurveCoefficientSerreAffineTargetIso k V).hom =
      (DerivedCategory.Plus.singleFunctor (ModuleCat.{u} k) 0).map
        (cmCurveCoefficientSerreAffineSectionsIso k V).hom := by
  let := cmCurveCoefficientSerreAffineUnit_isIso k V
  change (moduleGlobalSectionsFunctorOfHom (Spec (.of k))
      (Scheme.ΓSpecIso (.of k)).inv.hom).rightDerivedSingleUnit (tilde V) ≫
    inv ((moduleGlobalSectionsFunctorOfHom (Spec (.of k))
      (Scheme.ΓSpecIso (.of k)).inv.hom).rightDerivedSingleUnit (tilde V)) ≫ _ = _
  exact IsIso.hom_inv_id_assoc _ _

/-- The module-valued original arrow is obtained by the actual global
sections comparison, native derived sections, and original affine
coefficient isomorphism. -/
def cmCurveCoefficientSerreModuleHom (V : ModuleCat.{u} k) (F : C.Modules) (s : ℤ)
    (φ : cmCurveSerreDirectImage k ι j F ⟶
      ((DerivedCategory.singleFunctor (Spec (.of k)).Modules 0).obj
        ((tilde V)))⟦s⟧) :
    cmCurveSerreDerivedSections k ι j F ⟶
      ((DerivedCategory.singleFunctor (ModuleCat.{u} k) 0).obj (V))⟦s⟧ := by
  let p := j ≫ toSpec k ι
  let O : (Spec (.of k)).Modules := (tilde V)
  let IY := DerivedCategory.Plus.ι (C := (Spec (.of k)).Modules)
  let IM := DerivedCategory.Plus.ι (C := ModuleCat.{u} k)
  let G := moduleGlobalSectionsFunctorOfHom (Spec (.of k)) (Scheme.ΓSpecIso (.of k)).inv.hom
  let RF := G.rightDerivedFunctorPlus ⋙ IM
  let c := IM.map ((moduleDerivedGlobalSectionsPushforwardCompIso p
    (Scheme.ΓSpecIso (.of k)).inv.hom).hom.app
      ((DerivedCategory.Plus.singleFunctor C.Modules 0).obj F))
  let t := IM.map (cmCurveCoefficientSerreAffineTargetIso k V).hom
  exact cmCurveModuleHomOfIso IY RF c t s φ

omit [IsClosedImmersion j] in
/-- The module-valued specialization has the same original preimage,
composition comparison, and native coefficient map. -/
theorem cmCurveCoefficientSerreModuleHom_apply (V : ModuleCat.{u} k) (F : C.Modules) (s : ℤ)
    (φ : cmCurveSerreDirectImage k ι j F ⟶
      ((DerivedCategory.singleFunctor (Spec (.of k)).Modules 0).obj
        ((tilde V)))⟦s⟧) :
    let p := j ≫ toSpec k ι
    let O : (Spec (.of k)).Modules := (tilde V)
    let IY := DerivedCategory.Plus.ι (C := (Spec (.of k)).Modules)
    let IM := DerivedCategory.Plus.ι (C := ModuleCat.{u} k)
    let G := moduleGlobalSectionsFunctorOfHom (Spec (.of k)) (Scheme.ΓSpecIso (.of k)).inv.hom
    let v : ShiftedHom
        ((derivedPushforwardPlus p).obj ((DerivedCategory.Plus.singleFunctor C.Modules 0).obj F))
        ((DerivedCategory.Plus.singleFunctor (Spec (.of k)).Modules 0).obj O) s :=
      IY.preimage (φ ≫ (IY.commShiftIso s).inv.app
        ((DerivedCategory.Plus.singleFunctor (Spec (.of k)).Modules 0).obj O))
    cmCurveCoefficientSerreModuleHom k ι j V F s φ =
      IM.map ((moduleDerivedGlobalSectionsPushforwardCompIso p (Scheme.ΓSpecIso (.of
        k)).inv.hom).hom.app
          ((DerivedCategory.Plus.singleFunctor C.Modules 0).obj F)) ≫
        v.map (G.rightDerivedFunctorPlus ⋙ IM) ≫
          (IM.map (cmCurveCoefficientSerreAffineTargetIso k V).hom)⟦s⟧' := by
  dsimp only
  unfold cmCurveCoefficientSerreModuleHom
  exact cmCurveModuleHomOfIso_apply _ _ _ _ _ _

omit [IsClosedImmersion j] in
/-- The actual module-valued arrow retains all native source Ext actions. -/
theorem cmCurveCoefficientSerreModuleHom_comp (V : ModuleCat.{u} k)
    {F F' : C.Modules} {a : ℕ} {b c : ℤ}
    (η : Ext.{u + 1} (C := C.Modules) F F' a)
    (φ : cmCurveSerreDirectImage k ι j F' ⟶
      ((DerivedCategory.singleFunctor (Spec (.of k)).Modules 0).obj
        ((tilde V)))⟦b⟧)
    (hab : b + (a : ℤ) = c) :
    cmCurveCoefficientSerreModuleHom k ι j V F c
        ((η.homPlus.map (derivedPushforwardPlus (j ≫ toSpec k ι) ⋙
          DerivedCategory.Plus.ι)).comp φ hab) =
      (η.homPlus.map ((moduleGlobalSectionsFunctorOfHom C
        (cmCurveSerreScalar k ι j)).rightDerivedFunctorPlus ⋙
          DerivedCategory.Plus.ι)).comp
        (cmCurveCoefficientSerreModuleHom k ι j V F' b φ) hab := by
  let p := j ≫ toSpec k ι
  let O : (Spec (.of k)).Modules := (tilde V)
  let S := DerivedCategory.Plus.singleFunctor C.Modules 0
  let IY := DerivedCategory.Plus.ι (C := (Spec (.of k)).Modules)
  let IM := DerivedCategory.Plus.ι (C := ModuleCat.{u} k)
  let D := derivedPushforwardPlus p
  let G := moduleGlobalSectionsFunctorOfHom (Spec (.of k)) (Scheme.ΓSpecIso (.of k)).inv.hom
  let H := (moduleGlobalSectionsFunctorOfHom C (cmCurveSerreScalar k ι j)).rightDerivedFunctorPlus
  let RF := G.rightDerivedFunctorPlus ⋙ IM
  let Cmp : H ≅ D ⋙ G.rightDerivedFunctorPlus :=
    moduleDerivedGlobalSectionsPushforwardCompIso p (Scheme.ΓSpecIso (.of k)).inv.hom
  let : Cmp.hom.CommShift ℤ :=
    moduleDerivedGlobalSectionsPushforwardCompIso_commShift p
      (Scheme.ΓSpecIso (.of k)).inv.hom
  let E := cmCurveWhiskerRightAssoc Cmp IM
  let t := IM.map (cmCurveCoefficientSerreAffineTargetIso k V).hom
  let θ := (η.homPlus.map (D ⋙ IY)).comp φ hab
  have hL := congrArg
    (fun c' => cmCurveModuleHomOfIso IY RF c' t c θ)
    (cmCurveWhiskerRightAssoc_hom_app Cmp IM (S.obj F)).symm
  have hG := cmCurveModuleHomOfIso_comp D (H ⋙ IM) IY RF E t η.homPlus φ hab
  have hR := congrArg
    (fun c' => (η.homPlus.map (H ⋙ IM)).comp
      (cmCurveModuleHomOfIso IY RF c' t b φ) hab)
    (cmCurveWhiskerRightAssoc_hom_app Cmp IM (S.obj F'))
  exact hL.trans (hG.trans hR)

omit [IsClosedImmersion j] in
/-- In degree zero, no new derived arrow is chosen: the model is the
original composition comparison and original affine coefficient map. -/
theorem cmCurveCoefficientSerreModuleHom_mk₀ (V : ModuleCat.{u} k) (F : C.Modules)
    (f : (derivedPushforwardPlus (j ≫ toSpec k ι)).obj
        ((DerivedCategory.Plus.singleFunctor C.Modules 0).obj F) ⟶
      (DerivedCategory.Plus.singleFunctor (Spec (.of k)).Modules 0).obj
        ((tilde V))) :
    cmCurveCoefficientSerreModuleHom k ι j V F 0
      (ShiftedHom.mk₀ (0 : ℤ) rfl (DerivedCategory.Plus.ι.map f)) =
    ShiftedHom.mk₀ (0 : ℤ) rfl
      (DerivedCategory.Plus.ι.map
        ((moduleDerivedGlobalSectionsPushforwardCompIso (j ≫ toSpec k ι)
          (Scheme.ΓSpecIso (.of k)).inv.hom).hom.app
            ((DerivedCategory.Plus.singleFunctor C.Modules 0).obj F) ≫
          (moduleGlobalSectionsFunctorOfHom (Spec (.of k))
            (Scheme.ΓSpecIso (.of k)).inv.hom).rightDerivedFunctorPlus.map f ≫
          (cmCurveCoefficientSerreAffineTargetIso k V).hom)) := by
  let p := j ≫ toSpec k ι
  let O : (Spec (.of k)).Modules := (tilde V)
  let IY := DerivedCategory.Plus.ι (C := (Spec (.of k)).Modules)
  let IM := DerivedCategory.Plus.ι (C := ModuleCat.{u} k)
  let G := moduleGlobalSectionsFunctorOfHom (Spec (.of k)) (Scheme.ΓSpecIso (.of k)).inv.hom
  let RF := G.rightDerivedFunctorPlus ⋙ IM
  let c := (moduleDerivedGlobalSectionsPushforwardCompIso p (Scheme.ΓSpecIso (.of
    k)).inv.hom).hom.app
    ((DerivedCategory.Plus.singleFunctor C.Modules 0).obj F)
  let t := (cmCurveCoefficientSerreAffineTargetIso k V).hom
  have h := cmCurveModuleHomOfIso_mk₀ IY RF (IM.map c) (IM.map t) f
  exact h.trans (congrArg (ShiftedHom.mk₀ (0 : ℤ) rfl)
    ((congrArg (fun z => IM.map c ≫ z)
      (IM.map_comp (G.rightDerivedFunctorPlus.map f) t).symm).trans
        (IM.map_comp c (G.rightDerivedFunctorPlus.map f ≫ t)).symm))

/-- The coefficient section square is the actual composite defining c_V. -/
theorem cmCurveCoefficientSerreAffineSections_coefficient (V : ModuleCat.{u} k) :
    (moduleAffineGlobalSectionsIso (.of k)).inv.app (tilde V) ≫
      (cmCurveCoefficientSerreSpecSectionsIso k V).hom =
        (cmCurveCoefficientSerreAffineSectionsIso k V).hom := rfl

/-- The coefficient normalization in the affine Hom equivalence is the
original affine structural normalization, after its original section map. -/
theorem cmCurveCoefficientSerreAffineDerived_coefficient (V : ModuleCat.{u} k) :
    let O : (Spec (.of k)).Modules := (tilde V)
    let G := moduleGlobalSectionsFunctorOfHom (Spec (.of k)) (Scheme.ΓSpecIso (.of k)).inv.hom
    let U := moduleSpecΓFunctor (R := .of k)
    let : U.Additive := moduleSpecΓFunctor_additive (.of k)
    let : PreservesFiniteLimits U :=
      preservesFiniteLimits_of_natIso (moduleAffineGlobalSectionsIso (.of k)).symm
    let E := U.rightDerivedFunctorPlusSingleIsoOfAcyclic O
      (AffineDerived.isZero_rightDerived_globalSections_succ O)
    (G.rightDerivedFunctorPlusIso (moduleAffineGlobalSectionsIso (.of k)).symm).hom.app
        ((DerivedCategory.Plus.singleFunctor (Spec (.of k)).Modules 0).obj O) ≫
      E.hom ≫ (DerivedCategory.Plus.singleFunctor (ModuleCat.{u} k) 0).map
        (cmCurveCoefficientSerreSpecSectionsIso k V).hom =
      (cmCurveCoefficientSerreAffineTargetIso k V).hom := by
  dsimp only
  let O : (Spec (.of k)).Modules := (tilde V)
  let G := moduleGlobalSectionsFunctorOfHom (Spec (.of k)) (Scheme.ΓSpecIso (.of k)).inv.hom
  let U := moduleSpecΓFunctor (R := .of k)
  let : U.Additive := moduleSpecΓFunctor_additive (.of k)
  let : PreservesFiniteLimits U :=
    preservesFiniteLimits_of_natIso (moduleAffineGlobalSectionsIso (.of k)).symm
  let S := DerivedCategory.Plus.singleFunctor (ModuleCat.{u} k) 0
  let ρ := (moduleAffineGlobalSectionsIso (.of k)).symm
  let R := G.rightDerivedFunctorPlusIso ρ
  let E := U.rightDerivedFunctorPlusSingleIsoOfAcyclic O
    (AffineDerived.isZero_rightDerived_globalSections_succ O)
  let η := G.rightDerivedSingleUnit O
  let : IsIso η := cmCurveCoefficientSerreAffineUnit_isIso k V
  let c := (cmCurveCoefficientSerreAffineSectionsIso k V).hom
  let t := (cmCurveCoefficientSerreAffineTargetIso k V).hom
  have h₁ : η ≫ R.hom.app
        ((DerivedCategory.Plus.singleFunctor (Spec (.of k)).Modules 0).obj O) =
      S.map (ρ.hom.app O) ≫ U.rightDerivedSingleUnit O :=
    G.cmCurveRightDerivedPlusIso_singleUnit U ρ O
  have h₂ : U.rightDerivedSingleUnit O ≫ E.hom = 𝟙 _ :=
    U.cmCurveRightDerivedSingleUnit_acyclic O
      (AffineDerived.isZero_rightDerived_globalSections_succ O)
  have hc : S.map (ρ.hom.app O) ≫ S.map (cmCurveCoefficientSerreSpecSectionsIso k V).hom =
      S.map c := (S.map_comp _ _).symm.trans
        (congrArg S.map (cmCurveCoefficientSerreAffineSections_coefficient k V))
  have ht : η ≫ t = S.map c := IsIso.hom_inv_id_assoc η (S.map c)
  exact cmCurveCoefficientThroughUnit η (U.rightDerivedSingleUnit O)
    (R.hom.app ((DerivedCategory.Plus.singleFunctor (Spec (.of k)).Modules 0).obj O)) E.hom
    (S.map (ρ.hom.app O)) (S.map (cmCurveCoefficientSerreSpecSectionsIso k V).hom) t h₁ h₂
    (hc.trans ht.symm)

private theorem cmCurveCoefficientMapTriple
    {A B : Type*} [Category* A] [Category* B] (F : A ⥤ B)
    {P Q R T : A} (a : P ⟶ Q) (b : Q ⟶ R) (c : R ⟶ T) :
    F.map (a ≫ b ≫ c) = F.map a ≫ F.map b ≫ F.map c :=
  (F.map_comp a (b ≫ c)).trans
    (congrArg (fun t => F.map a ≫ t) (F.map_comp b c))

section AffineCoefficient

variable (n : ℕ) (e : ι ≃ Fin (n + 1))

/-- The original affine Hom equivalence and the module-valued original
arrow agree after their displayed native coefficient shifts and the
original spectrum coefficient map. No comparison equation is a premise. -/
theorem cmCurveCoefficientSerreAffineHom_moduleHom (V : ModuleCat.{u} k) (F : C.Modules)
    (hF : affineLocallyFiniteType C F) (q : ℕ)
    (a : cmCurveSerreDirectImage k ι j F ⟶
      ((DerivedCategory.singleFunctor (Spec (.of k)).Modules (n : ℤ)).obj
        ((tilde V)))⟦(q : ℤ)⟧) :
    let : Fintype ι := Fintype.ofEquiv (Fin (n + 1)) e.symm
    let : F.IsQuasicoherent := quasicoherent_of_affineLocallyFiniteType hF
    moduleSpecDerivedPushforwardHomAddEquiv (j ≫ toSpec k ι) F
        ((tilde V)) n q a ≫
      (relativeOpenCoefficientShiftIso
        ((moduleSpecΓFunctor (R := .of k)).obj
          ((tilde V))) (n : ℤ) (q : ℤ)).hom ≫
      ((DerivedCategory.singleFunctor (ModuleCat.{u} k) 0).map
        (cmCurveCoefficientSerreSpecSectionsIso k V).hom)⟦(q : ℤ) - n⟧' =
      cmCurveCoefficientSerreModuleHom k ι j V F ((q : ℤ) - n)
        (a ≫ (relativeOpenCoefficientShiftIso
          (C := (Spec (.of k)).Modules) (tilde (R := CommRingCat.of k) V)
            (n : ℤ) (q : ℤ)).hom) := by
  let : Fintype ι := Fintype.ofEquiv (Fin (n + 1)) e.symm
  let : F.IsQuasicoherent := quasicoherent_of_affineLocallyFiniteType hF
  let p := j ≫ toSpec k ι
  let O : (Spec (.of k)).Modules := (tilde V)
  let S := DerivedCategory.Plus.singleFunctor C.Modules 0
  let SY := DerivedCategory.Plus.singleFunctor (Spec (.of k)).Modules 0
  let SM := DerivedCategory.Plus.singleFunctor (ModuleCat.{u} k) 0
  let IY := DerivedCategory.Plus.ι (C := (Spec (.of k)).Modules)
  let IM := DerivedCategory.Plus.ι (C := ModuleCat.{u} k)
  let D := (Scheme.Modules.pushforward p).rightDerivedFunctorPlus
  let G := moduleGlobalSectionsFunctorOfHom (Spec (.of k)) (Scheme.ΓSpecIso (.of k)).inv.hom
  let U := moduleSpecΓFunctor (R := .of k)
  let : U.Additive := moduleSpecΓFunctor_additive (.of k)
  let : PreservesFiniteLimits U :=
    preservesFiniteLimits_of_natIso (moduleAffineGlobalSectionsIso (.of k)).symm
  let ρ : G ≅ U := NatIso.ofComponents
    (fun L => (moduleTopSectionsIso (Spec (.of k)) (Scheme.ΓSpecIso (.of k)).inv.hom L).symm)
    (by intro L L' f; ext x; rfl)
  have hρ : ρ = (moduleAffineGlobalSectionsIso (.of k)).symm := by
    apply Iso.ext
    apply NatTrans.ext
    funext L
    rfl
  let R := G.rightDerivedFunctorPlusIso ρ
  let : R.hom.CommShift ℤ := G.cmCurveRightDerivedPlusIso_commShift U ρ
  let Rfull := Functor.isoWhiskerRight R IM
  let : Rfull.hom.CommShift ℤ := by
    dsimp only [Rfull, Functor.isoWhiskerRight_hom]
    infer_instance
  let E := U.rightDerivedFunctorPlusSingleIsoOfAcyclic O
    (AffineDerived.isZero_rightDerived_globalSections_succ O)
  let Cmp := moduleDerivedGlobalSectionsPushforwardCompIso p (Scheme.ΓSpecIso (.of k)).inv.hom
  let cY := relativeOpenCoefficientShiftIso O (n : ℤ) (q : ℤ)
  let cM := relativeOpenCoefficientShiftIso (U.obj O) (n : ℤ) (q : ℤ)
  let s : ℤ := (q : ℤ) - n
  let v : ShiftedHom (D.obj (S.obj F)) (SY.obj O) s :=
    IY.preimage ((a ≫ cY.hom) ≫ (IY.commShiftIso s).inv.app (SY.obj O))
  have hnat : IM.map (R.hom.app (D.obj (S.obj F))) ≫
        v.map (U.rightDerivedFunctorPlus ⋙ IM) =
      v.map (G.rightDerivedFunctorPlus ⋙ IM) ≫
        (IM.map (R.hom.app (SY.obj O)))⟦s⟧' := by
    simpa only [ShiftedHom.comp_mk₀, ShiftedHom.mk₀_comp,
      Rfull, Functor.isoWhiskerRight_hom, Functor.whiskerRight_app] using
      (ShiftedHom.map_naturality v Rfull.hom).symm
  have hcoef₀ : IM.map (R.hom.app (SY.obj O)) ≫ IM.map E.hom ≫
      (DerivedCategory.singleFunctor (ModuleCat.{u} k) 0).map
        (cmCurveCoefficientSerreSpecSectionsIso k V).hom =
      IM.map (cmCurveCoefficientSerreAffineTargetIso k V).hom := by
    have h₀ := cmCurveCoefficientSerreAffineDerived_coefficient k V
    dsimp only at h₀
    rw [← hρ] at h₀
    have h := congrArg IM.map h₀
    have hm : IM.map (R.hom.app (SY.obj O) ≫ E.hom ≫
        SM.map (cmCurveCoefficientSerreSpecSectionsIso k V).hom) =
        IM.map (R.hom.app (SY.obj O)) ≫ IM.map E.hom ≫
          IM.map (SM.map (cmCurveCoefficientSerreSpecSectionsIso k V).hom) :=
      (IM.map_comp _ _).trans
        (congrArg (fun z => IM.map (R.hom.app (SY.obj O)) ≫ z) (IM.map_comp _ _))
    exact hm.symm.trans h
  let J := shiftFunctor (DerivedCategory (ModuleCat.{u} k)) s
  have hcoef : J.map (IM.map (R.hom.app (SY.obj O))) ≫
        J.map (IM.map E.hom) ≫
          J.map ((DerivedCategory.singleFunctor (ModuleCat.{u} k) 0).map
            (cmCurveCoefficientSerreSpecSectionsIso k V).hom) =
      J.map (IM.map (cmCurveCoefficientSerreAffineTargetIso k V).hom) :=
    (cmCurveCoefficientMapTriple J _ _ _).symm.trans (J.congr_map hcoef₀)
  have hA' : moduleSpecDerivedPushforwardHomAddEquiv p F O n q a =
      IM.map (Cmp.hom.app (S.obj F)) ≫ IM.map (R.hom.app (D.obj (S.obj F))) ≫
        v.map (U.rightDerivedFunctorPlus ⋙ IM) ≫ (IM.map E.hom)⟦s⟧' ≫ cM.inv := by
    have hA := moduleSpecDerivedPushforwardHomAddEquiv_apply p F O n q a
    dsimp only at hA
    convert hA using 1
    simp only [Cmp, ρ, G, U, R, E, cY, cM, s, v, S, SY, D, IM, IY,
      relativeOpenCoefficientShiftIso, Iso.trans_hom, NatTrans.comp_app,
      Functor.isoWhiskerLeft_hom, Functor.whiskerLeft_app, Functor.map_comp,
      Category.assoc]
    rfl
  let P := cmCurveSerreDerivedSections k ι j F
  let T := ((DerivedCategory.singleFunctor (ModuleCat.{u} k) 0).obj
    (V))⟦s⟧
  let a₀ : P ⟶ T := moduleSpecDerivedPushforwardHomAddEquiv p F O n q a ≫
    cM.hom ≫ ((DerivedCategory.singleFunctor (ModuleCat.{u} k) 0).map
      (cmCurveCoefficientSerreSpecSectionsIso k V).hom)⟦s⟧'
  let a₁ : P ⟶ T :=
    (IM.map (Cmp.hom.app (S.obj F)) ≫ IM.map (R.hom.app (D.obj (S.obj F))) ≫
      v.map (U.rightDerivedFunctorPlus ⋙ IM) ≫ (IM.map E.hom)⟦s⟧' ≫ cM.inv) ≫
        cM.hom ≫ ((DerivedCategory.singleFunctor (ModuleCat.{u} k) 0).map
          (cmCurveCoefficientSerreSpecSectionsIso k V).hom)⟦s⟧'
  let a₂ : P ⟶ T := IM.map (Cmp.hom.app (S.obj F)) ≫
    v.map (G.rightDerivedFunctorPlus ⋙ IM) ≫
      (IM.map (cmCurveCoefficientSerreAffineTargetIso k V).hom)⟦s⟧'
  have h₀ : a₀ = a₁ := congrArg (fun z => z ≫ cM.hom ≫
    ((DerivedCategory.singleFunctor (ModuleCat.{u} k) 0).map
      (cmCurveCoefficientSerreSpecSectionsIso k V).hom)⟦s⟧') hA'
  have h₁ : a₁ = a₂ := cmCurveAffineArrowTransport _ _ _ _ _ _ cM _ _ hnat hcoef
  have h₂ : a₂ = cmCurveCoefficientSerreModuleHom k ι j V F s (a ≫ cY.hom) :=
    (cmCurveCoefficientSerreModuleHom_apply k ι j V F s (a ≫ cY.hom)).symm
  exact h₀.trans (h₁.trans h₂)


/-- The same original affine Hom comparison uses any actual integer
reindex, proved from its original coefficient normalization. -/
theorem cmCurveCoefficientSerreAffineHom_moduleHom_reindex (V : ModuleCat.{u} k) (F : C.Modules)
    (hF : affineLocallyFiniteType C F) (q : ℕ) (s : ℤ)
    (hqn : (q : ℤ) - s = n)
    (a : cmCurveSerreDirectImage k ι j F ⟶
      ((DerivedCategory.singleFunctor (Spec (.of k)).Modules (n : ℤ)).obj
        ((tilde V)))⟦(q : ℤ)⟧) :
    let : Fintype ι := Fintype.ofEquiv (Fin (n + 1)) e.symm
    let : F.IsQuasicoherent := quasicoherent_of_affineLocallyFiniteType hF
    let O : (Spec (.of k)).Modules := (tilde V)
    let N := (moduleSpecΓFunctor (R := .of k)).obj O
    moduleSpecDerivedPushforwardHomAddEquiv (j ≫ toSpec k ι) F O n q a ≫
        (singleReindexIso N (n : ℤ) (q : ℤ) s hqn).inv ≫
        ((DerivedCategory.singleFunctor (ModuleCat.{u} k) 0).map
          (cmCurveCoefficientSerreSpecSectionsIso k V).hom)⟦s⟧' =
      cmCurveCoefficientSerreModuleHom k ι j V F s
        (a ≫ (singleReindexIso O (n : ℤ) (q : ℤ) s hqn).inv) := by
  let : Fintype ι := Fintype.ofEquiv (Fin (n + 1)) e.symm
  let : F.IsQuasicoherent := quasicoherent_of_affineLocallyFiniteType hF
  have hs : s = (q : ℤ) - n := by omega
  subst s
  dsimp only
  let O : (Spec (.of k)).Modules := (tilde V)
  let N := (moduleSpecΓFunctor (R := .of k)).obj O
  let B := moduleSpecDerivedPushforwardHomAddEquiv (j ≫ toSpec k ι) F O n q a
  let u := ((DerivedCategory.singleFunctor (ModuleCat.{u} k) 0).map
    (cmCurveCoefficientSerreSpecSectionsIso k V).hom)⟦(q : ℤ) - n⟧'
  have hM := congrArg (fun z => B ≫ z ≫ u)
    (cmCurveCoefficientShift_reindex N (n : ℤ) (q : ℤ)).symm
  have hY := congrArg
    (fun z => cmCurveCoefficientSerreModuleHom k ι j V F ((q : ℤ) - n) (a ≫ z))
    (cmCurveCoefficientShift_reindex O (n : ℤ) (q : ℤ))
  exact hM.trans ((cmCurveCoefficientSerreAffineHom_moduleHom k ι j n e V F hF q a).trans hY)

/-- The actual affine comparison, original homology extraction, and
original resolution-section comparison evaluate the module-valued native
shift map. This is a proved original-map identity, not an extra premise. -/
theorem cmCurveCoefficientSerreAffineHom_homology_of_reindex (V : ModuleCat.{u} k) (F : C.Modules)
    (hF : affineLocallyFiniteType C F) (q i : ℕ) (s : ℤ)
    (hqn : (q : ℤ) - s = n) (hsi : s + (i : ℤ) = 0)
    (a : cmCurveSerreDirectImage k ι j F ⟶
      ((DerivedCategory.singleFunctor (Spec (.of k)).Modules (n : ℤ)).obj
        ((tilde V)))⟦(q : ℤ)⟧)
    (x : cmCurveSerreCohomology k ι j F i) :
    let := moduleCohomologyModuleOfHom C (cmCurveSerreScalar k ι j) F i
    let : Fintype ι := Fintype.ofEquiv (Fin (n + 1)) e.symm
    let : F.IsQuasicoherent := quasicoherent_of_affineLocallyFiniteType hF
    let O : (Spec (.of k)).Modules := (tilde V)
    let N := (moduleSpecΓFunctor (R := .of k)).obj O
    let B := moduleSpecDerivedPushforwardHomAddEquiv (j ≫ toSpec k ι) F O n q a
    let T := ((DerivedCategory.singleFunctors (ModuleCat.{u} k)).shiftIso
      (q : ℤ) (i : ℤ) (n : ℤ) (by omega)).app N
    let E := moduleDerivedGlobalSectionsSingleCohomologyLinearEquiv C
      (cmCurveSerreScalar k ι j) (injectiveResolution F) i
    cmCurveCoefficientSerreHomologyTargetAddEquiv k ι j V N
        (cmCurveCoefficientSerreSpecSectionsIso k V) F i
        ((DerivedCategory.homologyFunctor (ModuleCat.{u} k) (i : ℤ)).map (B ≫ T.hom) ≫
          (DerivedCategory.singleFunctorCompHomologyFunctorIso (ModuleCat.{u} k)
            (i : ℤ)).hom.app N) x =
      ((DerivedCategory.homologyFunctor (ModuleCat.{u} k) 0).shiftMap
        (cmCurveCoefficientSerreModuleHom k ι j V F s
          (a ≫ (singleReindexIso O (n : ℤ) (q : ℤ) s hqn).inv))
        (i : ℤ) 0 (by omega) ≫
          (DerivedCategory.singleFunctorCompHomologyFunctorIso (ModuleCat.{u} k) 0).hom.app
            (V)) (E.symm x) := by
  let := moduleCohomologyModuleOfHom C (cmCurveSerreScalar k ι j) F i
  let : Fintype ι := Fintype.ofEquiv (Fin (n + 1)) e.symm
  let : F.IsQuasicoherent := quasicoherent_of_affineLocallyFiniteType hF
  let O : (Spec (.of k)).Modules := (tilde V)
  let N := (moduleSpecΓFunctor (R := .of k)).obj O
  let B := moduleSpecDerivedPushforwardHomAddEquiv (j ≫ toSpec k ι) F O n q a
  let T := ((DerivedCategory.singleFunctors (ModuleCat.{u} k)).shiftIso
    (q : ℤ) (i : ℤ) (n : ℤ) (by omega)).app N
  let JN := ((DerivedCategory.singleFunctors (ModuleCat.{u} k)).shiftIso
    s (i : ℤ) 0 (by omega)).app N
  let Jk := ((DerivedCategory.singleFunctors (ModuleCat.{u} k)).shiftIso
    s (i : ℤ) 0 (by omega)).app (V)
  let E := moduleDerivedGlobalSectionsSingleCohomologyLinearEquiv C
    (cmCurveSerreScalar k ι j) (injectiveResolution F) i
  let eN := cmCurveCoefficientSerreSpecSectionsIso k V
  let ψ := cmCurveCoefficientSerreModuleHom k ι j V F s
    (a ≫ (singleReindexIso O (n : ℤ) (q : ℤ) s hqn).inv)
  let H := DerivedCategory.homologyFunctor (ModuleCat.{u} k) (i : ℤ)
  have hbridge := cmCurveCoefficientSerreAffineHom_moduleHom_reindex k ι j n e V F hF q s hqn a
  have hshift : (singleReindexIso N (n : ℤ) (q : ℤ) s hqn).inv = T.hom ≫ JN.inv :=
    cmCurveReindexCoefficient N (n : ℤ) (q : ℤ) s (i : ℤ) hqn hsi
  have hnat : ((DerivedCategory.singleFunctor (ModuleCat.{u} k) 0).map eN.hom)⟦s⟧' ≫
      Jk.hom = JN.hom ≫ (DerivedCategory.singleFunctor (ModuleCat.{u} k) (i : ℤ)).map eN.hom :=
    (((DerivedCategory.singleFunctors (ModuleCat.{u} k)).shiftIso s (i : ℤ) 0
      (by omega)).hom.naturality eN.hom)
  have hArrow : B ≫ T.hom ≫
      (DerivedCategory.singleFunctor (ModuleCat.{u} k) (i : ℤ)).map eN.hom =
      ψ ≫ Jk.hom :=
    cmCurveTargetSinglePasting B T.hom
      (singleReindexIso N (n : ℤ) (q : ℤ) s hqn).inv JN
      (((DerivedCategory.singleFunctor (ModuleCat.{u} k) 0).map eN.hom)⟦s⟧')
      Jk ((DerivedCategory.singleFunctor (ModuleCat.{u} k) (i : ℤ)).map eN.hom) ψ
      hshift hnat hbridge
  let eI := (DerivedCategory.singleFunctorCompHomologyFunctorIso (ModuleCat.{u} k) (i :
    ℤ)).hom.app N
  let eK := (DerivedCategory.singleFunctorCompHomologyFunctorIso (ModuleCat.{u} k) (i :
    ℤ)).hom.app
    (V)
  have hcoef : H.map ((DerivedCategory.singleFunctor (ModuleCat.{u} k) (i : ℤ)).map eN.hom) ≫ eK =
      eI ≫ eN.hom := by
    simpa only [Functor.comp_map, Functor.id_map] using
      (DerivedCategory.singleFunctorCompHomologyFunctorIso (ModuleCat.{u} k) (i :
        ℤ)).hom.naturality eN.hom
  have hform : H.map (B ≫ T.hom) ≫ eI ≫ eN.hom =
      H.map ((B ≫ T.hom) ≫
        (DerivedCategory.singleFunctor (ModuleCat.{u} k) (i : ℤ)).map eN.hom) ≫ eK := by
    exact (congrArg (fun z => H.map (B ≫ T.hom) ≫ z) hcoef.symm).trans
      ((Category.assoc _ _ _).symm.trans
        (congrArg (fun z => z ≫ eK)
          (H.map_comp (B ≫ T.hom)
            ((DerivedCategory.singleFunctor (ModuleCat.{u} k) (i : ℤ)).map eN.hom)).symm))
  have hnormalize : H.map (B ≫ T.hom) ≫ eI ≫ eN.hom =
      (DerivedCategory.homologyFunctor (ModuleCat.{u} k) 0).shiftMap ψ (i : ℤ) 0 (by omega) ≫
        (DerivedCategory.singleFunctorCompHomologyFunctorIso (ModuleCat.{u} k) 0).hom.app
          (V) :=
    hform.trans ((congrArg (fun z => H.map z ≫ eK)
      ((Category.assoc _ _ _).trans hArrow)).trans
      (DerivedCategory.cmCurveHomToShiftSingle_homology (V) s (i : ℤ) (by omega)
        ψ))
  change (H.map (B ≫ T.hom) ≫ eI ≫ eN.hom) (E.symm x) = _
  exact congrArg (fun f => f (E.symm x)) hnormalize

end AffineCoefficient

variable (V : ModuleCat.{u} k)

/-- Precompose by the original structural unit and evaluate the actual coefficient section. -/
def cmCurveCoefficientSerreUnitEvaluationLinearMap :
    let := moduleCategoryLinearOfHom (Spec (.of k)) (Scheme.ΓSpecIso (.of k)).inv.hom
    (cmCurveSerreDirectImage k ι j (cmCurveSerreUnit C) ⟶
      ((DerivedCategory.singleFunctor (Spec (.of k)).Modules 0).obj
        (tilde V))⟦(0 : ℤ)⟧) →ₗ[k] V := by
  let Y := Spec (.of k)
  let O : Y.Modules := cmCurveSerreUnit Y
  let T : Y.Modules := tilde V
  let := moduleCategoryLinearOfHom Y (Scheme.ΓSpecIso (.of k)).inv.hom
  let S := DerivedCategory.singleFunctor Y.Modules 0
  let X := cmCurveSerreDirectImage k ι j (cmCurveSerreUnit C)
  let η : S.obj O ⟶ X := DerivedCategory.Plus.ι.map
    (moduleDerivedPushforwardUnit Y (j ≫ toSpec k ι))
  let U : (O ⟶ T) ≃ₗ[k] (moduleSpecΓFunctor (R := .of k)).obj T :=
    unitHomGlobalSectionsLinearEquivOfHom Y (Scheme.ΓSpecIso (.of k)).inv.hom T
  exact (cmCurveCoefficientEvaluationPacket S O T X η U
    (cmCurveCoefficientSerreSpecSectionsIso k V).hom.hom).toLinearMap

omit [IsClosedImmersion j] in
/-- The actual evaluator retains its original fully faithful single preimage. -/
theorem cmCurveCoefficientSerreUnitEvaluationLinearMap_apply
    (φ : cmCurveSerreDirectImage k ι j (cmCurveSerreUnit C) ⟶
      ((DerivedCategory.singleFunctor (Spec (.of k)).Modules 0).obj (tilde V))⟦(0 : ℤ)⟧) :
    cmCurveCoefficientSerreUnitEvaluationLinearMap k ι j V φ =
      (cmCurveCoefficientSerreSpecSectionsIso k V).hom
        (unitHomGlobalSectionsEquiv (Spec (.of k)) (tilde V)
          ((DerivedCategory.singleFunctor (Spec (.of k)).Modules 0).preimage
            (DerivedCategory.Plus.ι.map (moduleDerivedPushforwardUnit (Spec (.of k))
              (j ≫ toSpec k ι)) ≫ φ ≫
                (shiftFunctorZero (DerivedCategory (Spec (.of k)).Modules) ℤ).hom.app
                  ((DerivedCategory.singleFunctor (Spec (.of k)).Modules 0).obj (tilde V))))) := by
  let Y := Spec (.of k)
  let O : Y.Modules := cmCurveSerreUnit Y
  let T : Y.Modules := tilde V
  let := moduleCategoryLinearOfHom Y (Scheme.ΓSpecIso (.of k)).inv.hom
  let S := DerivedCategory.singleFunctor Y.Modules 0
  let X := cmCurveSerreDirectImage k ι j (cmCurveSerreUnit C)
  let η : S.obj O ⟶ X := DerivedCategory.Plus.ι.map
    (moduleDerivedPushforwardUnit Y (j ≫ toSpec k ι))
  let U : (O ⟶ T) ≃ₗ[k] (moduleSpecΓFunctor (R := .of k)).obj T :=
    unitHomGlobalSectionsLinearEquivOfHom Y (Scheme.ΓSpecIso (.of k)).inv.hom T
  exact (cmCurveCoefficientEvaluationPacket S O T X η U
    (cmCurveCoefficientSerreSpecSectionsIso k V).hom.hom).apply φ

/-- Original affine unit naturality permits a different coefficient target. -/
theorem cmCurveCoefficientSerreAffineTarget_map
    (h : (cmCurveSerreUnit (Spec (.of k)) : (Spec (.of k)).Modules) ⟶ tilde V) :
    (affineDerivedStructureTargetIso (.of k)).inv ≫
        (moduleGlobalSectionsFunctorOfHom (Spec (.of k))
          (Scheme.ΓSpecIso (.of k)).inv.hom).rightDerivedFunctorPlus.map
            ((DerivedCategory.Plus.singleFunctor (Spec (.of k)).Modules 0).map h) ≫
        (cmCurveCoefficientSerreAffineTargetIso k V).hom =
      (DerivedCategory.Plus.singleFunctor (ModuleCat.{u} k) 0).map
        ((moduleAffineStructureSectionsIso (.of k)).inv ≫
          (moduleGlobalSectionsFunctorOfHom (Spec (.of k))
            (Scheme.ΓSpecIso (.of k)).inv.hom).map h ≫
              (cmCurveCoefficientSerreAffineSectionsIso k V).hom) := by
  let Y := Spec (.of k)
  let O : Y.Modules := cmCurveSerreUnit Y
  let T : Y.Modules := tilde V
  let G := moduleGlobalSectionsFunctorOfHom Y (Scheme.ΓSpecIso (.of k)).inv.hom
  let S := DerivedCategory.Plus.singleFunctor (ModuleCat.{u} k) 0
  let E := moduleAffineStructureSectionsIso (.of k)
  let F := cmCurveCoefficientSerreAffineSectionsIso k V
  let η₀ := G.rightDerivedSingleUnit O
  let η₁ := G.rightDerivedSingleUnit T
  let : IsIso η₀ := affineStructureUnit_isIso (.of k)
  let : IsIso η₁ := cmCurveCoefficientSerreAffineUnit_isIso k V
  let b := G.rightDerivedFunctorPlus.map
    ((DerivedCategory.Plus.singleFunctor Y.Modules 0).map h)
  have hn : S.map (G.map h) ≫ η₁ = η₀ ≫ b := G.rightDerivedSingleUnit_naturality h
  change (S.map E.inv ≫ η₀) ≫ b ≫ (inv η₁ ≫ S.map F.hom) =
    S.map (E.inv ≫ G.map h ≫ F.hom)
  have hp : (S.map E.inv ≫ η₀) ≫ b ≫ (inv η₁ ≫ S.map F.hom) =
      S.map E.inv ≫ S.map (G.map h) ≫ S.map F.hom := by
    simp only [Category.assoc]
    rw [← Category.assoc η₀ b, ← hn]
    simp only [Category.assoc, IsIso.hom_inv_id_assoc]
  exact hp.trans (cmCurveCoefficientMapTriple S E.inv (G.map h) F.hom).symm

/-- The original affine coefficient map evaluates the original unit morphism at one. -/
theorem cmCurveCoefficientSerreAffineSections_map_one
    (h : (cmCurveSerreUnit (Spec (.of k)) : (Spec (.of k)).Modules) ⟶ tilde V) :
    ((moduleAffineStructureSectionsIso (.of k)).inv ≫
      (moduleGlobalSectionsFunctorOfHom (Spec (.of k))
        (Scheme.ΓSpecIso (.of k)).inv.hom).map h ≫
          (cmCurveCoefficientSerreAffineSectionsIso k V).hom) (1 : k) =
      (cmCurveCoefficientSerreSpecSectionsIso k V).hom
        (unitHomGlobalSectionsEquiv (Spec (.of k)) (tilde V) h) := by
  change (cmCurveCoefficientSerreSpecSectionsIso k V).hom
      (Scheme.Modules.Hom.app h ⊤ ((Scheme.ΓSpecIso (.of k)).inv (1 : k))) =
    (cmCurveCoefficientSerreSpecSectionsIso k V).hom
      (Scheme.Modules.Hom.app h ⊤ (1 : Γ(Spec (.of k), ⊤)))
  exact congrArg (fun z : Γ(Spec (.of k), ⊤) =>
    (cmCurveCoefficientSerreSpecSectionsIso k V).hom (Scheme.Modules.Hom.app h ⊤ z))
    (Scheme.ΓSpecIso (.of k)).inv.hom.map_one

private theorem cmCurveCoefficientUnitPaste
    {A B : Type*} [Category* A] [Category* B] (F : A ⥤ B)
    {M N P : A} {K L Z : B} (η : M ⟶ N) (f : N ⟶ P)
    (u : K ⟶ L) (c : L ⟶ F.obj N) (a : K ⟶ F.obj M) (t : F.obj P ⟶ Z)
    (h : u ≫ c = a ≫ F.map η) :
    u ≫ (c ≫ F.map f ≫ t) = a ≫ F.map (η ≫ f) ≫ t := by
  simp only [Functor.map_comp, Category.assoc]
  rw [← Category.assoc u c, h]
  simp only [Category.assoc]

omit [IsClosedImmersion j] in
/-- Every original degree-zero arrow has the same coefficient-valued structural evaluation. -/
theorem cmCurveCoefficientSerreModuleHom_unit
    (φ : cmCurveSerreDirectImage k ι j (cmCurveSerreUnit C) ⟶
      ((DerivedCategory.singleFunctor (Spec (.of k)).Modules 0).obj (tilde V))⟦(0 : ℤ)⟧) :
    let H := DerivedCategory.homologyFunctor (ModuleCat.{u} k) 0
    let E₀ := (DerivedCategory.singleFunctorCompHomologyFunctorIso (ModuleCat.{u} k) 0).app
      (ModuleCat.of k k)
    let E₁ := (DerivedCategory.singleFunctorCompHomologyFunctorIso (ModuleCat.{u} k) 0).app V
    let u := DerivedCategory.Plus.ι.map (moduleDerivedStructureUnit C (cmCurveSerreScalar k ι j))
    (H.shiftMap (cmCurveCoefficientSerreModuleHom k ι j V (cmCurveSerreUnit C) 0 φ)
      0 0 (by omega) ≫ E₁.hom) (H.map u (E₀.inv (1 : k))) =
        cmCurveCoefficientSerreUnitEvaluationLinearMap k ι j V φ := by
  dsimp only
  let Y := Spec (.of k)
  let O : Y.Modules := cmCurveSerreUnit Y
  let T : Y.Modules := tilde V
  let OC : C.Modules := cmCurveSerreUnit C
  let p := j ≫ toSpec k ι
  let G := moduleGlobalSectionsFunctorOfHom Y (Scheme.ΓSpecIso (.of k)).inv.hom
  let IY := DerivedCategory.Plus.ι (C := Y.Modules)
  let IM := DerivedCategory.Plus.ι (C := ModuleCat.{u} k)
  let SY := DerivedCategory.singleFunctor Y.Modules 0
  let SYp := DerivedCategory.Plus.singleFunctor Y.Modules 0
  let SM := DerivedCategory.singleFunctor (ModuleCat.{u} k) 0
  let Z := (shiftFunctorZero (DerivedCategory Y.Modules) ℤ).app (SY.obj T)
  let f : (derivedPushforwardPlus p).obj
      ((DerivedCategory.Plus.singleFunctor C.Modules 0).obj OC) ⟶ SYp.obj T :=
    IY.preimage (φ ≫ Z.hom)
  let η := moduleDerivedPushforwardUnit Y p
  let h : O ⟶ T := SY.preimage (IY.map (η ≫ f))
  have hf : IY.map f = φ ≫ Z.hom := IY.map_preimage _
  have hh : SY.map h = IY.map (η ≫ f) := SY.map_preimage _
  have hp : SYp.map h = η ≫ f := by
    apply IY.map_injective
    exact hh
  have hφ : φ = ShiftedHom.mk₀ (0 : ℤ) rfl (IY.map f) :=
    Functor.cmCurveEqMk₀_of_postZero φ (IY.map f) hf.symm
  let Cmp := moduleDerivedGlobalSectionsPushforwardCompIso p (Scheme.ΓSpecIso (.of k)).inv.hom
  let u := moduleDerivedStructureUnit C (cmCurveSerreScalar k ι j)
  let Ξ := Cmp.hom.app ((DerivedCategory.Plus.singleFunctor C.Modules 0).obj OC) ≫
    G.rightDerivedFunctorPlus.map f ≫ (cmCurveCoefficientSerreAffineTargetIso k V).hom
  let b := (moduleAffineStructureSectionsIso (.of k)).inv ≫ G.map h ≫
    (cmCurveCoefficientSerreAffineSectionsIso k V).hom
  have hu : u ≫ Cmp.hom.app ((DerivedCategory.Plus.singleFunctor C.Modules 0).obj OC) =
      (affineDerivedStructureTargetIso (.of k)).inv ≫ G.rightDerivedFunctorPlus.map η := by
    have hη : moduleDerivedStructureUnit Y (Scheme.ΓSpecIso (.of k)).inv.hom =
        (affineDerivedStructureTargetIso (.of k)).inv := by
      apply (cancel_mono (affineDerivedStructureTargetIso (.of k)).hom).mp
      exact (affineDerivedStructureTargetIso_unit (.of k)).trans
        (affineDerivedStructureTargetIso (.of k)).inv_hom_id.symm
    exact (moduleDerivedStructureUnit_pushforward p (Scheme.ΓSpecIso (.of k)).inv.hom).symm.trans
      (congrArg (fun z => z ≫ G.rightDerivedFunctorPlus.map η) hη)
  have hcomp : u ≫ Ξ = (DerivedCategory.Plus.singleFunctor (ModuleCat.{u} k) 0).map b := by
    have h₀ := cmCurveCoefficientUnitPaste G.rightDerivedFunctorPlus η f u
      (Cmp.hom.app ((DerivedCategory.Plus.singleFunctor C.Modules 0).obj OC))
      (affineDerivedStructureTargetIso (.of k)).inv
      (cmCurveCoefficientSerreAffineTargetIso k V).hom hu
    exact h₀.trans ((congrArg (fun z =>
      (affineDerivedStructureTargetIso (.of k)).inv ≫ G.rightDerivedFunctorPlus.map z ≫
        (cmCurveCoefficientSerreAffineTargetIso k V).hom) hp.symm).trans
          (cmCurveCoefficientSerreAffineTarget_map k V h))
  let H := DerivedCategory.homologyFunctor (ModuleCat.{u} k) 0
  let E₀ := (DerivedCategory.singleFunctorCompHomologyFunctorIso (ModuleCat.{u} k) 0).app
    (ModuleCat.of k k)
  let E₁ := (DerivedCategory.singleFunctorCompHomologyFunctorIso (ModuleCat.{u} k) 0).app V
  let v := H.map (IM.map u)
  let w := H.map (IM.map Ξ)
  have hχ : cmCurveCoefficientSerreModuleHom k ι j V OC 0 φ =
      ShiftedHom.mk₀ (0 : ℤ) rfl (IM.map Ξ) :=
    (congrArg (cmCurveCoefficientSerreModuleHom k ι j V OC 0) hφ).trans
      (cmCurveCoefficientSerreModuleHom_mk₀ k ι j V OC f)
  have hH : H.shiftMap (cmCurveCoefficientSerreModuleHom k ι j V OC 0 φ) 0 0 (by omega) = w :=
    (congrArg (fun q => H.shiftMap q 0 0 (by omega)) hχ).trans
      (DerivedCategory.cmCurve_homology_shiftMap_mk₀ (IM.map Ξ))
  let σ₀ := (DerivedCategory.Plus.singleFunctorιIso (ModuleCat.{u} k) 0).app
    (ModuleCat.of k k)
  let σ₁ := (DerivedCategory.Plus.singleFunctorιIso (ModuleCat.{u} k) 0).app V
  let g : SM.obj (ModuleCat.of k k) ⟶ SM.obj V :=
    σ₀.inv ≫ IM.map (u ≫ Ξ) ≫ σ₁.hom
  have hg : g = IM.map (u ≫ Ξ) :=
    (Category.id_comp (IM.map (u ≫ Ξ) ≫ 𝟙 _)).trans
      (Category.comp_id (IM.map (u ≫ Ξ)))
  have hm : H.map g = v ≫ w :=
    (congrArg H.map hg).trans
      ((congrArg H.map (IM.map_comp u Ξ)).trans (H.map_comp (IM.map u) (IM.map Ξ)))
  have hpre := DerivedCategory.cmCurveSinglePreimage_homology
    (A := ModuleCat.{u} k) (M := ModuleCat.of k k) (N := V) 0 g
  have hb : SM.preimage g = b := by
    apply SM.map_injective
    exact (SM.map_preimage g).trans (hg.trans (congrArg IM.map hcomp))
  have hchain : E₀.inv ≫ v ≫ w ≫ E₁.hom = b :=
    (congrArg (fun z => E₀.inv ≫ z) (Category.assoc v w E₁.hom).symm).trans
      ((congrArg (fun z => E₀.inv ≫ z ≫ E₁.hom) hm.symm).trans (hpre.trans hb))
  have hvalue := congrArg (fun q : ModuleCat.of k k ⟶ V => q (1 : k)) hchain
  have hleft := congrArg (fun q => (q ≫ E₁.hom) (v (E₀.inv (1 : k)))) hH
  have hunit : IY.map η ≫ φ ≫ Z.hom = IY.map (η ≫ f) :=
    (congrArg (fun z => IY.map η ≫ z) hf.symm).trans (IY.map_comp η f).symm
  have heval := cmCurveCoefficientSerreUnitEvaluationLinearMap_apply k ι j V φ
  have heval' : cmCurveCoefficientSerreUnitEvaluationLinearMap k ι j V φ =
      (cmCurveCoefficientSerreSpecSectionsIso k V).hom
        (unitHomGlobalSectionsEquiv Y T h) :=
    heval.trans (congrArg (fun z => (cmCurveCoefficientSerreSpecSectionsIso k V).hom
      (unitHomGlobalSectionsEquiv Y T (SY.preimage z))) hunit)
  exact hleft.trans (hvalue.trans
    ((cmCurveCoefficientSerreAffineSections_map_one k V h).trans heval'.symm))

end AlgebraicGeometry.Scheme.Cohomology
