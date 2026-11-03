/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Cohomology.Projective.TwistCohomology.Coefficients.Model

/-!
# Original twist coefficient unit and section equations

The native ring-unit, augmentation and degree-zero section maps are retained.
-/

@[expose] public section

noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open AlgebraicGeometry TopologicalSpace Opposite HomologicalComplex
open AlgebraicGeometry.ProjectiveSpace AlgebraicGeometry.Scheme.Modules
namespace AlgebraicGeometry.Scheme.Cohomology
universe u
variable (R : Type u) [CommRing R] (ι : Type u) [Finite ι]

attribute [local instance] twistingCoefficientSource twistingCoefficientTarget

/-- The coefficient ring recovers the original twist through the native geometric units. -/
def twistingSheafTensorSelfIso (d : ℤ) :
    twistingSheafTensorCoefficients R ι d (ModuleCat.of R R) ≅ twistingSheaf R ι d :=
  moduleTensorPullbackTildeSelfIso (toSpec R ι) (twistingSheaf R ι d)

/-- The actual finite tensor comparison at the base ring is the native right unitor. -/
@[reassoc]
theorem twistingFiniteCechTensorCoefficientsIso_self (n : ℕ) (e : ι ≃ Fin (n + 1))
    (d : ℤ) :
    (twistingFiniteCechTensorCoefficientsIso R ι n e d (ModuleCat.of R R)).hom ≫
      (moduleFiniteCechFunctor (ProjectiveSpace R ι)
        ((toSpec R ι).appTop.hom.comp (Scheme.ΓSpecIso (.of R)).inv.hom)
        (coordinateOpen R ι) n).map (twistingSheafTensorSelfIso R ι d).hom =
    (NatTrans.mapHomologicalComplex (rightUnitorNatIso (ModuleCat.{u} R)).hom (.up ℤ)).app
      (twistingFiniteCechComplex R ι n d) := by
  let K := moduleCechIntComplex (ProjectiveSpace R ι)
    ((toSpec R ι).appTop.hom.comp (Scheme.ΓSpecIso (.of R)).inv.hom)
    (coordinateOpen R ι) (twistingSheaf R ι d)
  let (q : ℤ) : Module.Flat R (K.X q) := twistingCechIntComplex_flat_X R ι d q
  exact moduleFiniteCechTensorTildeIso_self (toSpec R ι) (twistingSheaf R ι d)
    (coordinateOpen R ι) n e (isAffineOpen_coordinateOpen R ι) (iSup_coordinateOpen_eq_top R ι)

omit [Finite ι] in
/-- Original finite degree-zero homology identifies with the original global sections. -/
def twistingFiniteCechHomologyZeroSectionsIso (n : ℕ) (e : ι ≃ Fin (n + 1)) (d : ℤ) :
    (twistingFiniteCechComplex R ι n d).homology 0 ≅
      (moduleSectionsPresheaf (ProjectiveSpace R ι)
        ((toSpec R ι).appTop.hom.comp (Scheme.ΓSpecIso (.of R)).inv.hom)
        (twistingSheaf R ι d)).obj (op ⊤) :=
  moduleFiniteCechHomologyIso (ProjectiveSpace R ι)
    ((toSpec R ι).appTop.hom.comp (Scheme.ΓSpecIso (.of R)).inv.hom) (coordinateOpen R ι)
    (twistingSheaf R ι d) n e (isAffineOpen_coordinateOpen R ι) (iSup_coordinateOpen_eq_top R ι) 0
        ≪≫
  moduleCechH0Iso (ProjectiveSpace R ι)
    ((toSpec R ι).appTop.hom.comp (Scheme.ΓSpecIso (.of R)).inv.hom) (twistingSheaf R ι d)
    (coordinateOpen R ι) (iSup_coordinateOpen_eq_top R ι)

omit [Finite ι] in
/-- The bottom inclusion retains the original section restriction augmentation. -/
@[reassoc]
theorem twistingFiniteCechHomologyZeroSectionsIso_hom_augmentation
    (n : ℕ) (e : ι ≃ Fin (n + 1)) (d : ℤ) :
    (singleObjXSelf (.up ℤ) (0 : ℤ)
      ((twistingFiniteCechComplex R ι n d).homology 0)).inv ≫
      (CochainComplex.bottomHomologyInclusion (twistingFiniteCechComplex R ι n d) 0).f 0 ≫
      (moduleFiniteCechInclusion (ProjectiveSpace R ι)
        ((toSpec R ι).appTop.hom.comp (Scheme.ΓSpecIso (.of R)).inv.hom) (coordinateOpen R ι)
        (twistingSheaf R ι d) n).f 0 ≫
      ((moduleCechComplex (ProjectiveSpace R ι)
        ((toSpec R ι).appTop.hom.comp (Scheme.ΓSpecIso (.of R)).inv.hom)
        (twistingSheaf R ι d) (coordinateOpen R ι)).extendXIso
          ComplexShape.embeddingUpNat (show ComplexShape.embeddingUpNat.f 0 = (0 : ℤ) from rfl)).hom
              =
    (twistingFiniteCechHomologyZeroSectionsIso R ι n e d).hom ≫
      cechAugmentationZero (ProjectiveSpace R ι) (coordinateOpen R ι)
        (moduleSectionsPresheaf (ProjectiveSpace R ι)
          ((toSpec R ι).appTop.hom.comp (Scheme.ΓSpecIso (.of R)).inv.hom)
          (twistingSheaf R ι d)) := by
  let X : Scheme.{u} := ProjectiveSpace R ι
  let α : R →+* Γ(X, ⊤) :=
    (toSpec R ι).appTop.hom.comp (Scheme.ΓSpecIso (.of R)).inv.hom
  let M : X.Modules := twistingSheaf R ι d
  let C : CochainComplex (ModuleCat.{u} R) ℕ :=
    moduleCechComplex X α M (coordinateOpen R ι)
  let K := twistingFiniteCechComplex R ι n d
  let i := moduleFiniteCechInclusion X α (coordinateOpen R ι) M n
  rw [CochainComplex.bottomHomologyInclusion_f]
  simp only [← Category.assoc, Iso.inv_hom_id, Category.id_comp]
  dsimp only [twistingFiniteCechHomologyZeroSectionsIso, moduleFiniteCechHomologyIso,
    Iso.trans_hom, asIso_hom]
  simp only [Category.assoc]
  rw [moduleCechH0Iso_hom_augmentation]
  apply (cancel_epi (K.homologyπ 0)).mp
  simp only [← Category.assoc]
  rw [homology_π_ι]
  simp only [Category.assoc]
  erw [pOpcyclesIso_hom_inv_id_assoc]
  erw [← cyclesMap_i_assoc i 0, homologyπ_naturality_assoc,
    homologyπ_extendHomologyIso_hom_assoc, CochainComplex.homologyπ_homologyZeroι,
    extendCyclesIso_hom_iCycles]
  rfl


omit [Finite ι] in
/-- Original finite coefficient homology identifies with the original coefficient sections. -/
def twistingFiniteCechTensorHomologyZeroSectionsIso (n : ℕ) (e : ι ≃ Fin (n + 1))
    (d : ℤ) (J : ModuleCat.{u} R) :
    (moduleFiniteCechComplex (ProjectiveSpace R ι)
      ((toSpec R ι).appTop.hom.comp (Scheme.ΓSpecIso (.of R)).inv.hom) (coordinateOpen R ι)
      (twistingSheafTensorCoefficients R ι d J) n).homology 0 ≅
    (moduleSectionsPresheaf (ProjectiveSpace R ι)
      ((toSpec R ι).appTop.hom.comp (Scheme.ΓSpecIso (.of R)).inv.hom)
      (twistingSheafTensorCoefficients R ι d J)).obj (op ⊤) := by
  let X : Scheme.{u} := ProjectiveSpace R ι
  let M := twistingSheafTensorCoefficients R ι d J
  let : M.IsQuasicoherent := isQuasicoherent_moduleTensorLeftFunctor (twistingSheaf R ι d)
    ((Scheme.Modules.pullback (toSpec R ι)).obj (tilde (R := CommRingCat.of R) J))
  exact moduleFiniteCechHomologyIso X
    ((toSpec R ι).appTop.hom.comp (Scheme.ΓSpecIso (.of R)).inv.hom) (coordinateOpen R ι)
    M n e (isAffineOpen_coordinateOpen R ι) (iSup_coordinateOpen_eq_top R ι) 0 ≪≫
  moduleCechH0Iso X ((toSpec R ι).appTop.hom.comp (Scheme.ΓSpecIso (.of R)).inv.hom)
    M (coordinateOpen R ι) (iSup_coordinateOpen_eq_top R ι)

omit [Finite ι] in
/-- Every original single-to-finite-model map retains its original augmentation component. -/
@[reassoc]
theorem twistingFiniteCechTensorHomologyZeroSectionsIso_hom_augmentation
    (n : ℕ) (e : ι ≃ Fin (n + 1)) (d : ℤ) (J A : ModuleCat.{u} R)
    (f : (CochainComplex.singleFunctor (ModuleCat.{u} R) 0).obj A ⟶
      moduleFiniteCechComplex (ProjectiveSpace R ι)
        ((toSpec R ι).appTop.hom.comp (Scheme.ΓSpecIso (.of R)).inv.hom) (coordinateOpen R ι)
        (twistingSheafTensorCoefficients R ι d J) n) :
    (singleObjHomologySelfIso (.up ℤ) (0 : ℤ) A).inv ≫ homologyMap f 0 ≫
      (twistingFiniteCechTensorHomologyZeroSectionsIso R ι n e d J).hom ≫
      cechAugmentationZero (ProjectiveSpace R ι) (coordinateOpen R ι)
        (moduleSectionsPresheaf (ProjectiveSpace R ι)
          ((toSpec R ι).appTop.hom.comp (Scheme.ΓSpecIso (.of R)).inv.hom)
          (twistingSheafTensorCoefficients R ι d J)) =
    (singleObjXSelf (.up ℤ) (0 : ℤ) A).inv ≫ f.f 0 ≫
      (moduleFiniteCechInclusion (ProjectiveSpace R ι)
        ((toSpec R ι).appTop.hom.comp (Scheme.ΓSpecIso (.of R)).inv.hom) (coordinateOpen R ι)
        (twistingSheafTensorCoefficients R ι d J) n).f 0 ≫
      ((moduleCechComplex (ProjectiveSpace R ι)
        ((toSpec R ι).appTop.hom.comp (Scheme.ΓSpecIso (.of R)).inv.hom)
        (twistingSheafTensorCoefficients R ι d J) (coordinateOpen R ι)).extendXIso
          ComplexShape.embeddingUpNat (show ComplexShape.embeddingUpNat.f 0 = (0 : ℤ) from rfl)).hom
              := by
  let X : Scheme.{u} := ProjectiveSpace R ι
  let α : R →+* Γ(X, ⊤) :=
    (toSpec R ι).appTop.hom.comp (Scheme.ΓSpecIso (.of R)).inv.hom
  let N : X.Modules := twistingSheafTensorCoefficients R ι d J
  let C : CochainComplex (ModuleCat.{u} R) ℕ :=
    moduleCechComplex X α N (coordinateOpen R ι)
  let S := (CochainComplex.singleFunctor (ModuleCat.{u} R) 0).obj A
  let i := moduleFiniteCechInclusion X α (coordinateOpen R ι) N n
  dsimp only [twistingFiniteCechTensorHomologyZeroSectionsIso, moduleFiniteCechHomologyIso,
    Iso.trans_hom, asIso_hom]
  simp only [Category.assoc]
  rw [moduleCechH0Iso_hom_augmentation]
  apply (cancel_epi (singleObjCyclesSelfIso (.up ℤ) (0 : ℤ) A).hom).mp
  have hs : (singleObjCyclesSelfIso (.up ℤ) (0 : ℤ) A).hom ≫
      (singleObjXSelf (.up ℤ) (0 : ℤ) A).inv = S.iCycles 0 := by
    simp only [singleObjCyclesSelfIso_hom, Category.assoc, Iso.hom_inv_id, Category.comp_id]
    rfl
  rw [← Category.assoc, singleObjHomologySelfIso_hom_singleObjHomologySelfIso_inv]
  erw [reassoc_of% hs]
  erw [homologyπ_naturality_assoc, homologyπ_naturality_assoc,
    homologyπ_extendHomologyIso_hom_assoc, CochainComplex.homologyπ_homologyZeroι,
    extendCyclesIso_hom_iCycles, cyclesMap_i_assoc, cyclesMap_i_assoc]
  rfl

/-- At the base ring, the same tensor-bottom map retains the original right unitor. -/
@[reassoc]
theorem twistingFiniteCechTensorBottomMap_self (n : ℕ) (e : ι ≃ Fin (n + 1)) (d : ℤ) :
    twistingFiniteCechTensorBottomMap R ι n e d (ModuleCat.of R R) ≫
      (moduleFiniteCechFunctor (ProjectiveSpace R ι)
        ((toSpec R ι).appTop.hom.comp (Scheme.ΓSpecIso (.of R)).inv.hom)
        (coordinateOpen R ι) n).map (twistingSheafTensorSelfIso R ι d).hom =
    (CochainComplex.singleFunctor (ModuleCat.{u} R) 0).map
        (ρ_ ((twistingFiniteCechComplex R ι n d).homology 0)).hom ≫
      CochainComplex.bottomHomologyInclusion (twistingFiniteCechComplex R ι n d) 0 := by
  let K := twistingFiniteCechComplex R ι n d
  let A := K.homology 0
  let S := (CochainComplex.singleFunctor (ModuleCat.{u} R) 0).obj A
  let τ : tensorRight (ModuleCat.of R R) ⟶ 𝟭 (ModuleCat.{u} R) :=
    (rightUnitorNatIso (ModuleCat.{u} R)).hom
  let a := (HomologicalComplex.singleMapHomologicalComplex (tensorRight (ModuleCat.of R R))
    (.up ℤ) (0 : ℤ)).app A
  have hid : (HomologicalComplex.singleMapHomologicalComplex (𝟭 (ModuleCat.{u} R))
      (.up ℤ) (0 : ℤ)).inv.app A = 𝟙 S := by
    rw [HomologicalComplex.singleMapHomologicalComplex_id_inv_app]
    ext i : 1
    rfl
  have hs := HomologicalComplex.natTransMapHomologicalComplex_app_single_obj
    τ (.up ℤ) (0 : ℤ) A
  rw [hid] at hs
  change (NatTrans.mapHomologicalComplex τ (.up ℤ)).app S =
    a.hom ≫ (CochainComplex.singleFunctor (ModuleCat.{u} R) 0).map (ρ_ A).hom ≫ 𝟙 S at hs
  rw [Category.comp_id] at hs
  dsimp only [twistingFiniteCechTensorBottomMap]
  simp only [Category.assoc]
  rw [twistingFiniteCechTensorCoefficientsIso_self]
  have hn := (NatTrans.mapHomologicalComplex τ (.up ℤ)).naturality
    (CochainComplex.bottomHomologyInclusion K 0)
  change a.inv ≫ ((tensorRight (ModuleCat.of R R)).mapHomologicalComplex (.up ℤ)).map
      (CochainComplex.bottomHomologyInclusion K 0) ≫
      (NatTrans.mapHomologicalComplex τ (.up ℤ)).app K =
    (CochainComplex.singleFunctor (ModuleCat.{u} R) 0).map (ρ_ A).hom ≫
      CochainComplex.bottomHomologyInclusion K 0
  rw [hn]
  change a.inv ≫ (NatTrans.mapHomologicalComplex τ (.up ℤ)).app S ≫
      CochainComplex.bottomHomologyInclusion K 0 = _
  rw [hs]
  simp only [Category.assoc, Iso.inv_hom_id_assoc]

private theorem twistingCechIntTensorCoefficientsMap_f_zero
    (d : ℤ) (J : ModuleCat.{u} R) :
    (moduleCechIntTensorTildeMap (toSpec R ι) (twistingSheaf R ι d) J
      (coordinateOpen R ι)).f 0 ≫
      ((moduleCechComplex (ProjectiveSpace R ι)
        ((toSpec R ι).appTop.hom.comp (Scheme.ΓSpecIso (.of R)).inv.hom)
        (twistingSheafTensorCoefficients R ι d J) (coordinateOpen R ι)).extendXIso
          ComplexShape.embeddingUpNat
          (show ComplexShape.embeddingUpNat.f 0 = (0 : ℤ) from rfl)).hom =
    (tensorRight J).map
      ((moduleCechComplex (ProjectiveSpace R ι)
        ((toSpec R ι).appTop.hom.comp (Scheme.ΓSpecIso (.of R)).inv.hom)
        (twistingSheaf R ι d) (coordinateOpen R ι)).extendXIso
          ComplexShape.embeddingUpNat
          (show ComplexShape.embeddingUpNat.f 0 = (0 : ℤ) from rfl)).hom ≫
      (moduleCechTensorTildeMap (toSpec R ι) (twistingSheaf R ι d) J
        (coordinateOpen R ι)).f 0 := by
  let X : Scheme.{u} := ProjectiveSpace R ι
  let α : R →+* Γ(X, ⊤) :=
    (toSpec R ι).appTop.hom.comp (Scheme.ΓSpecIso (.of R)).inv.hom
  let C : CochainComplex (ModuleCat.{u} R) ℕ :=
    moduleCechComplex X α (twistingSheaf R ι d) (coordinateOpen R ι)
  let C' : CochainComplex (ModuleCat.{u} R) ℕ :=
    moduleCechComplex X α (twistingSheafTensorCoefficients R ι d J) (coordinateOpen R ι)
  let F := tensorRight J
  let φ := moduleCechTensorTildeMap (toSpec R ι) (twistingSheaf R ι d) J (coordinateOpen R ι)
  change ((C.mapExtendIso F ComplexShape.embeddingUpNat).hom.f 0 ≫
      (extendMap φ ComplexShape.embeddingUpNat).f 0) ≫
      (C'.extendXIso ComplexShape.embeddingUpNat rfl).hom =
    F.map (C.extendXIso ComplexShape.embeddingUpNat rfl).hom ≫ φ.f 0
  erw [HomologicalComplex.extendMap_f φ ComplexShape.embeddingUpNat
    (show ComplexShape.embeddingUpNat.f 0 = (0 : ℤ) from rfl)]
  simp only [Category.assoc]
  erw [Iso.inv_hom_id, Category.comp_id]
  exact C.mapExtendIso_hom_f_extendXIso_assoc F ComplexShape.embeddingUpNat
    (show ComplexShape.embeddingUpNat.f 0 = (0 : ℤ) from rfl) (φ.f 0)

private theorem twistingCechTensorCoefficientsMap_augmentation_zero
    (d : ℤ) (J : ModuleCat.{u} R) :
    (tensorRight J).map
      (cechAugmentationZero (ProjectiveSpace R ι) (coordinateOpen R ι)
        (moduleSectionsPresheaf (ProjectiveSpace R ι)
          ((toSpec R ι).appTop.hom.comp (Scheme.ΓSpecIso (.of R)).inv.hom)
          (twistingSheaf R ι d))) ≫
      (moduleCechTensorTildeMap (toSpec R ι) (twistingSheaf R ι d) J
        (coordinateOpen R ι)).f 0 =
    (moduleTensorTildeSectionsMap (toSpec R ι) (twistingSheaf R ι d) J).app (op ⊤) ≫
      cechAugmentationZero (ProjectiveSpace R ι) (coordinateOpen R ι)
        (moduleSectionsPresheaf (ProjectiveSpace R ι)
          ((toSpec R ι).appTop.hom.comp (Scheme.ΓSpecIso (.of R)).inv.hom)
          (twistingSheafTensorCoefficients R ι d J)) := by
  let X : Scheme.{u} := ProjectiveSpace R ι
  let p := toSpec R ι
  let α : R →+* Γ(X, ⊤) :=
    p.appTop.hom.comp (Scheme.ΓSpecIso (.of R)).inv.hom
  let M : X.Modules := twistingSheaf R ι d
  let A : ModuleCat.{u} R := (moduleSectionsPresheaf X α M).obj (op ⊤)
  have h := congrArg (fun q => q.f 0)
    (moduleCechTensorTildeMap_augmentation p M J (coordinateOpen R ι))
  have ha : ((HomologicalComplex.singleMapHomologicalComplex (tensorRight J)
      (.up ℕ) (0 : ℕ)).hom.app A).f 0 = 𝟙 ((tensorRight J).obj A) := by
    rw [HomologicalComplex.singleMapHomologicalComplex_hom_app_self]
    simp [singleObjXSelf, singleObjXIsoOfEq]
  simp only [comp_f, CochainComplex.single₀_map_f_zero, cechAugmentation_f_zero] at h
  change _ = ((HomologicalComplex.singleMapHomologicalComplex (tensorRight J)
      (.up ℕ) (0 : ℕ)).hom.app A).f 0 ≫ _ at h
  rw [ha] at h
  erw [Category.id_comp] at h
  exact h

private theorem twistingFiniteCechTensorBottomMap_f_zero
    (n : ℕ) (e : ι ≃ Fin (n + 1)) (d : ℤ) (J : ModuleCat.{u} R) :
    (singleObjXSelf (.up ℤ) (0 : ℤ)
      ((tensorRight J).obj ((twistingFiniteCechComplex R ι n d).homology 0))).inv ≫
      (twistingFiniteCechTensorBottomMap R ι n e d J).f 0 =
    (tensorRight J).map
      ((singleObjXSelf (.up ℤ) (0 : ℤ)
        ((twistingFiniteCechComplex R ι n d).homology 0)).inv ≫
        (CochainComplex.bottomHomologyInclusion (twistingFiniteCechComplex R ι n d) 0).f 0) ≫
      (twistingFiniteCechTensorCoefficientsIso R ι n e d J).hom.f 0 := by
  dsimp only [twistingFiniteCechTensorBottomMap]
  simp only [comp_f, Functor.map_comp, Category.assoc]
  rw [HomologicalComplex.singleMapHomologicalComplex_inv_app_self]
  simp only [Category.assoc]
  erw [Iso.inv_hom_id_assoc]

/- Paste the original component equations without changing any diagram arrow. -/
private theorem coefficientComponentPaste {C : Type*} [Category* C]
    {A₀ A₁ A₂ A₃ A₄ A₅ A₆ A₇ A₈ A₉ A₁₀ : C}
    {x : A₀ ⟶ A₁} {g : A₁ ⟶ A₄} {p : A₀ ⟶ A₂} {q : A₂ ⟶ A₃}
    {μ : A₃ ⟶ A₄} {i : A₃ ⟶ A₅} {i' : A₄ ⟶ A₆} {χ' : A₅ ⟶ A₆}
    {j : A₅ ⟶ A₇} {j' : A₆ ⟶ A₈} {χ : A₇ ⟶ A₈}
    {φ : A₀ ⟶ A₉} {a : A₉ ⟶ A₇} {B : A₉ ⟶ A₁₀} {a' : A₁₀ ⟶ A₈}
    (h₀ : x ≫ g = p ≫ q ≫ μ) (h₁ : μ ≫ i' = i ≫ χ')
    (h₂ : χ' ≫ j' = j ≫ χ) (h₃ : p ≫ q ≫ i ≫ j = φ ≫ a)
    (h₄ : a ≫ χ = B ≫ a') : x ≫ g ≫ i' ≫ j' = φ ≫ B ≫ a' := by
  calc
    x ≫ g ≫ i' ≫ j' = (x ≫ g) ≫ (i' ≫ j') := (Category.assoc _ _ _).symm
    _ = (p ≫ q ≫ μ) ≫ (i' ≫ j') := congrArg (fun f => f ≫ (i' ≫ j')) h₀
    _ = p ≫ q ≫ (μ ≫ i') ≫ j' := by simp only [Category.assoc]
    _ = p ≫ q ≫ (i ≫ χ') ≫ j' := congrArg (fun f => p ≫ q ≫ f ≫ j') h₁
    _ = p ≫ q ≫ i ≫ (χ' ≫ j') := by simp only [Category.assoc]
    _ = p ≫ q ≫ i ≫ (j ≫ χ) := congrArg (fun f => p ≫ q ≫ i ≫ f) h₂
    _ = (p ≫ q ≫ i ≫ j) ≫ χ := by simp only [Category.assoc]
    _ = (φ ≫ a) ≫ χ := congrArg (fun f => f ≫ χ) h₃
    _ = φ ≫ (a ≫ χ) := Category.assoc _ _ _
    _ = φ ≫ (B ≫ a') := congrArg (fun f => φ ≫ f) h₄

private theorem twistingFiniteCechTensorBottomMap_f_zero_sections (n : ℕ)
    (e : ι ≃ Fin (n + 1)) (d : ℤ) (J : ModuleCat.{u} R) :
    (singleObjXSelf (.up ℤ) (0 : ℤ)
      ((tensorRight J).obj ((twistingFiniteCechComplex R ι n d).homology 0))).inv ≫
      (twistingFiniteCechTensorBottomMap R ι n e d J).f 0 ≫
      (moduleFiniteCechInclusion (ProjectiveSpace R ι)
        ((toSpec R ι).appTop.hom.comp (Scheme.ΓSpecIso (.of R)).inv.hom) (coordinateOpen R ι)
        (twistingSheafTensorCoefficients R ι d J) n).f 0 ≫
      ((moduleCechComplex (ProjectiveSpace R ι)
        ((toSpec R ι).appTop.hom.comp (Scheme.ΓSpecIso (.of R)).inv.hom)
        (twistingSheafTensorCoefficients R ι d J) (coordinateOpen R ι)).extendXIso
          ComplexShape.embeddingUpNat
          (show ComplexShape.embeddingUpNat.f 0 = (0 : ℤ) from rfl)).hom =
    (tensorRight J).map (twistingFiniteCechHomologyZeroSectionsIso R ι n e d).hom ≫
      (moduleTensorTildeSectionsMap (toSpec R ι) (twistingSheaf R ι d) J).app (op ⊤) ≫
      cechAugmentationZero (ProjectiveSpace R ι) (coordinateOpen R ι)
        (moduleSectionsPresheaf (ProjectiveSpace R ι)
          ((toSpec R ι).appTop.hom.comp (Scheme.ΓSpecIso (.of R)).inv.hom)
          (twistingSheafTensorCoefficients R ι d J)) := by
  have h0 := twistingFiniteCechTensorBottomMap_f_zero R ι n e d J
  have hμ := congrArg (fun f => f.f 0)
    (twistingFiniteCechTensorCoefficientsIso_hom_ιTruncLE R ι n e d J)
  have hχ := twistingCechIntTensorCoefficientsMap_f_zero R ι d J
  have hM := congrArg (tensorRight J).map
    (twistingFiniteCechHomologyZeroSectionsIso_hom_augmentation R ι n e d)
  have ha := twistingCechTensorCoefficientsMap_augmentation_zero R ι d J
  simp only [CategoryTheory.Functor.map_comp] at h0 hM
  simp only [HomologicalComplex.comp_f] at hμ
  have h0' := h0.trans (Category.assoc _ _ _)
  exact coefficientComponentPaste h0' hμ hχ hM ha

/-- The actual tensor-bottom map retains the literal original global-section tensor map on H0. -/
@[reassoc]
theorem twistingFiniteCechTensorBottomMap_homology_sections (n : ℕ)
    (e : ι ≃ Fin (n + 1)) (d : ℤ) (J : ModuleCat.{u} R) :
    (singleObjHomologySelfIso (.up ℤ) (0 : ℤ)
      ((tensorRight J).obj ((twistingFiniteCechComplex R ι n d).homology 0))).inv ≫
      homologyMap (twistingFiniteCechTensorBottomMap R ι n e d J) 0 ≫
      (twistingFiniteCechTensorHomologyZeroSectionsIso R ι n e d J).hom =
    (tensorRight J).map (twistingFiniteCechHomologyZeroSectionsIso R ι n e d).hom ≫
      (moduleTensorTildeSectionsMap (toSpec R ι) (twistingSheaf R ι d) J).app (op ⊤) := by
  let X : Scheme.{u} := ProjectiveSpace R ι
  let α : R →+* Γ(X, ⊤) :=
    (toSpec R ι).appTop.hom.comp (Scheme.ΓSpecIso (.of R)).inv.hom
  let N : X.Modules := twistingSheafTensorCoefficients R ι d J
  let a := cechAugmentationZero X (coordinateOpen R ι) (moduleSectionsPresheaf X α N)
  let : Mono a := (moduleCechAugmentation_exact_mono X α N (coordinateOpen R ι)
    (iSup_coordinateOpen_eq_top R ι)).2
  apply (cancel_mono a).mp
  simp only [Category.assoc]
  exact (twistingFiniteCechTensorHomologyZeroSectionsIso_hom_augmentation
    R ι n e d J ((tensorRight J).obj ((twistingFiniteCechComplex R ι n d).homology 0))
      (twistingFiniteCechTensorBottomMap R ι n e d J)).trans
    (twistingFiniteCechTensorBottomMap_f_zero_sections R ι n e d J)

/-- The literal global-section tensor map is invertible in the sharp acyclic range. -/
theorem twistingTensorTildeSectionsMap_isIso (n : ℕ) (e : ι ≃ Fin (n + 1))
    (d : ℤ) (hd : -(n : ℤ) ≤ d) (J : ModuleCat.{u} R) :
    IsIso ((moduleTensorTildeSectionsMap (toSpec R ι) (twistingSheaf R ι d) J).app (op ⊤)) := by
  let := twistingFiniteCechTensorBottomMap_quasiIso R ι n e d hd J
  have h := twistingFiniteCechTensorBottomMap_homology_sections R ι n e d J
  have ht : IsIso ((tensorRight J).map
      (twistingFiniteCechHomologyZeroSectionsIso R ι n e d).hom ≫
      (moduleTensorTildeSectionsMap (toSpec R ι) (twistingSheaf R ι d) J).app (op ⊤)) := by
    rw [← h]
    infer_instance
  exact (isIso_comp_left_iff _ _).mp ht

/-- The original global-section tensor map is the coefficient section isomorphism. -/
def twistingTensorTildeSectionsIso (n : ℕ) (e : ι ≃ Fin (n + 1))
    (d : ℤ) (hd : -(n : ℤ) ≤ d) (J : ModuleCat.{u} R) :
    (tensorRight J).obj ((moduleSectionsPresheaf (ProjectiveSpace R ι)
      ((toSpec R ι).appTop.hom.comp (Scheme.ΓSpecIso (.of R)).inv.hom)
      (twistingSheaf R ι d)).obj (op ⊤)) ≅
    (moduleSectionsPresheaf (ProjectiveSpace R ι)
      ((toSpec R ι).appTop.hom.comp (Scheme.ΓSpecIso (.of R)).inv.hom)
      (twistingSheafTensorCoefficients R ι d J)).obj (op ⊤) := by
  let := twistingTensorTildeSectionsMap_isIso R ι n e d hd J
  exact asIso ((moduleTensorTildeSectionsMap (toSpec R ι) (twistingSheaf R ι d) J).app (op ⊤))

/-- The section isomorphism has the literal original section tensor map as its forward map. -/
@[reassoc]
theorem twistingTensorTildeSectionsIso_hom (n : ℕ) (e : ι ≃ Fin (n + 1))
    (d : ℤ) (hd : -(n : ℤ) ≤ d) (J : ModuleCat.{u} R) :
    (twistingTensorTildeSectionsIso R ι n e d hd J).hom =
      (moduleTensorTildeSectionsMap (toSpec R ι) (twistingSheaf R ι d) J).app (op ⊤) := rfl


end AlgebraicGeometry.Scheme.Cohomology
