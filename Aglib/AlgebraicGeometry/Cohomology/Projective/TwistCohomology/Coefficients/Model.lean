/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.Algebra.Homology.CochainComplex.BottomHomology
public import Aglib.Algebra.Homology.Flat.ModuleTensor
public import Aglib.AlgebraicGeometry.Cohomology.Cech.TensorCoefficients
public import Aglib.AlgebraicGeometry.Cohomology.Cech.Finite.Derived
public import Aglib.AlgebraicGeometry.Cohomology.Cech.DegreeZero.Forget
public import Aglib.AlgebraicGeometry.Cohomology.DirectImage.ResolutionSections.Derived
public import Aglib.AlgebraicGeometry.Cohomology.Projective.TwistCohomology
public import Aglib.AlgebraicGeometry.Cohomology.Projective.TwistCohomology.Flat

/-!
# Original bounded twist coefficient models and cohomology

The original finite tensor model, installed derived comparison, sharp vanishing
and degree-zero normalization are retained without changing their definitions.
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

/-- The standard derived-category model for modules on `ProjectiveSpace R ι`, used locally. -/
local instance twistingCoefficientSource :
    HasDerivedCategory.{u + 1} (ProjectiveSpace R ι).Modules := HasDerivedCategory.standard _
/-- The standard derived-category model for `R`-modules, used locally. -/
local instance twistingCoefficientTarget :
    HasDerivedCategory.{u + 1} (ModuleCat.{u} R) := HasDerivedCategory.standard _

/-- The original finite good Cech truncation of the actual integer twist. -/
abbrev twistingFiniteCechComplex (n : ℕ) (d : ℤ) : CochainComplex (ModuleCat.{u} R) ℤ :=
  moduleFiniteCechComplex (ProjectiveSpace R ι)
    ((toSpec R ι).appTop.hom.comp (Scheme.ΓSpecIso (.of R)).inv.hom)
    (coordinateOpen R ι) (twistingSheaf R ι d) n

omit [Finite ι] in
/-- Original degree-zero homology of the finite twist model is free over the base ring. -/
theorem twistingFiniteCechHomologyZero_free (n : ℕ) (e : ι ≃ Fin (n + 1)) (d : ℤ) :
    Module.Free R ((twistingFiniteCechComplex R ι n d).homology 0) := by
  let X := ProjectiveSpace R ι
  let α := (toSpec R ι).appTop.hom.comp (Scheme.ΓSpecIso (.of R)).inv.hom
  let := moduleCohomologyModuleOfHom X α (twistingSheaf R ι d) 0
  let := twistingCohomology_free R ι n e d 0
  exact Module.Free.of_equiv (moduleFiniteCechCohomologyLinearEquiv X α (coordinateOpen R ι)
    (twistingSheaf R ι d) n e (isAffineOpen_coordinateOpen R ι)
    (iSup_coordinateOpen_eq_top R ι) 0).symm

omit [Finite ι] in
/-- Original degree-zero homology of the finite twist model is finite over the base ring. -/
theorem twistingFiniteCechHomologyZero_finite (n : ℕ) (e : ι ≃ Fin (n + 1)) (d : ℤ) :
    Module.Finite R ((twistingFiniteCechComplex R ι n d).homology 0) := by
  let X := ProjectiveSpace R ι
  let α := (toSpec R ι).appTop.hom.comp (Scheme.ΓSpecIso (.of R)).inv.hom
  let := moduleCohomologyModuleOfHom X α (twistingSheaf R ι d) 0
  let := twistingCohomology_finite R ι n e d 0
  exact Module.Finite.equiv (moduleFiniteCechCohomologyLinearEquiv X α (coordinateOpen R ι)
    (twistingSheaf R ι d) n e (isAffineOpen_coordinateOpen R ι)
    (iSup_coordinateOpen_eq_top R ι) 0).symm

omit [Finite ι] in
/-- The original bounded model has no nonzero homology away from zero when `d ≥ -n`. -/
theorem twistingFiniteCechComplex_isZero_homology_of_neg_le_degree (n : ℕ)
    (e : ι ≃ Fin (n + 1)) (d : ℤ) (hd : -(n : ℤ) ≤ d) (i : ℤ) (hi : i ≠ 0) :
    IsZero ((twistingFiniteCechComplex R ι n d).homology i) := by
  let X := ProjectiveSpace R ι
  let α := (toSpec R ι).appTop.hom.comp (Scheme.ΓSpecIso (.of R)).inv.hom
  by_cases hi0 : 0 ≤ i
  · obtain ⟨q, rfl⟩ := Int.eq_ofNat_of_zero_le hi0
    let := moduleCohomologyModuleOfHom X α (twistingSheaf R ι d) q
    let : Subsingleton (Sheaf.H.{u + 1} (moduleAddSheaf X (twistingSheaf R ι d)) q) :=
      twistingCohomology_subsingleton_of_neg_le_degree R ι n e d q hd (by exact_mod_cast hi)
    let : Subsingleton ((twistingFiniteCechComplex R ι n d).homology (q : ℤ)) :=
      (moduleFiniteCechCohomologyLinearEquiv X α (coordinateOpen R ι)
        (twistingSheaf R ι d) n e (isAffineOpen_coordinateOpen R ι)
        (iSup_coordinateOpen_eq_top R ι) q).injective.subsingleton
    exact ModuleCat.isZero_of_subsingleton _
  · rw [← exactAt_iff_isZero_homology]
    exact ShortComplex.exact_of_isZero_X₂ _
      ((twistingFiniteCechComplex R ι n d).isZero_of_isStrictlyGE 0 i (by omega))

omit [Finite ι] in
/-- The same native bottom-homology inclusion is a quasi-isomorphism when `d ≥ -n`. -/
theorem twistingFiniteCechBottomHomologyInclusion_quasiIso (n : ℕ)
    (e : ι ≃ Fin (n + 1)) (d : ℤ) (hd : -(n : ℤ) ≤ d) :
    QuasiIso (CochainComplex.bottomHomologyInclusion (twistingFiniteCechComplex R ι n d) 0) := by
  let K := twistingFiniteCechComplex R ι n d
  let f := CochainComplex.bottomHomologyInclusion K 0
  rw [quasiIso_iff]
  intro i
  rw [quasiIsoAt_iff_isIso_homologyMap]
  by_cases hi : i = 0
  · subst i
    let E := singleObjHomologySelfIso (.up ℤ) (0 : ℤ) (K.homology 0)
    have h : homologyMap f 0 = E.hom := by
      apply (cancel_epi E.inv).mp
      exact (CochainComplex.bottomHomologyInclusion_homology K 0).trans
        E.inv_hom_id.symm
    rw [h]
    infer_instance
  · exact (isZero_single_obj_homology (.up ℤ) (0 : ℤ) (K.homology 0) i hi).isIso
      (twistingFiniteCechComplex_isZero_homology_of_neg_le_degree R ι n e d hd i hi) _

/-- The actual bounded flat cone preserves this same inclusion after tensoring any `J`. -/
theorem twistingFiniteCechBottomHomologyInclusion_tensorRight_quasiIso (n : ℕ)
    (e : ι ≃ Fin (n + 1)) (d : ℤ) (hd : -(n : ℤ) ≤ d) (J : ModuleCat.{u} R) :
    QuasiIso (((tensorRight J).mapHomologicalComplex (.up ℤ)).map
      (CochainComplex.bottomHomologyInclusion (twistingFiniteCechComplex R ι n d) 0)) := by
  let K := twistingFiniteCechComplex R ι n d
  let S := (CochainComplex.singleFunctor (ModuleCat.{u} R) 0).obj (K.homology 0)
  let := twistingFiniteCechHomologyZero_free R ι n e d
  let (q : ℤ) : Module.Flat R (K.X q) := twistingFiniteCechComplex_flat_X R ι n e d q
  let (q : ℤ) : Module.Flat R (S.X q) := by
    by_cases hq : q = 0
    · subst q
      let : Module.Free R (S.X 0) := Module.Free.of_equiv
        (singleObjXSelf (.up ℤ) (0 : ℤ) (K.homology 0)).toLinearEquiv.symm
      infer_instance
    · let := ModuleCat.subsingleton_of_isZero
        (isZero_single_obj_X (.up ℤ) (0 : ℤ) (K.homology 0) q hq)
      infer_instance
  let := twistingFiniteCechBottomHomologyInclusion_quasiIso R ι n e d hd
  exact CochainComplex.quasiIso_tensorRight_of_flat J
    (CochainComplex.bottomHomologyInclusion K 0) 0 (n : ℤ)


/-- The literal twist tensor the native pullback of the base-module sheaf. -/
abbrev twistingSheafTensorCoefficients (d : ℤ) (J : ModuleCat.{u} R) :
    (ProjectiveSpace R ι).Modules :=
  (moduleTensorLeftFunctor (ProjectiveSpace R ι) (twistingSheaf R ι d)).obj
    ((Scheme.Modules.pullback (toSpec R ι)).obj (tilde (R := CommRingCat.of R) J))

/-- The actual installed plus-derived global sections, included in the full derived category. -/
abbrev twistingDerivedGlobalSectionsTensorCoefficients (d : ℤ) (J : ModuleCat.{u} R) :
    DerivedCategory (ModuleCat.{u} R) :=
  DerivedCategory.Plus.ι.obj
    ((moduleGlobalSectionsFunctorOfHom (ProjectiveSpace R ι)
      ((toSpec R ι).appTop.hom.comp (Scheme.ΓSpecIso (.of R)).inv.hom)).rightDerivedFunctorPlus.obj
        ((DerivedCategory.Plus.singleFunctor (ProjectiveSpace R ι).Modules 0).obj
          (twistingSheafTensorCoefficients R ι d J)))

/-- The original finite Cech coefficient tensor isomorphism for the actual twist. -/
def twistingFiniteCechTensorCoefficientsIso (n : ℕ) (e : ι ≃ Fin (n + 1))
    (d : ℤ) (J : ModuleCat.{u} R) :
    ((tensorRight J).mapHomologicalComplex (.up ℤ)).obj (twistingFiniteCechComplex R ι n d) ≅
    moduleFiniteCechComplex (ProjectiveSpace R ι)
      ((toSpec R ι).appTop.hom.comp (Scheme.ΓSpecIso (.of R)).inv.hom) (coordinateOpen R ι)
      (twistingSheafTensorCoefficients R ι d J) n := by
  let K := moduleCechIntComplex (ProjectiveSpace R ι)
    ((toSpec R ι).appTop.hom.comp (Scheme.ΓSpecIso (.of R)).inv.hom) (coordinateOpen R ι)
    (twistingSheaf R ι d)
  let (q : ℤ) : Module.Flat R (K.X q) := twistingCechIntComplex_flat_X R ι d q
  exact moduleFiniteCechTensorTildeIso (toSpec R ι) (twistingSheaf R ι d) J
    (coordinateOpen R ι) n e (isAffineOpen_coordinateOpen R ι) (iSup_coordinateOpen_eq_top R ι)

/-- The actual tensor comparison retains the tensor of the original bounded inclusion. -/
@[reassoc]
theorem twistingFiniteCechTensorCoefficientsIso_hom_ιTruncLE
    (n : ℕ) (e : ι ≃ Fin (n + 1)) (d : ℤ) (J : ModuleCat.{u} R) :
    (twistingFiniteCechTensorCoefficientsIso R ι n e d J).hom ≫
      moduleFiniteCechInclusion (ProjectiveSpace R ι)
        ((toSpec R ι).appTop.hom.comp (Scheme.ΓSpecIso (.of R)).inv.hom)
        (coordinateOpen R ι) (twistingSheafTensorCoefficients R ι d J) n =
    ((tensorRight J).mapHomologicalComplex (.up ℤ)).map
      (moduleFiniteCechInclusion (ProjectiveSpace R ι)
        ((toSpec R ι).appTop.hom.comp (Scheme.ΓSpecIso (.of R)).inv.hom)
        (coordinateOpen R ι) (twistingSheaf R ι d) n) ≫
      moduleCechIntTensorTildeMap (toSpec R ι) (twistingSheaf R ι d) J (coordinateOpen R ι) := by
  let X := ProjectiveSpace R ι
  let α : R →+* Γ(X, ⊤) :=
    (toSpec R ι).appTop.hom.comp (Scheme.ΓSpecIso (.of R)).inv.hom
  let (q : ℤ) : Module.Flat R
      ((moduleCechIntComplex X α (coordinateOpen R ι) (twistingSheaf R ι d)).X q) :=
    twistingCechIntComplex_flat_X R ι d q
  exact moduleFiniteCechTensorTildeIso_hom_ιTruncLE (toSpec R ι) (twistingSheaf R ι d) J
    (coordinateOpen R ι) n e (isAffineOpen_coordinateOpen R ι) (iSup_coordinateOpen_eq_top R ι)

/-- Tensor the same bottom inclusion through the native single and finite-Cech comparisons. -/
def twistingFiniteCechTensorBottomMap (n : ℕ) (e : ι ≃ Fin (n + 1))
    (d : ℤ) (J : ModuleCat.{u} R) :
    (CochainComplex.singleFunctor (ModuleCat.{u} R) 0).obj
      ((tensorRight J).obj ((twistingFiniteCechComplex R ι n d).homology 0)) ⟶
    moduleFiniteCechComplex (ProjectiveSpace R ι)
      ((toSpec R ι).appTop.hom.comp (Scheme.ΓSpecIso (.of R)).inv.hom) (coordinateOpen R ι)
      (twistingSheafTensorCoefficients R ι d J) n :=
  (HomologicalComplex.singleMapHomologicalComplex (tensorRight J) (.up ℤ) (0 : ℤ)).inv.app
      ((twistingFiniteCechComplex R ι n d).homology 0) ≫
    ((tensorRight J).mapHomologicalComplex (.up ℤ)).map
      (CochainComplex.bottomHomologyInclusion (twistingFiniteCechComplex R ι n d) 0) ≫
    (twistingFiniteCechTensorCoefficientsIso R ι n e d J).hom

/-- The original single-to-coefficient-model arrow is a quasi-isomorphism when `d ≥ -n`. -/
theorem twistingFiniteCechTensorBottomMap_quasiIso (n : ℕ) (e : ι ≃ Fin (n + 1))
    (d : ℤ) (hd : -(n : ℤ) ≤ d) (J : ModuleCat.{u} R) :
    QuasiIso (twistingFiniteCechTensorBottomMap R ι n e d J) := by
  let := twistingFiniteCechBottomHomologyInclusion_tensorRight_quasiIso R ι n e d hd J
  dsimp only [twistingFiniteCechTensorBottomMap]
  infer_instance

/-- The original bounded map followed by the original installed-derived comparison. -/
def twistingDerivedGlobalSectionsTensorCoefficientsIso (n : ℕ) (e : ι ≃ Fin (n + 1))
    (d : ℤ) (hd : -(n : ℤ) ≤ d) (J : ModuleCat.{u} R) :
    (DerivedCategory.singleFunctor (ModuleCat.{u} R) 0).obj
      ((tensorRight J).obj ((twistingFiniteCechComplex R ι n d).homology 0)) ≅
    twistingDerivedGlobalSectionsTensorCoefficients R ι d J := by
  let M := twistingSheafTensorCoefficients R ι d J
  let : M.IsQuasicoherent := isQuasicoherent_moduleTensorLeftFunctor
    (twistingSheaf R ι d)
    ((Scheme.Modules.pullback (toSpec R ι)).obj (tilde (R := CommRingCat.of R) J))
  let := twistingFiniteCechTensorBottomMap_quasiIso R ι n e d hd J
  let : IsIso (DerivedCategory.Q.map (twistingFiniteCechTensorBottomMap R ι n e d J)) :=
    (DerivedCategory.isIso_Q_map_iff_quasiIso (ModuleCat.{u} R) _).mpr inferInstance
  exact asIso (DerivedCategory.Q.map (twistingFiniteCechTensorBottomMap R ι n e d J)) ≪≫
    moduleFiniteCechDerivedGlobalSectionsIso (ProjectiveSpace R ι)
      ((toSpec R ι).appTop.hom.comp (Scheme.ΓSpecIso (.of R)).inv.hom) (coordinateOpen R ι)
      M (injectiveResolution M) n e (isAffineOpen_coordinateOpen R ι)
      (iSup_coordinateOpen_eq_top R ι)

/-- The forward derived model retains its original finite Cech comparison factors. -/
@[reassoc]
theorem twistingDerivedGlobalSectionsTensorCoefficientsIso_hom (n : ℕ)
    (e : ι ≃ Fin (n + 1)) (d : ℤ) (hd : -(n : ℤ) ≤ d) (J : ModuleCat.{u} R) :
    letI : (twistingSheafTensorCoefficients R ι d J).IsQuasicoherent :=
      isQuasicoherent_moduleTensorLeftFunctor (twistingSheaf R ι d)
        ((Scheme.Modules.pullback (toSpec R ι)).obj (tilde (R := CommRingCat.of R) J))
    (twistingDerivedGlobalSectionsTensorCoefficientsIso R ι n e d hd J).hom =
    DerivedCategory.Q.map (twistingFiniteCechTensorBottomMap R ι n e d J) ≫
      (moduleFiniteCechDerivedGlobalSectionsIso (ProjectiveSpace R ι)
        ((toSpec R ι).appTop.hom.comp (Scheme.ΓSpecIso (.of R)).inv.hom) (coordinateOpen R ι)
        (twistingSheafTensorCoefficients R ι d J)
        (injectiveResolution (twistingSheafTensorCoefficients R ι d J)) n e
        (isAffineOpen_coordinateOpen R ι) (iSup_coordinateOpen_eq_top R ι)).hom := rfl

/-- Actual derived global sections of the coefficient twist are bounded above by zero. -/
theorem twistingDerivedGlobalSectionsTensorCoefficients_isLE (n : ℕ)
    (e : ι ≃ Fin (n + 1)) (d : ℤ) (hd : -(n : ℤ) ≤ d) (J : ModuleCat.{u} R) :
    (twistingDerivedGlobalSectionsTensorCoefficients R ι d J).IsLE 0 :=
  DerivedCategory.TStructure.t.isLE_of_iso
    (twistingDerivedGlobalSectionsTensorCoefficientsIso R ι n e d hd J) 0

/-- Actual derived global sections of the coefficient twist are bounded below by zero. -/
theorem twistingDerivedGlobalSectionsTensorCoefficients_isGE (n : ℕ)
    (e : ι ≃ Fin (n + 1)) (d : ℤ) (hd : -(n : ℤ) ≤ d) (J : ModuleCat.{u} R) :
    (twistingDerivedGlobalSectionsTensorCoefficients R ι d J).IsGE 0 :=
  DerivedCategory.TStructure.t.isGE_of_iso
    (twistingDerivedGlobalSectionsTensorCoefficientsIso R ι n e d hd J) 0

/-- Original positive sheaf cohomology of the coefficient twist vanishes when `d ≥ -n`. -/
theorem twistingTensorCohomology_subsingleton_of_neg_le_degree (n : ℕ)
    (e : ι ≃ Fin (n + 1)) (d : ℤ) (hd : -(n : ℤ) ≤ d) (J : ModuleCat.{u} R)
    (q : ℕ) (hq : q ≠ 0) :
    Subsingleton (Sheaf.H.{u + 1} (moduleAddSheaf (ProjectiveSpace R ι)
      (twistingSheafTensorCoefficients R ι d J)) q) := by
  let X := ProjectiveSpace R ι
  let α := (toSpec R ι).appTop.hom.comp (Scheme.ΓSpecIso (.of R)).inv.hom
  let M := twistingSheafTensorCoefficients R ι d J
  have hLE := twistingDerivedGlobalSectionsTensorCoefficients_isLE R ι n e d hd J
  rw [DerivedCategory.isLE_iff] at hLE
  have hz := hLE (q : ℤ) (by omega)
  change IsZero ((DerivedCategory.Plus.homologyFunctor (ModuleCat.{u} R) (q : ℤ)).obj
    ((moduleGlobalSectionsFunctorOfHom X α).rightDerivedFunctorPlus.obj
      ((DerivedCategory.Plus.singleFunctor X.Modules 0).obj M))) at hz
  let := ModuleCat.subsingleton_of_isZero hz
  exact (moduleDerivedGlobalSectionsSingleCohomologyLinearEquiv X α
    (injectiveResolution M) q).symm.injective.subsingleton


/-- Native degree-zero homology of the installed derived model is the original tensor module. -/
def twistingTensorHomologyZeroIso (n : ℕ) (e : ι ≃ Fin (n + 1))
    (d : ℤ) (hd : -(n : ℤ) ≤ d) (J : ModuleCat.{u} R) :
    (DerivedCategory.homologyFunctor (ModuleCat.{u} R) 0).obj
      (twistingDerivedGlobalSectionsTensorCoefficients R ι d J) ≅
    (tensorRight J).obj ((twistingFiniteCechComplex R ι n d).homology 0) :=
  ((DerivedCategory.homologyFunctor (ModuleCat.{u} R) 0).mapIso
    (twistingDerivedGlobalSectionsTensorCoefficientsIso R ι n e d hd J)).symm ≪≫
    (DerivedCategory.singleFunctorCompHomologyFunctorIso (ModuleCat.{u} R) 0).app _

/-- Native degree-zero homology preserves the literal forward derived model. -/
@[reassoc]
theorem twistingTensorHomologyZeroIso_hom (n : ℕ) (e : ι ≃ Fin (n + 1))
    (d : ℤ) (hd : -(n : ℤ) ≤ d) (J : ModuleCat.{u} R) :
    (DerivedCategory.homologyFunctor (ModuleCat.{u} R) 0).map
      (twistingDerivedGlobalSectionsTensorCoefficientsIso R ι n e d hd J).hom ≫
      (twistingTensorHomologyZeroIso R ι n e d hd J).hom =
    (DerivedCategory.singleFunctorCompHomologyFunctorIso (ModuleCat.{u} R) 0).hom.app
      ((tensorRight J).obj ((twistingFiniteCechComplex R ι n d).homology 0)) := by
  let E := (DerivedCategory.homologyFunctor (ModuleCat.{u} R) 0).mapIso
    (twistingDerivedGlobalSectionsTensorCoefficientsIso R ι n e d hd J)
  change E.hom ≫ (E.inv ≫ _) = _
  exact E.hom_inv_id_assoc _

/-- Original large sheaf cohomology computes the native tensor model in degree zero. -/
def twistingTensorCohomologyZeroLinearEquiv (n : ℕ) (e : ι ≃ Fin (n + 1))
    (d : ℤ) (hd : -(n : ℤ) ≤ d) (J : ModuleCat.{u} R) :
    letI := moduleCohomologyModuleOfHom (ProjectiveSpace R ι)
      ((toSpec R ι).appTop.hom.comp (Scheme.ΓSpecIso (.of R)).inv.hom)
      (twistingSheafTensorCoefficients R ι d J) 0
    Sheaf.H.{u + 1} (moduleAddSheaf (ProjectiveSpace R ι)
      (twistingSheafTensorCoefficients R ι d J)) 0 ≃ₗ[R]
      ((tensorRight J).obj ((twistingFiniteCechComplex R ι n d).homology 0)) := by
  let X := ProjectiveSpace R ι
  let α := (toSpec R ι).appTop.hom.comp (Scheme.ΓSpecIso (.of R)).inv.hom
  let M := twistingSheafTensorCoefficients R ι d J
  let := moduleCohomologyModuleOfHom X α M 0
  exact (moduleDerivedGlobalSectionsSingleCohomologyLinearEquiv X α
    (injectiveResolution M) 0).symm.trans
      (twistingTensorHomologyZeroIso R ι n e d hd J).toLinearEquiv

/-- Every original coefficient resolution gives the same native degree-zero normalization. -/
theorem twistingTensorCohomologyZeroLinearEquiv_derived_apply (n : ℕ)
    (e : ι ≃ Fin (n + 1)) (d : ℤ) (hd : -(n : ℤ) ≤ d) (J : ModuleCat.{u} R)
    (I : InjectiveResolution (twistingSheafTensorCoefficients R ι d J))
    (x : (DerivedCategory.homologyFunctor (ModuleCat.{u} R) 0).obj
      (twistingDerivedGlobalSectionsTensorCoefficients R ι d J)) :
    twistingTensorCohomologyZeroLinearEquiv R ι n e d hd J
      (moduleDerivedGlobalSectionsSingleCohomologyLinearEquiv (ProjectiveSpace R ι)
        ((toSpec R ι).appTop.hom.comp (Scheme.ΓSpecIso (.of R)).inv.hom) I 0 x) =
      (twistingTensorHomologyZeroIso R ι n e d hd J).hom x := by
  dsimp only [twistingTensorCohomologyZeroLinearEquiv, LinearEquiv.trans_apply]
  rw [moduleDerivedGlobalSectionsSingleCohomologyLinearEquiv_eq _ _ I
    (injectiveResolution (twistingSheafTensorCoefficients R ι d J)) 0,
    LinearEquiv.symm_apply_apply]
  rfl



end AlgebraicGeometry.Scheme.Cohomology
