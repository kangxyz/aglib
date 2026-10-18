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
# Original bounded projective twist models with arbitrary module coefficients

Tensor the original bottom-homology inclusion of the bounded flat Cech model
with an arbitrary base module. In the sharp range `d ≥ -n`, its actual bounded
flat acyclic cone proves the tensor remains a quasi-isomorphism. The original
finite Cech coefficient isomorphism and original finite-derived comparison
then compute the installed derived global sections of `O(d) ⊗ π*tilde J`.

The actual model is natural in `J`. Original finite-inclusion, ring-unit,
and degree-zero augmentation equations retain the original maps. No
Noetherianity, coefficient flatness, relative-flatness assumption or generic
preservation-of-homology instance is needed. Dimension zero is included.
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


/-- Native coefficient morphisms commute with the same original finite tensor comparison. -/
@[reassoc]
theorem twistingFiniteCechTensorCoefficientsIso_naturality (n : ℕ)
    (e : ι ≃ Fin (n + 1)) (d : ℤ) {J J' : ModuleCat.{u} R} (f : J ⟶ J') :
    (NatTrans.mapHomologicalComplex ((tensoringRight (ModuleCat.{u} R)).map f) (.up ℤ)).app
      (twistingFiniteCechComplex R ι n d) ≫
        (twistingFiniteCechTensorCoefficientsIso R ι n e d J').hom =
    (twistingFiniteCechTensorCoefficientsIso R ι n e d J).hom ≫
      (moduleFiniteCechFunctor (ProjectiveSpace R ι)
        ((toSpec R ι).appTop.hom.comp (Scheme.ΓSpecIso (.of R)).inv.hom)
        (coordinateOpen R ι) n).map
        ((moduleTensorLeftFunctor (ProjectiveSpace R ι) (twistingSheaf R ι d)).map
          ((Scheme.Modules.pullback (toSpec R ι)).map (tilde.map f))) := by
  let K := moduleCechIntComplex (ProjectiveSpace R ι)
    ((toSpec R ι).appTop.hom.comp (Scheme.ΓSpecIso (.of R)).inv.hom)
    (coordinateOpen R ι) (twistingSheaf R ι d)
  let (q : ℤ) : Module.Flat R (K.X q) := twistingCechIntComplex_flat_X R ι d q
  exact moduleFiniteCechTensorTildeIso_naturality_coefficients (toSpec R ι)
    (twistingSheaf R ι d) J (coordinateOpen R ι) n e
    (isAffineOpen_coordinateOpen R ι) (iSup_coordinateOpen_eq_top R ι) f

/-- Native coefficient morphisms commute with the same tensor of the bottom inclusion. -/
@[reassoc]
theorem twistingFiniteCechTensorBottomMap_naturality (n : ℕ) (e : ι ≃ Fin (n + 1))
    (d : ℤ) {J J' : ModuleCat.{u} R} (f : J ⟶ J') :
    (CochainComplex.singleFunctor (ModuleCat.{u} R) 0).map
      (((tensoringRight (ModuleCat.{u} R)).map f).app
        ((twistingFiniteCechComplex R ι n d).homology 0)) ≫
      twistingFiniteCechTensorBottomMap R ι n e d J' =
    twistingFiniteCechTensorBottomMap R ι n e d J ≫
      (moduleFiniteCechFunctor (ProjectiveSpace R ι)
        ((toSpec R ι).appTop.hom.comp (Scheme.ΓSpecIso (.of R)).inv.hom)
        (coordinateOpen R ι) n).map
        ((moduleTensorLeftFunctor (ProjectiveSpace R ι) (twistingSheaf R ι d)).map
          ((Scheme.Modules.pullback (toSpec R ι)).map (tilde.map f))) := by
  let K := twistingFiniteCechComplex R ι n d
  let A := K.homology 0
  let S := (CochainComplex.singleFunctor (ModuleCat.{u} R) 0).obj A
  let τ : tensorRight J ⟶ tensorRight J' := (tensoringRight (ModuleCat.{u} R)).map f
  let a := (HomologicalComplex.singleMapHomologicalComplex (tensorRight J) (.up ℤ) (0 : ℤ)).app A
  let a' :=
    (HomologicalComplex.singleMapHomologicalComplex (tensorRight J') (.up ℤ) (0 : ℤ)).app A
  have hs₀ := HomologicalComplex.natTransMapHomologicalComplex_app_single_obj
    τ (.up ℤ) (0 : ℤ) A
  have hs : (CochainComplex.singleFunctor (ModuleCat.{u} R) 0).map (τ.app A) ≫ a'.inv =
      a.inv ≫ (NatTrans.mapHomologicalComplex τ (.up ℤ)).app S := by
    apply (cancel_epi a.hom).mp
    simp only [← Category.assoc, Iso.hom_inv_id, Category.id_comp]
    exact hs₀.symm
  change (CochainComplex.singleFunctor (ModuleCat.{u} R) 0).map (τ.app A) ≫
      (HomologicalComplex.singleMapHomologicalComplex (tensorRight J')
        (.up ℤ) (0 : ℤ)).inv.app A =
    (HomologicalComplex.singleMapHomologicalComplex (tensorRight J)
      (.up ℤ) (0 : ℤ)).inv.app A ≫
      (NatTrans.mapHomologicalComplex τ (.up ℤ)).app S at hs
  have hi := (NatTrans.mapHomologicalComplex τ (.up ℤ)).naturality
    (CochainComplex.bottomHomologyInclusion K 0)
  dsimp only [twistingFiniteCechTensorBottomMap]
  simp only [Category.assoc]
  rw [reassoc_of% hs, ← reassoc_of% hi, twistingFiniteCechTensorCoefficientsIso_naturality]

/-- Original coefficient morphisms commute with the actual installed-derived model. -/
@[reassoc]
theorem twistingDerivedGlobalSectionsTensorCoefficientsIso_naturality (n : ℕ)
    (e : ι ≃ Fin (n + 1)) (d : ℤ) (hd : -(n : ℤ) ≤ d)
    {J J' : ModuleCat.{u} R} (f : J ⟶ J') :
    (DerivedCategory.singleFunctor (ModuleCat.{u} R) 0).map
      (((tensoringRight (ModuleCat.{u} R)).map f).app
        ((twistingFiniteCechComplex R ι n d).homology 0)) ≫
      (twistingDerivedGlobalSectionsTensorCoefficientsIso R ι n e d hd J').hom =
    (twistingDerivedGlobalSectionsTensorCoefficientsIso R ι n e d hd J).hom ≫
      DerivedCategory.Plus.ι.map
        ((moduleGlobalSectionsFunctorOfHom (ProjectiveSpace R ι)
          ((toSpec R ι).appTop.hom.comp (Scheme.ΓSpecIso (.of
              R)).inv.hom)).rightDerivedFunctorPlus.map
            ((DerivedCategory.Plus.singleFunctor (ProjectiveSpace R ι).Modules 0).map
              ((moduleTensorLeftFunctor (ProjectiveSpace R ι) (twistingSheaf R ι d)).map
                ((Scheme.Modules.pullback (toSpec R ι)).map (tilde.map f))))) := by
  let X := ProjectiveSpace R ι
  let α := (toSpec R ι).appTop.hom.comp (Scheme.ΓSpecIso (.of R)).inv.hom
  let M := twistingSheafTensorCoefficients R ι d J
  let N := twistingSheafTensorCoefficients R ι d J'
  let : M.IsQuasicoherent := isQuasicoherent_moduleTensorLeftFunctor (twistingSheaf R ι d)
    ((Scheme.Modules.pullback (toSpec R ι)).obj (tilde (R := CommRingCat.of R) J))
  let : N.IsQuasicoherent := isQuasicoherent_moduleTensorLeftFunctor (twistingSheaf R ι d)
    ((Scheme.Modules.pullback (toSpec R ι)).obj (tilde (R := CommRingCat.of R) J'))
  let g : M ⟶ N := (moduleTensorLeftFunctor X (twistingSheaf R ι d)).map
    ((Scheme.Modules.pullback (toSpec R ι)).map (tilde.map f))
  let I := injectiveResolution M
  let I' := injectiveResolution N
  let φ : InjectiveResolution.Hom I I' g :=
    ⟨InjectiveResolution.desc g I' I, by
      simpa only [CochainComplex.single₀_map_f_zero] using
        InjectiveResolution.desc_commutes_zero g I' I⟩
  have hg := congrArg (fun q => DerivedCategory.Q.map q)
    (twistingFiniteCechTensorBottomMap_naturality R ι n e d f)
  simp only [Functor.map_comp] at hg
  change (DerivedCategory.singleFunctor (ModuleCat.{u} R) 0).map
      (((tensoringRight (ModuleCat.{u} R)).map f).app
        ((twistingFiniteCechComplex R ι n d).homology 0)) ≫
      DerivedCategory.Q.map (twistingFiniteCechTensorBottomMap R ι n e d J') =
    DerivedCategory.Q.map (twistingFiniteCechTensorBottomMap R ι n e d J) ≫
      DerivedCategory.Q.map ((moduleFiniteCechFunctor X α (coordinateOpen R ι) n).map g) at hg
  have hD := moduleFiniteCechDerivedGlobalSectionsIso_naturality X α (coordinateOpen R ι)
    M I n e (isAffineOpen_coordinateOpen R ι) (iSup_coordinateOpen_eq_top R ι) φ
  rw [twistingDerivedGlobalSectionsTensorCoefficientsIso_hom,
    twistingDerivedGlobalSectionsTensorCoefficientsIso_hom]
  simp only [Category.assoc]
  rw [reassoc_of% hg, hD]


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
