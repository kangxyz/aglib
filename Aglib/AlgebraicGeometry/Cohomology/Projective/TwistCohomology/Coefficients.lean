/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Cohomology.Projective.TwistCohomology.Coefficients.Model
public import Aglib.AlgebraicGeometry.Cohomology.Projective.TwistCohomology.Coefficients.Sections

/-!
# Projective twist coefficient models and their naturality

The bounded coefficient model and its cohomology live in `Coefficients.Model`.
The original unit, augmentation and section equations live in `Coefficients.Sections`.
This entry reexports those same native constructions and retains their naturality
in the coefficient module. It defines no second copy of the model or its maps.
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

end AlgebraicGeometry.Scheme.Cohomology
