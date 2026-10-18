/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module
public import Aglib.AlgebraicGeometry.Modules.DerivedCategory.Basic
public import Aglib.AlgebraicGeometry.Cohomology.Functoriality.Modules.Composition
public import Aglib.AlgebraicGeometry.Modules.Restriction.Unit
public import Aglib.AlgebraicGeometry.Modules.QuasiCoherent.Affine.Free.Sections
public import Aglib.AlgebraicGeometry.Modules.ExteriorPower.OpenRestriction
public import Aglib.AlgebraicGeometry.Modules.QuasiCoherent.Affine.Pullback
public import Aglib.AlgebraicGeometry.Cohomology.Modules.Scalars.Iso
public import Aglib.AlgebraicGeometry.Cohomology.Duality.Projective.Derived.Coefficients
public import Aglib.AlgebraicGeometry.Cohomology.Duality.Projective.DifferentialTrace.Restriction

/-!
# Original affine normalization for projective differential traces

For polynomial projective space and any quasicoherent coefficient on its affine
base, actual top-differential cohomology is identified with the original coefficient
sections. The construction retains the old ordered determinant/twist comparison,
the original coefficient residue trace, and the native tilde counit. Native unit
and coefficient naturality extend the original differential open trace to arbitrary
quasicoherent coefficients. The only finite-coordinate choice is induced by e.

The raw coefficient functor and its open/unit comparisons are literal constructions
for arbitrary scheme morphisms. The projective trace statements require the displayed
coordinate order. No Noetherianity or coefficient flatness is assumed.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian HomologicalComplex
open AlgebraicGeometry AlgebraicGeometry.ProjectiveSpace AlgebraicGeometry.Scheme.Modules
open AlgebraicGeometry.Scheme.Modules.Differentials
universe u
attribute [local instance] AlgebraicGeometry.Scheme.Modules.standardHasDerivedCategory
attribute [local instance] AlgebraicGeometry.Scheme.Cohomology.projectiveCoefficientTraceTarget
namespace AlgebraicGeometry.Scheme.Cohomology
open AlgebraicGeometry.Scheme.Modules.Differentials

/-- The actual top relative differential sheaf tensored with the original pulled coefficient. -/
def relativeTopDifferentialCoefficientsFunctor {X Y : Scheme.{u}} (p : X ⟶ Y) (n : ℕ) :
    Y.Modules ⥤ X.Modules :=
  Scheme.Modules.pullback p ⋙
    moduleTensorLeftFunctor X (moduleExteriorPower X (relativeDifferentialSheaf p) n)

/-- The actual exterior differential comparison on a commuting open square. -/
def relativeTopDifferentialRestrictionIso
    {W X Z Y : Scheme.{u}} (p : X ⟶ Y) (i : W ⟶ X) (q : W ⟶ Z) (j : Z ⟶ Y)
    [IsOpenImmersion i] [IsOpenImmersion j] (h : i ≫ p = q ≫ j) (n : ℕ) :
    (moduleExteriorPower X (relativeDifferentialSheaf p) n).restrict i ≅
      moduleExteriorPower W (relativeDifferentialSheaf q) n :=
  (moduleExteriorPowerRestrictionIso i (relativeDifferentialSheaf p) n).symm ≪≫
    (moduleExteriorPowerFunctor W n).mapIso (relativeDifferentialOpenSquareIso p i q j h)

/-- The original restriction comparison for the actual top differential coefficient functor. -/
def relativeTopDifferentialCoefficientsRestrictionIso
    {W X Z Y : Scheme.{u}} (p : X ⟶ Y) (i : W ⟶ X) (q : W ⟶ Z) (j : Z ⟶ Y)
    [IsOpenImmersion i] [IsOpenImmersion j] (h : i ≫ p = q ≫ j) (n : ℕ) :
    relativeTopDifferentialCoefficientsFunctor p n ⋙ Scheme.Modules.restrictFunctor i ≅
      Scheme.Modules.restrictFunctor j ⋙ relativeTopDifferentialCoefficientsFunctor q n :=
  Functor.isoWhiskerLeft (Scheme.Modules.pullback p)
      (tensorRestrictionNatIso i (moduleExteriorPower X (relativeDifferentialSheaf p) n)).symm ≪≫
    Functor.isoWhiskerRight (Scheme.Modules.pullbackOpenSquare i q p j h)
      (moduleTensorLeftFunctor W
        ((moduleExteriorPower X (relativeDifferentialSheaf p) n).restrict i)) ≪≫
    Functor.isoWhiskerLeft (Scheme.Modules.restrictFunctor j ⋙ Scheme.Modules.pullback q)
      ((SheafOfModulesOfCommRing.tensorFunctor W.sheaf).mapIso
        (relativeTopDifferentialRestrictionIso p i q j h n))

/-- The original geometric unit and tensor right unitor at the structure coefficient. -/
def relativeTopDifferentialCoefficientsUnitIso {X Y : Scheme.{u}} (p : X ⟶ Y) (n : ℕ) :
    (relativeTopDifferentialCoefficientsFunctor p n).obj (SheafOfModules.unit Y.ringCatSheaf) ≅
      moduleExteriorPower X (relativeDifferentialSheaf p) n :=
  (moduleTensorLeftFunctor X (moduleExteriorPower X (relativeDifferentialSheaf p) n)).mapIso
    (pullbackUnitIso p) ≪≫
    (SheafOfModulesOfCommRing.tensorRightUnitIso X.sheaf).app _

end AlgebraicGeometry.Scheme.Cohomology

namespace AlgebraicGeometry.Scheme.Cohomology
variable (R : Type u) [CommRing R] (ι : Type u) [Fintype ι]
private abbrev coefficientMap {J J' : ModuleCat.{u} R} (f : J ⟶ J') :=
  (moduleTensorLeftFunctor (ProjectiveSpace R ι)
    (twistingSheaf R ι (-(Fintype.card ι : ℤ)))).map
      ((Scheme.Modules.pullback (toSpec R ι)).map (tilde.map f))

private theorem coefficientTrace_naturality (n : ℕ) (e : ι ≃ Fin (n + 1))
    {J J' : ModuleCat.{u} R} (f : J ⟶ J')
    (x : Sheaf.H.{u + 1} (moduleAddSheaf (ProjectiveSpace R ι)
      (projectiveResidueTwistTensorCoefficients R ι J)) n) :
    projectiveTraceCoefficientsLinearEquiv R ι n e J'
        (Sheaf.H.map ((SheafOfModules.toSheaf (ProjectiveSpace R ι).ringCatSheaf).map
          (coefficientMap R ι f)) n x) =
      f (projectiveTraceCoefficientsLinearEquiv R ι n e J x) := by
  let P := ProjectiveSpace R ι
  let α := (toSpec R ι).appTop.hom.comp (Scheme.ΓSpecIso (.of R)).inv.hom
  let M := projectiveResidueTwistTensorCoefficients R ι J
  let N := projectiveResidueTwistTensorCoefficients R ι J'
  let g : M ⟶ N := coefficientMap R ι f
  let I := injectiveResolution M
  let I' := injectiveResolution N
  let φ : InjectiveResolution.Hom I I' g :=
    ⟨InjectiveResolution.desc g I' I, by
      simpa only [CochainComplex.single₀_map_f_zero] using
        InjectiveResolution.desc_commutes_zero g I' I⟩
  let E := moduleDerivedGlobalSectionsSingleCohomologyLinearEquiv P α I n
  let E' := moduleDerivedGlobalSectionsSingleCohomologyLinearEquiv P α I' n
  obtain ⟨y, rfl⟩ := E.surjective x
  have hn := moduleDerivedGlobalSectionsSingleCohomologyLinearEquiv_naturality P α φ n y
  change E' ((DerivedCategory.Plus.homologyFunctor (ModuleCat.{u} R) (n : ℤ)).map
      ((moduleGlobalSectionsFunctorOfHom P α).rightDerivedFunctorPlus.map
        ((DerivedCategory.Plus.singleFunctor P.Modules 0).map g)) y) =
    Sheaf.H.map ((SheafOfModules.toSheaf P.ringCatSheaf).map g) n (E y) at hn
  rw [← hn]
  rw [projectiveTraceCoefficientsLinearEquiv_derived_apply R ι n e J' I',
    projectiveTraceCoefficientsLinearEquiv_derived_apply R ι n e J I]
  exact ConcreteCategory.congr_hom
    (projectiveDerivedTraceCoefficientsHomologyIso_naturality R ι n e f) y

private theorem coefficientTrace_self (n : ℕ) (e : ι ≃ Fin (n + 1))
    (x : Sheaf.H.{u + 1} (moduleAddSheaf (ProjectiveSpace R ι)
      (projectiveResidueTwistTensorCoefficients R ι (ModuleCat.of R R))) n) :
    projectiveTraceCoefficientsLinearEquiv R ι n e (ModuleCat.of R R) x =
      projectiveTrace R ι n e
        (Sheaf.H.map ((SheafOfModules.toSheaf (ProjectiveSpace R ι).ringCatSheaf).map
          (projectiveResidueTwistTensorSelfIso R ι).hom) n x) := by
  let P := ProjectiveSpace R ι
  let α := (toSpec R ι).appTop.hom.comp (Scheme.ΓSpecIso (.of R)).inv.hom
  let M := projectiveResidueTwistTensorCoefficients R ι (ModuleCat.of R R)
  let N := twistingSheaf R ι (-(Fintype.card ι : ℤ))
  let g : M ⟶ N := (projectiveResidueTwistTensorSelfIso R ι).hom
  let I := injectiveResolution M
  let I' := injectiveResolution N
  let φ : InjectiveResolution.Hom I I' g :=
    ⟨InjectiveResolution.desc g I' I, by
      simpa only [CochainComplex.single₀_map_f_zero] using
        InjectiveResolution.desc_commutes_zero g I' I⟩
  let E := moduleDerivedGlobalSectionsSingleCohomologyLinearEquiv P α I n
  obtain ⟨y, rfl⟩ := E.surjective x
  rw [projectiveTraceCoefficientsLinearEquiv_derived_apply R ι n e (ModuleCat.of R R) I]
  have h := ConcreteCategory.congr_hom
    (projectiveDerivedTraceCoefficientsHomologyIso_self R ι n e) y
  rw [h]
  change projectiveTrace R ι n e
      (moduleDerivedGlobalSectionsSingleCohomologyLinearEquiv P α I' n
        ((DerivedCategory.Plus.homologyFunctor (ModuleCat.{u} R) (n : ℤ)).map
          ((moduleGlobalSectionsFunctorOfHom P α).rightDerivedFunctorPlus.map
            ((DerivedCategory.Plus.singleFunctor P.Modules 0).map g)) y)) = _
  exact congrArg (projectiveTrace R ι n e)
    (moduleDerivedGlobalSectionsSingleCohomologyLinearEquiv_naturality P α φ n y)

end AlgebraicGeometry.Scheme.Cohomology

namespace AlgebraicGeometry.Scheme.Cohomology
variable (R : Type u) [CommRing R] (ι : Type u)

private abbrev differentialCoefficient (n : ℕ) (J : ModuleCat.{u} R) :=
  (relativeTopDifferentialCoefficientsFunctor (toSpec R ι) n).obj (tilde J)

/-- The original ordered determinant/twist comparison on actual tilde coefficients. -/
def projectiveDifferentialCoefficientsTwistingIso (n : ℕ) (e : ι ≃ Fin (n + 1))
    (J : ModuleCat.{u} R) :
    letI : Fintype ι := Fintype.ofEquiv (Fin (n + 1)) e.symm
    (relativeTopDifferentialCoefficientsFunctor (toSpec R ι) n).obj (tilde J) ≅
      projectiveResidueTwistTensorCoefficients R ι J := by
  let : Fintype ι := Fintype.ofEquiv (Fin (n + 1)) e.symm
  exact (moduleTensorRightFunctor (ProjectiveSpace R ι)
    ((Scheme.Modules.pullback (toSpec R ι)).obj (tilde J))).mapIso
      (differentialResidueTwistingIso R ι n e)

private def affineDifferentialTraceCoefficients (n : ℕ) (e : ι ≃ Fin (n + 1))
    (J : ModuleCat.{u} R) :
    letI : Fintype ι := Fintype.ofEquiv (Fin (n + 1)) e.symm
    letI := moduleCohomologyModuleOfHom (ProjectiveSpace R ι)
      ((toSpec R ι).appTop.hom.comp (Scheme.ΓSpecIso (.of R)).inv.hom)
      (differentialCoefficient R ι n J) n
    Sheaf.H.{u + 1} (moduleAddSheaf (ProjectiveSpace R ι)
      (differentialCoefficient R ι n J)) n ≃ₗ[R] J := by
  let : Fintype ι := Fintype.ofEquiv (Fin (n + 1)) e.symm
  exact (moduleCohomologyIsoOfHom (ProjectiveSpace R ι)
    ((toSpec R ι).appTop.hom.comp (Scheme.ΓSpecIso (.of R)).inv.hom)
    (projectiveDifferentialCoefficientsTwistingIso R ι n e J) n).toLinearEquiv.trans
      (projectiveTraceCoefficientsLinearEquiv R ι n e J)

private abbrev differentialCoefficientMap (n : ℕ) {J J' : ModuleCat.{u} R} (f : J ⟶ J') :=
  (relativeTopDifferentialCoefficientsFunctor (toSpec R ι) n).map (tilde.map f)

private theorem affineDifferentialTraceCoefficients_naturality
    (n : ℕ) (e : ι ≃ Fin (n + 1)) {J J' : ModuleCat.{u} R} (f : J ⟶ J')
    (x : Sheaf.H.{u + 1} (moduleAddSheaf (ProjectiveSpace R ι)
      (differentialCoefficient R ι n J)) n) :
    letI : Fintype ι := Fintype.ofEquiv (Fin (n + 1)) e.symm
    affineDifferentialTraceCoefficients R ι n e J'
        (Sheaf.H.map ((SheafOfModules.toSheaf (ProjectiveSpace R ι).ringCatSheaf).map
          (differentialCoefficientMap R ι n f)) n x) =
      f (affineDifferentialTraceCoefficients R ι n e J x) := by
  let : Fintype ι := Fintype.ofEquiv (Fin (n + 1)) e.symm
  have hc : differentialCoefficientMap R ι n f ≫
        (projectiveDifferentialCoefficientsTwistingIso R ι n e J').hom =
      (projectiveDifferentialCoefficientsTwistingIso R ι n e J).hom ≫ coefficientMap R ι f :=
    (moduleTensorCoefficientMap (ProjectiveSpace R ι)
      (differentialResidueTwistingIso R ι n e).hom).naturality
        ((Scheme.Modules.pullback (toSpec R ι)).map (tilde.map f))
  change projectiveTraceCoefficientsLinearEquiv R ι n e J'
      (Sheaf.H.map ((SheafOfModules.toSheaf (ProjectiveSpace R ι).ringCatSheaf).map
        (projectiveDifferentialCoefficientsTwistingIso R ι n e J').hom) n
          (Sheaf.H.map ((SheafOfModules.toSheaf (ProjectiveSpace R ι).ringCatSheaf).map
            (differentialCoefficientMap R ι n f)) n x)) = _
  erw [← Sheaf.H.map_comp_apply, ← Functor.map_comp, hc, Functor.map_comp,
    Sheaf.H.map_comp_apply]
  exact coefficientTrace_naturality R ι n e f _

private theorem tensorPullbackSelfIso_naturality
    {X : Scheme.{u}} (p : X ⟶ Spec (.of R)) {K L : X.Modules} (φ : K ⟶ L) :
    (moduleTensorRightFunctor X ((Scheme.Modules.pullback p).obj
      (tilde (ModuleCat.of R R)))).map φ ≫ (moduleTensorPullbackTildeSelfIso p L).hom =
      (moduleTensorPullbackTildeSelfIso p K).hom ≫ φ := by
  let η : moduleTensorLeftFunctor X K ⟶ moduleTensorLeftFunctor X L :=
    moduleTensorCoefficientMap X φ
  let γ : (Scheme.Modules.pullback p).obj (SheafOfModules.unit (Spec (.of R)).ringCatSheaf) ⟶
      SheafOfModules.unit X.ringCatSheaf := (pullbackUnitIso p).hom
  let ρ := SheafOfModulesOfCommRing.tensorRightUnitIso X.sheaf
  change η.app _ ≫ ((moduleTensorLeftFunctor X L).map γ ≫ ρ.hom.app L) =
    ((moduleTensorLeftFunctor X K).map γ ≫ ρ.hom.app K) ≫ φ
  rw [← Category.assoc, ← η.naturality γ, Category.assoc]
  exact congrArg (fun k => (moduleTensorLeftFunctor X K).map γ ≫ k) (ρ.hom.naturality φ)

private theorem projectiveDifferentialCoefficientsTwistingIso_self (n : ℕ) (e : ι ≃ Fin (n + 1)) :
    letI : Fintype ι := Fintype.ofEquiv (Fin (n + 1)) e.symm
    (projectiveDifferentialCoefficientsTwistingIso R ι n e (ModuleCat.of R R)).hom ≫
        (projectiveResidueTwistTensorSelfIso R ι).hom =
      (moduleTensorPullbackTildeSelfIso (toSpec R ι)
        (moduleExteriorPower (ProjectiveSpace R ι)
          (Scheme.Modules.Differentials.relativeDifferentialSheaf (toSpec R ι)) n)).hom ≫
        (differentialResidueTwistingIso R ι n e).hom := by
  let : Fintype ι := Fintype.ofEquiv (Fin (n + 1)) e.symm
  exact tensorPullbackSelfIso_naturality R (toSpec R ι) (differentialResidueTwistingIso R ι n e).hom

private theorem affineDifferentialTraceCoefficients_self
    (n : ℕ) (e : ι ≃ Fin (n + 1))
    (x : Sheaf.H.{u + 1} (moduleAddSheaf (ProjectiveSpace R ι)
      (differentialCoefficient R ι n (ModuleCat.of R R))) n) :
    letI : Fintype ι := Fintype.ofEquiv (Fin (n + 1)) e.symm
    affineDifferentialTraceCoefficients R ι n e (ModuleCat.of R R) x =
      projectiveTrace R ι n e
        (Sheaf.H.map ((SheafOfModules.toSheaf (ProjectiveSpace R ι).ringCatSheaf).map
          (differentialResidueTwistingIso R ι n e).hom) n
            (Sheaf.H.map ((SheafOfModules.toSheaf (ProjectiveSpace R ι).ringCatSheaf).map
              (moduleTensorPullbackTildeSelfIso (toSpec R ι)
                (moduleExteriorPower (ProjectiveSpace R ι)
                  (Scheme.Modules.Differentials.relativeDifferentialSheaf
                    (toSpec R ι)) n)).hom) n x)) := by
  let : Fintype ι := Fintype.ofEquiv (Fin (n + 1)) e.symm
  change projectiveTraceCoefficientsLinearEquiv R ι n e (ModuleCat.of R R)
    (Sheaf.H.map ((SheafOfModules.toSheaf (ProjectiveSpace R ι).ringCatSheaf).map
      (projectiveDifferentialCoefficientsTwistingIso R ι n e (ModuleCat.of R R)).hom) n x) = _
  rw [coefficientTrace_self, ← Sheaf.H.map_comp_apply, ← Functor.map_comp,
    projectiveDifferentialCoefficientsTwistingIso_self, Functor.map_comp, Sheaf.H.map_comp_apply]
  rfl

end AlgebraicGeometry.Scheme.Cohomology



namespace AlgebraicGeometry.Scheme.Cohomology
open AlgebraicGeometry.Scheme.Modules.Differentials Opposite

private theorem relativeTopDifferentialRestrictionIso_hom_mk
    {W X Z Y : Scheme.{u}} (p : X ⟶ Y) (i : W ⟶ X) (q : W ⟶ Z) (j : Z ⟶ Y)
    [IsOpenImmersion i] [IsOpenImmersion j] (h : i ≫ p = q ≫ j) (n : ℕ)
    (U : W.Opens) (s : Fin n → Γ(relativeDifferentialSheaf p, i ''ᵁ U)) :
    (relativeTopDifferentialRestrictionIso p i q j h n).hom.app U
      ((SheafOfModulesOfCommRing.exteriorPowerMk X.sheaf
        (relativeDifferentialSheaf p) n).app (op (i ''ᵁ U)) s) =
      (SheafOfModulesOfCommRing.exteriorPowerMk W.sheaf
        (relativeDifferentialSheaf q) n).app (op U)
          (fun k => (relativeDifferentialOpenSquareIso p i q j h).hom.app U (s k)) := by
  change ((moduleExteriorPowerFunctor W n).map
    (relativeDifferentialOpenSquareIso p i q j h).hom).app U
      ((moduleExteriorPowerRestrictionIso i (relativeDifferentialSheaf p) n).inv.app U
        ((SheafOfModulesOfCommRing.exteriorPowerMk X.sheaf
          (relativeDifferentialSheaf p) n).app (op (i ''ᵁ U)) s)) = _
  erw [moduleExteriorPowerRestrictionIso_inv_mk]
  exact SheafOfModulesOfCommRing.exteriorPowerFunctor_map_mk W.sheaf
    (relativeDifferentialOpenSquareIso p i q j h).hom n (op U) s

private theorem relativeTopDifferentialRestrictionIso_original
    {R A : Type u} [CommRing R] [CommRing A] (σ : R →+* A) (ι : Type u)
    [IsOpenImmersion (Spec.map (CommRingCat.ofHom σ))] (n : ℕ) :
    letI : IsOpenImmersion (ProjectiveSpace.map σ ι) :=
      MorphismProperty.of_isPullback (ProjectiveSpace.isPullback_map σ ι).flip inferInstance
    (Scheme.Modules.restrictAdjunction (ProjectiveSpace.map σ ι)).homEquiv _ _
      (relativeTopDifferentialRestrictionIso (toSpec R ι) (ProjectiveSpace.map σ ι) (toSpec A ι)
        (Spec.map (CommRingCat.ofHom σ)) (ProjectiveSpace.map_toSpec σ ι) n).hom =
      differentialTopBaseOpenCoefficient σ ι n := by
  let : IsOpenImmersion (ProjectiveSpace.map σ ι) :=
    MorphismProperty.of_isPullback (ProjectiveSpace.isPullback_map σ ι).flip inferInstance
  let g := ProjectiveSpace.map σ ι
  apply SheafOfModulesOfCommRing.exteriorPower_hom_ext
    (ProjectiveSpace R ι).sheaf (relativeDifferentialSheaf (toSpec R ι)) _ n
  intro U s
  erw [differentialTopBaseOpenCoefficient_wedge]
  rw [Adjunction.homEquiv_unit]
  change (relativeTopDifferentialRestrictionIso (toSpec R ι) g (toSpec A ι)
    (Spec.map (CommRingCat.ofHom σ)) (ProjectiveSpace.map_toSpec σ ι) n).hom.app
      (g ⁻¹ᵁ U.unop)
        ((moduleExteriorPower (ProjectiveSpace R ι)
          (relativeDifferentialSheaf (toSpec R ι)) n).val.map
            (homOfLE (g.image_preimage_le U.unop)).op
              ((SheafOfModulesOfCommRing.exteriorPowerMk (ProjectiveSpace R ι).sheaf
                (relativeDifferentialSheaf (toSpec R ι)) n).app U s)) = _
  have hmk := SheafOfModulesOfCommRing.exteriorPowerMk_naturality
    (ProjectiveSpace R ι).sheaf (relativeDifferentialSheaf (toSpec R ι)) n
    (homOfLE (g.image_preimage_le U.unop)).op s
  change (moduleExteriorPower (ProjectiveSpace R ι)
      (relativeDifferentialSheaf (toSpec R ι)) n).val.map
    (homOfLE (g.image_preimage_le U.unop)).op
      ((SheafOfModulesOfCommRing.exteriorPowerMk (ProjectiveSpace R ι).sheaf
        (relativeDifferentialSheaf (toSpec R ι)) n).app U s) = _ at hmk
  rw [hmk]
  erw [relativeTopDifferentialRestrictionIso_hom_mk]
  congr 1
  funext k
  rw [differentialBaseOpenCoefficient_eq_restrict, Adjunction.homEquiv_unit]
  rfl

end AlgebraicGeometry.Scheme.Cohomology

namespace AlgebraicGeometry.Scheme.Cohomology
variable (R : Type u) [CommRing R] (ι : Type u) (n : ℕ) (e : ι ≃ Fin (n + 1))

/-- Original top cohomology of the actual differential coefficient, for every affine QC sheaf. -/
def projectiveAffineDifferentialTraceLinearEquiv
    (N : (Spec (.of R)).Modules) [N.IsQuasicoherent] :
    letI := moduleCohomologyModuleOfHom (ProjectiveSpace R ι)
      ((toSpec R ι).appTop.hom.comp (Scheme.ΓSpecIso (.of R)).inv.hom)
      ((relativeTopDifferentialCoefficientsFunctor (toSpec R ι) n).obj N) n
    Sheaf.H.{u + 1} (moduleAddSheaf (ProjectiveSpace R ι)
      ((relativeTopDifferentialCoefficientsFunctor (toSpec R ι) n).obj N)) n ≃ₗ[R]
        moduleSpecΓFunctor.obj N := by
  let : Fintype ι := Fintype.ofEquiv (Fin (n + 1)) e.symm
  let E := (relativeTopDifferentialCoefficientsFunctor (toSpec R ι) n).mapIso
    (asIso N.fromTildeΓ).symm
  exact (moduleCohomologyIsoOfHom (ProjectiveSpace R ι)
    ((toSpec R ι).appTop.hom.comp (Scheme.ΓSpecIso (.of R)).inv.hom) E n).toLinearEquiv.trans
      ((moduleCohomologyIsoOfHom (ProjectiveSpace R ι)
        ((toSpec R ι).appTop.hom.comp (Scheme.ΓSpecIso (.of R)).inv.hom)
        (projectiveDifferentialCoefficientsTwistingIso R ι n e
          (moduleSpecΓFunctor.obj N)) n).toLinearEquiv.trans
          (projectiveTraceCoefficientsLinearEquiv R ι n e (moduleSpecΓFunctor.obj N)))

/-- The original coefficient morphism commutes with the affine trace. -/
theorem projectiveAffineDifferentialTraceLinearEquiv_naturality
    {N N' : (Spec (.of R)).Modules} [N.IsQuasicoherent] [N'.IsQuasicoherent] (f : N ⟶ N')
    (x : Sheaf.H.{u + 1} (moduleAddSheaf (ProjectiveSpace R ι)
      ((relativeTopDifferentialCoefficientsFunctor (toSpec R ι) n).obj N)) n) :
    projectiveAffineDifferentialTraceLinearEquiv R ι n e N'
      (Sheaf.H.map ((SheafOfModules.toSheaf (ProjectiveSpace R ι).ringCatSheaf).map
        ((relativeTopDifferentialCoefficientsFunctor (toSpec R ι) n).map f)) n x) =
      (moduleSpecΓFunctor.map f) (projectiveAffineDifferentialTraceLinearEquiv R ι n e N x) := by
  let : Fintype ι := Fintype.ofEquiv (Fin (n + 1)) e.symm
  let F := relativeTopDifferentialCoefficientsFunctor (toSpec R ι) n
  have hc : f ≫ (asIso N'.fromTildeΓ).inv =
      (asIso N.fromTildeΓ).inv ≫ tilde.map (moduleSpecΓFunctor.map f) := by
    apply (cancel_epi N.fromTildeΓ).mp
    have hn : tilde.map (moduleSpecΓFunctor.map f) ≫ N'.fromTildeΓ = N.fromTildeΓ ≫ f :=
      fromTildeΓNatTrans.naturality f
    rw [← Category.assoc, ← hn]
    change tilde.map (moduleSpecΓFunctor.map f) ≫ (asIso N'.fromTildeΓ).hom ≫
      (asIso N'.fromTildeΓ).inv = (asIso N.fromTildeΓ).hom ≫
        (asIso N.fromTildeΓ).inv ≫ tilde.map (moduleSpecΓFunctor.map f)
    simp only [Iso.hom_inv_id, Category.comp_id, Iso.hom_inv_id_assoc]
  have hF := congrArg F.map hc
  simp only [Functor.map_comp] at hF
  change affineDifferentialTraceCoefficients R ι n e (moduleSpecΓFunctor.obj N')
    (Sheaf.H.map ((SheafOfModules.toSheaf (ProjectiveSpace R ι).ringCatSheaf).map
      (F.map (asIso N'.fromTildeΓ).inv)) n
      (Sheaf.H.map ((SheafOfModules.toSheaf (ProjectiveSpace R ι).ringCatSheaf).map
        (F.map f)) n x)) = _
  rw [← Sheaf.H.map_comp_apply, ← Functor.map_comp, hF, Functor.map_comp,
    Sheaf.H.map_comp_apply]
  exact affineDifferentialTraceCoefficients_naturality R ι n e (moduleSpecΓFunctor.map f) _

private theorem projectiveAffineDifferentialTraceLinearEquiv_apply
    (N : (Spec (.of R)).Modules) [N.IsQuasicoherent]
    (x : Sheaf.H.{u + 1} (moduleAddSheaf (ProjectiveSpace R ι)
      ((relativeTopDifferentialCoefficientsFunctor (toSpec R ι) n).obj N)) n) :
    projectiveAffineDifferentialTraceLinearEquiv R ι n e N x =
      affineDifferentialTraceCoefficients R ι n e (moduleSpecΓFunctor.obj N)
        (Sheaf.H.map ((SheafOfModules.toSheaf (ProjectiveSpace R ι).ringCatSheaf).map
          ((relativeTopDifferentialCoefficientsFunctor (toSpec R ι) n).map
            (asIso N.fromTildeΓ).inv)) n x) := rfl

private theorem tildeCounit_inv {A : CommRingCat.{u}} (J : ModuleCat.{u} A) :
    (asIso (tilde J).fromTildeΓ).inv =
      (tilde.functor A).map ((tilde.adjunction (R := A)).unit.app J) := by
  apply (cancel_mono (tilde J).fromTildeΓ).mp
  exact (asIso (tilde J).fromTildeΓ).inv_hom_id.trans
    ((tilde.adjunction (R := A)).left_triangle_components J).symm

private theorem projectiveAffineDifferentialTraceLinearEquiv_tilde (J : ModuleCat.{u} R)
    (x : Sheaf.H.{u + 1} (moduleAddSheaf (ProjectiveSpace R ι)
      (differentialCoefficient R ι n J)) n) :
    projectiveAffineDifferentialTraceLinearEquiv R ι n e (tilde J) x =
      (tilde.toTildeΓNatIso (R := .of R)).hom.app J
        (affineDifferentialTraceCoefficients R ι n e J x) := by
  let : Fintype ι := Fintype.ofEquiv (Fin (n + 1)) e.symm
  rw [projectiveAffineDifferentialTraceLinearEquiv_apply, tildeCounit_inv]
  exact affineDifferentialTraceCoefficients_naturality R ι n e
    ((tilde.toTildeΓNatIso (R := .of R)).hom.app J) x

private def affineDifferentialUnitClass :
    Sheaf.H.{u + 1} (moduleAddSheaf (ProjectiveSpace R ι)
      ((relativeTopDifferentialCoefficientsFunctor (toSpec R ι) n).obj
        (SheafOfModules.unit (Spec (.of R)).ringCatSheaf))) n :=
  (affineDifferentialTraceCoefficients R ι n e (ModuleCat.of R R)).symm 1

private def affineDifferentialUnitTrace
    (x : Sheaf.H.{u + 1} (moduleAddSheaf (ProjectiveSpace R ι)
      ((relativeTopDifferentialCoefficientsFunctor (toSpec R ι) n).obj
        (SheafOfModules.unit (Spec (.of R)).ringCatSheaf))) n) : R :=
  affineDifferentialTraceCoefficients R ι n e (ModuleCat.of R R) x

private theorem affineDifferentialUnitTrace_injective :
    Function.Injective (affineDifferentialUnitTrace R ι n e) :=
  (affineDifferentialTraceCoefficients R ι n e (ModuleCat.of R R)).injective

private theorem affineDifferentialUnitTrace_class :
    affineDifferentialUnitTrace R ι n e (affineDifferentialUnitClass R ι n e) = 1 :=
  (affineDifferentialTraceCoefficients R ι n e (ModuleCat.of R R)).apply_symm_apply 1

private theorem affineDifferentialUnitTrace_apply
    (x : Sheaf.H.{u + 1} (moduleAddSheaf (ProjectiveSpace R ι)
      ((relativeTopDifferentialCoefficientsFunctor (toSpec R ι) n).obj
        (SheafOfModules.unit (Spec (.of R)).ringCatSheaf))) n) :
    letI : Fintype ι := Fintype.ofEquiv (Fin (n + 1)) e.symm
    affineDifferentialUnitTrace R ι n e x = projectiveTrace R ι n e
      (Sheaf.H.map ((SheafOfModules.toSheaf (ProjectiveSpace R ι).ringCatSheaf).map
        (differentialResidueTwistingIso R ι n e).hom) n
          (Sheaf.H.map ((SheafOfModules.toSheaf (ProjectiveSpace R ι).ringCatSheaf).map
            (relativeTopDifferentialCoefficientsUnitIso (toSpec R ι) n).hom) n x)) :=
  affineDifferentialTraceCoefficients_self R ι n e x

private theorem projectiveAffineDifferentialTraceLinearEquiv_unitClass :
    projectiveAffineDifferentialTraceLinearEquiv R ι n e (tilde (ModuleCat.of R R))
      (affineDifferentialUnitClass R ι n e) =
        (1 : Γ(Spec (.of R), ⊤)) := by
  have h := projectiveAffineDifferentialTraceLinearEquiv_tilde R ι n e (ModuleCat.of R R)
    (affineDifferentialUnitClass R ι n e)
  have hc : affineDifferentialTraceCoefficients R ι n e (ModuleCat.of R R)
      (affineDifferentialUnitClass R ι n e) = 1 := affineDifferentialUnitTrace_class R ι n e
  rw [hc] at h
  exact h.trans (tilde_toOpen_self_one ⊤)

private theorem projectiveAffineDifferentialTraceLinearEquiv_unitMap
    {N : (Spec (.of R)).Modules} [N.IsQuasicoherent]
    (s : (SheafOfModules.unit (Spec (.of R)).ringCatSheaf : (Spec (.of R)).Modules) ⟶ N) :
    projectiveAffineDifferentialTraceLinearEquiv R ι n e N
      (Sheaf.H.map ((SheafOfModules.toSheaf (ProjectiveSpace R ι).ringCatSheaf).map
        ((relativeTopDifferentialCoefficientsFunctor (toSpec R ι) n).map s)) n
          (affineDifferentialUnitClass R ι n e)) =
      unitHomGlobalSectionsEquiv (Spec (.of R)) N s := by
  let : (SheafOfModules.unit (Spec (.of R)).ringCatSheaf).IsQuasicoherent :=
    inferInstanceAs (tilde (R := CommRingCat.of R) (ModuleCat.of R R)).IsQuasicoherent
  have hn := projectiveAffineDifferentialTraceLinearEquiv_naturality R ι n e s
    (affineDifferentialUnitClass R ι n e)
  exact hn.trans (congrArg (fun t => (moduleSpecΓFunctor.map s) t)
    (projectiveAffineDifferentialTraceLinearEquiv_unitClass R ι n e))

private theorem projectiveAffineDifferentialTraceLinearEquiv_generator
    (N : (Spec (.of R)).Modules) [N.IsQuasicoherent]
    (x : Sheaf.H.{u + 1} (moduleAddSheaf (ProjectiveSpace R ι)
      ((relativeTopDifferentialCoefficientsFunctor (toSpec R ι) n).obj N)) n) :
    x = Sheaf.H.map ((SheafOfModules.toSheaf (ProjectiveSpace R ι).ringCatSheaf).map
      ((relativeTopDifferentialCoefficientsFunctor (toSpec R ι) n).map
        ((unitHomGlobalSectionsEquiv (Spec (.of R)) N).symm
          (projectiveAffineDifferentialTraceLinearEquiv R ι n e N x)))) n
            (affineDifferentialUnitClass R ι n e) := by
  let m := projectiveAffineDifferentialTraceLinearEquiv R ι n e N x
  let s : tilde (ModuleCat.of R R) ⟶ N := (unitHomGlobalSectionsEquiv (Spec (.of R)) N).symm m
  let c := affineDifferentialUnitClass R ι n e
  have hn := projectiveAffineDifferentialTraceLinearEquiv_naturality R ι n e s c
  have hu := projectiveAffineDifferentialTraceLinearEquiv_unitClass R ι n e
  change projectiveAffineDifferentialTraceLinearEquiv R ι n e (tilde (ModuleCat.of R R)) c =
    (1 : Γ(Spec (.of R), ⊤)) at hu
  rw [hu] at hn
  apply (projectiveAffineDifferentialTraceLinearEquiv R ι n e N).injective
  change m = projectiveAffineDifferentialTraceLinearEquiv R ι n e N
    (Sheaf.H.map ((SheafOfModules.toSheaf (ProjectiveSpace R ι).ringCatSheaf).map
      ((relativeTopDifferentialCoefficientsFunctor (toSpec R ι) n).map s)) n c)
  exact ((unitHomGlobalSectionsEquiv (Spec (.of R)) N).apply_symm_apply m).symm.trans hn.symm

end AlgebraicGeometry.Scheme.Cohomology



namespace AlgebraicGeometry.Scheme.Cohomology
open AlgebraicGeometry.Scheme.Modules.Differentials Opposite
open AlgebraicGeometry.Scheme.Modules.Invertible

private theorem pullbackOpenSquare_unit
    {W X Z Y : Scheme.{u}} (p : X ⟶ Y) (i : W ⟶ X) (q : W ⟶ Z) (j : Z ⟶ Y)
    [IsOpenImmersion i] [IsOpenImmersion j] (h : i ≫ p = q ≫ j) :
    (pullbackOpenSquare i q p j h).hom.app (SheafOfModules.unit Y.ringCatSheaf) ≫
      (Scheme.Modules.pullback q).map (restrictUnitIso j).hom ≫ (pullbackUnitIso q).hom =
    (Scheme.Modules.restrictFunctor i).map (pullbackUnitIso p).hom ≫ (restrictUnitIso i).hom := by
  dsimp only [pullbackOpenSquare, Iso.trans_hom, Iso.symm_hom, NatTrans.comp_app,
    Functor.isoWhiskerLeft_hom, Functor.isoWhiskerRight_hom, Functor.whiskerLeft_app,
    Functor.whiskerRight_app]
  simp only [Category.assoc]
  rw [← Functor.map_comp_assoc, restrictFunctorIsoPullback_inv_unit]
  change _ ≫ _ ≫ _ ≫ (pullbackComp q j).inv.app _ ≫
    (Scheme.Modules.pullback q).map (pullbackUnitIso j).hom ≫ (pullbackUnitIso q).hom = _
  rw [← pullbackUnitIso_comp q j, Iso.inv_hom_id_app_assoc, pullbackUnitIso_congr,
    pullbackUnitIso_comp]
  rw [← Category.assoc, ← (restrictFunctorIsoPullback i).hom.naturality]
  simp only [Category.assoc]
  exact congrArg (fun k => (Scheme.Modules.restrictFunctor i).map (pullbackUnitIso p).hom ≫ k)
    (restrictFunctorIsoPullback_hom_unit i)

private theorem tensorRightUnit_restrict {X Y : Scheme.{u}} (i : X ⟶ Y)
    [IsOpenImmersion i] (K : Y.Modules) :
    (tensorRestrictionIso i K (SheafOfModules.unit Y.ringCatSheaf)).hom ≫
      (Scheme.Modules.restrictFunctor i).map
        ((SheafOfModulesOfCommRing.tensorRightUnitIso Y.sheaf).hom.app K) =
    (moduleTensorLeftFunctor X (K.restrict i)).map (restrictUnitIso i).hom ≫
      (SheafOfModulesOfCommRing.tensorRightUnitIso X.sheaf).hom.app (K.restrict i) := by
  apply moduleTensor_hom_ext
  intro U k r
  let ρY : (moduleTensorLeftFunctor Y K).obj (SheafOfModules.unit Y.ringCatSheaf) ⟶ K :=
    (SheafOfModulesOfCommRing.tensorRightUnitIso Y.sheaf).hom.app K
  let ρX : (moduleTensorLeftFunctor X (K.restrict i)).obj (SheafOfModules.unit X.ringCatSheaf) ⟶
      K.restrict i := (SheafOfModulesOfCommRing.tensorRightUnitIso X.sheaf).hom.app (K.restrict i)
  have hl := congrArg (fun z => ρY.val.app (op (i ''ᵁ U)) z)
    (tensorRestrictionIso_section i K (SheafOfModules.unit Y.ringCatSheaf) U k r)
  have hr := congrArg (fun z => ρX.val.app (op U) z)
    (moduleTensorLeftFunctor_map_section (K.restrict i) (restrictUnitIso i).hom U k r)
  have hu := tensorRightUnitIso_hom_section X (K.restrict i) U k
    ((restrictUnitIso i).hom.val.app (op U) r)
  have hs : (show Γ(X, U) from (restrictUnitIso i).hom.val.app (op U) r) • k =
      (show Γ(Y, i ''ᵁ U) from r) • (show Γ(K, i ''ᵁ U) from k) := by
    change (i.appIso U).inv.hom ((i.appIso U).hom.hom r) • (show Γ(K, i ''ᵁ U) from k) = _
    exact congrArg (fun z : Γ(Y, i ''ᵁ U) => z • (show Γ(K, i ''ᵁ U) from k))
      (Iso.hom_inv_id_apply (i.appIso U) r)
  exact (hl.trans (tensorRightUnitIso_hom_section Y K (i ''ᵁ U) k r)).trans
    ((hr.trans (hu.trans hs)).symm)

end AlgebraicGeometry.Scheme.Cohomology



namespace AlgebraicGeometry.Scheme.Cohomology
open AlgebraicGeometry.Scheme.Modules.Differentials

private theorem coefficientRightUnit {W : Scheme.{u}} {B K L : W.Modules}
    (b : B ⟶ SheafOfModules.unit W.ringCatSheaf) (d : K ⟶ L) :
    (moduleTensorCoefficientMap W d).app B ≫ (moduleTensorLeftFunctor W L).map b ≫
        (SheafOfModulesOfCommRing.tensorRightUnitIso W.sheaf).hom.app L =
      (moduleTensorLeftFunctor W K).map b ≫
        (SheafOfModulesOfCommRing.tensorRightUnitIso W.sheaf).hom.app K ≫ d := by
  let η := moduleTensorCoefficientMap W d
  let ρ := SheafOfModulesOfCommRing.tensorRightUnitIso W.sheaf
  have ht : η.app B ≫ (moduleTensorLeftFunctor W L).map b =
      (moduleTensorLeftFunctor W K).map b ≫ η.app _ := (η.naturality b).symm
  have hr : η.app (SheafOfModules.unit W.ringCatSheaf) ≫ ρ.hom.app L =
      ρ.hom.app K ≫ d := ρ.hom.naturality d
  change η.app B ≫ _ ≫ ρ.hom.app L = _
  rw [← Category.assoc, ht, Category.assoc, hr]

private theorem tensorRestriction_unit_map {W X : Scheme.{u}} (i : W ⟶ X)
    [IsOpenImmersion i] {A K : X.Modules} {B : W.Modules}
    (a : A ⟶ SheafOfModules.unit X.ringCatSheaf)
    (b : B ⟶ SheafOfModules.unit W.ringCatSheaf) (μ : A.restrict i ⟶ B)
    (hb : μ ≫ b = (Scheme.Modules.restrictFunctor i).map a ≫ (restrictUnitIso i).hom) :
    (tensorRestrictionIso i K A).inv ≫ (moduleTensorLeftFunctor W (K.restrict i)).map μ ≫
        (moduleTensorLeftFunctor W (K.restrict i)).map b ≫
        (SheafOfModulesOfCommRing.tensorRightUnitIso W.sheaf).hom.app (K.restrict i) =
      (Scheme.Modules.restrictFunctor i).map
        ((moduleTensorLeftFunctor X K).map a ≫
          (SheafOfModulesOfCommRing.tensorRightUnitIso X.sheaf).hom.app K) := by
  let ρ := SheafOfModulesOfCommRing.tensorRightUnitIso W.sheaf
  have ha := (tensorRestrictionNatIso i K).inv.naturality a
  change (Scheme.Modules.restrictFunctor i).map ((moduleTensorLeftFunctor X K).map a) ≫
    (tensorRestrictionIso i K (SheafOfModules.unit X.ringCatSheaf)).inv =
      (tensorRestrictionIso i K A).inv ≫
        (moduleTensorLeftFunctor W (K.restrict i)).map
          ((Scheme.Modules.restrictFunctor i).map a) at ha
  have hu : (tensorRestrictionIso i K (SheafOfModules.unit X.ringCatSheaf)).inv ≫
      (moduleTensorLeftFunctor W (K.restrict i)).map (restrictUnitIso i).hom ≫
        ρ.hom.app (K.restrict i) =
      (Scheme.Modules.restrictFunctor i).map
        ((SheafOfModulesOfCommRing.tensorRightUnitIso X.sheaf).hom.app K) := by
    rw [← tensorRightUnit_restrict, Iso.inv_hom_id_assoc]
  rw [← Functor.map_comp_assoc, hb, Functor.map_comp]
  have hh := congrArg (fun z => z ≫
    (moduleTensorLeftFunctor W (K.restrict i)).map (restrictUnitIso i).hom ≫
      ρ.hom.app (K.restrict i)) ha.symm
  calc
    _ = (Scheme.Modules.restrictFunctor i).map ((moduleTensorLeftFunctor X K).map a) ≫
        (tensorRestrictionIso i K (SheafOfModules.unit X.ringCatSheaf)).inv ≫
        (moduleTensorLeftFunctor W (K.restrict i)).map (restrictUnitIso i).hom ≫
          ρ.hom.app (K.restrict i) := by simpa only [Category.assoc] using hh
    _ = _ := by rw [hu, Functor.map_comp]

private theorem tensorRestriction_unit_compare {W X : Scheme.{u}} (i : W ⟶ X)
    [IsOpenImmersion i] {A K : X.Modules} {B L : W.Modules}
    (a : A ⟶ SheafOfModules.unit X.ringCatSheaf)
    (b : B ⟶ SheafOfModules.unit W.ringCatSheaf) (μ : A.restrict i ⟶ B) (d : K.restrict i ⟶ L)
    (hb : μ ≫ b = (Scheme.Modules.restrictFunctor i).map a ≫ (restrictUnitIso i).hom) :
    (tensorRestrictionIso i K A).inv ≫ (moduleTensorLeftFunctor W (K.restrict i)).map μ ≫
        (moduleTensorCoefficientMap W d).app B ≫ (moduleTensorLeftFunctor W L).map b ≫
        (SheafOfModulesOfCommRing.tensorRightUnitIso W.sheaf).hom.app L =
      (Scheme.Modules.restrictFunctor i).map
        ((moduleTensorLeftFunctor X K).map a ≫
          (SheafOfModulesOfCommRing.tensorRightUnitIso X.sheaf).hom.app K) ≫ d := by
  rw [coefficientRightUnit]
  simpa only [Category.assoc] using congrArg (fun z => z ≫ d)
    (tensorRestriction_unit_map (K := K) i a b μ hb)

/-- The original differential coefficient restriction preserves the native
structure-coefficient unit. -/
theorem relativeTopDifferentialCoefficientsRestrictionIso_unit
    {W X Z Y : Scheme.{u}} (p : X ⟶ Y) (i : W ⟶ X) (q : W ⟶ Z) (j : Z ⟶ Y)
    [IsOpenImmersion i] [IsOpenImmersion j] (h : i ≫ p = q ≫ j) (n : ℕ) :
    (relativeTopDifferentialCoefficientsRestrictionIso p i q j h n).hom.app
        (SheafOfModules.unit Y.ringCatSheaf) ≫
      (relativeTopDifferentialCoefficientsFunctor q n).map (restrictUnitIso j).hom ≫
        (relativeTopDifferentialCoefficientsUnitIso q n).hom =
      (Scheme.Modules.restrictFunctor i).map (relativeTopDifferentialCoefficientsUnitIso p n).hom ≫
        (relativeTopDifferentialRestrictionIso p i q j h n).hom := by
  let K := moduleExteriorPower X (relativeDifferentialSheaf p) n
  let L := moduleExteriorPower W (relativeDifferentialSheaf q) n
  let μ := (pullbackOpenSquare i q p j h).hom.app (SheafOfModules.unit Y.ringCatSheaf)
  let b := (Scheme.Modules.pullback q).map (restrictUnitIso j).hom ≫ (pullbackUnitIso q).hom
  let d := (relativeTopDifferentialRestrictionIso p i q j h n).hom
  have hb : μ ≫ b = (Scheme.Modules.restrictFunctor i).map (pullbackUnitIso p).hom ≫
      (restrictUnitIso i).hom := pullbackOpenSquare_unit p i q j h
  have H := tensorRestriction_unit_compare i (pullbackUnitIso p).hom b μ d hb
  dsimp only [b] at H
  rw [Functor.map_comp] at H
  simpa only [relativeTopDifferentialCoefficientsRestrictionIso,
    relativeTopDifferentialCoefficientsUnitIso,
    relativeTopDifferentialCoefficientsFunctor, Iso.trans_hom, Iso.symm_hom, Functor.mapIso_hom,
    NatTrans.comp_app, Functor.isoWhiskerLeft_hom, Functor.isoWhiskerRight_hom,
    Functor.whiskerLeft_app, Functor.whiskerRight_app, Functor.comp_map, Functor.comp_obj,
    Functor.id_obj, Iso.app_hom, NatIso.ofComponents,
    moduleTensorCoefficientMap, tensorRestrictionNatIso, μ, d, K, L,
    Category.assoc] using H

end AlgebraicGeometry.Scheme.Cohomology

namespace AlgebraicGeometry.Scheme.Cohomology
open AlgebraicGeometry.Scheme.Modules.Differentials
variable {R A : Type u} [CommRing R] [CommRing A] (σ : R →+* A) (ι : Type u)
  [IsOpenImmersion (Spec.map (CommRingCat.ofHom σ))]

private theorem adjointNat_naturality
    {C D E : Type*} [Category* C] [Category* D] [Category* E]
    {L : D ⥤ E} {T : E ⥤ D} (adj : L ⊣ T)
    {F : C ⥤ D} {G : C ⥤ E} (η : F ⋙ L ⟶ G) {x y : C} (s : x ⟶ y) :
    F.map s ≫ adj.homEquiv (F.obj y) (G.obj y) (η.app y) =
      adj.homEquiv (F.obj x) (G.obj x) (η.app x) ≫ T.map (G.map s) := by
  rw [← Adjunction.homEquiv_naturality_left, ← Functor.comp_map,
    η.naturality, Adjunction.homEquiv_naturality_right]

private def typedAdjointComponent
    {C D E : Type*} [Category* C] [Category* D] [Category* E]
    {L : D ⥤ E} {T : E ⥤ D} (adj : L ⊣ T)
    {F : C ⥤ D} {G : C ⥤ E} (η : F ⋙ L ⟶ G) (x : C) :
    F.obj x ⟶ T.obj (G.obj x) :=
  adj.homEquiv (F.obj x) (G.obj x) (η.app x)

private theorem typedAdjointComponent_eq
    {C D E : Type*} [Category* C] [Category* D] [Category* E]
    {L : D ⥤ E} {T : E ⥤ D} (adj : L ⊣ T)
    {F : C ⥤ D} {G : C ⥤ E} (η : F ⋙ L ⟶ G) (x : C) :
    typedAdjointComponent adj η x = adj.homEquiv (F.obj x) (G.obj x) (η.app x) := rfl

private theorem typedAdjointComponent_naturality
    {C D E : Type*} [Category* C] [Category* D] [Category* E]
    {L : D ⥤ E} {T : E ⥤ D} (adj : L ⊣ T)
    {F : C ⥤ D} {G : C ⥤ E} (η : F ⋙ L ⟶ G) {x y : C} (s : x ⟶ y) :
    F.map s ≫ typedAdjointComponent adj η y =
      typedAdjointComponent adj η x ≫ T.map (G.map s) :=
  adjointNat_naturality adj η s

private def typedAdjointNat
    {C D E : Type*} [Category* C] [Category* D] [Category* E]
    {L : D ⥤ E} {T : E ⥤ D} (adj : L ⊣ T)
    {F : C ⥤ D} {G : C ⥤ E} (η : F ⋙ L ⟶ G) : F ⟶ G ⋙ T where
  app x := typedAdjointComponent adj η x
  naturality {_x _y} s := typedAdjointComponent_naturality adj η s

private def affineDifferentialCoefficientOpenNat (n : ℕ) :
    relativeTopDifferentialCoefficientsFunctor (toSpec R ι) n ⟶
      (Scheme.Modules.restrictFunctor (Spec.map (CommRingCat.ofHom σ)) ⋙
        relativeTopDifferentialCoefficientsFunctor (toSpec A ι) n) ⋙
          Scheme.Modules.pushforward (ProjectiveSpace.map σ ι) := by
  let : IsOpenImmersion (ProjectiveSpace.map σ ι) :=
    MorphismProperty.of_isPullback (ProjectiveSpace.isPullback_map σ ι).flip inferInstance
  exact typedAdjointNat
    (F := relativeTopDifferentialCoefficientsFunctor (toSpec R ι) n)
    (G := Scheme.Modules.restrictFunctor (Spec.map (CommRingCat.ofHom σ)) ⋙
      relativeTopDifferentialCoefficientsFunctor (toSpec A ι) n)
    (L := Scheme.Modules.restrictFunctor (ProjectiveSpace.map σ ι))
    (T := Scheme.Modules.pushforward (ProjectiveSpace.map σ ι))
    (Scheme.Modules.restrictAdjunction (ProjectiveSpace.map σ ι))
    (relativeTopDifferentialCoefficientsRestrictionIso (toSpec R ι) (ProjectiveSpace.map σ ι)
      (toSpec A ι) (Spec.map (CommRingCat.ofHom σ)) (ProjectiveSpace.map_toSpec σ ι) n).hom

/-- The original open coefficient adjunct for the actual differential coefficient. -/
@[no_expose] def projectiveAffineDifferentialCoefficientsOpenMap
    (n : ℕ) (N : (Spec (.of R)).Modules) :
    (relativeTopDifferentialCoefficientsFunctor (toSpec R ι) n).obj N ⟶
      (Scheme.Modules.pushforward (ProjectiveSpace.map σ ι)).obj
        ((Scheme.Modules.restrictFunctor (Spec.map (CommRingCat.ofHom σ)) ⋙
          relativeTopDifferentialCoefficientsFunctor (toSpec A ι) n).obj N) := by
  let : IsOpenImmersion (ProjectiveSpace.map σ ι) :=
    MorphismProperty.of_isPullback (ProjectiveSpace.isPullback_map σ ι).flip inferInstance
  exact typedAdjointComponent
    (F := relativeTopDifferentialCoefficientsFunctor (toSpec R ι) n)
    (G := Scheme.Modules.restrictFunctor (Spec.map (CommRingCat.ofHom σ)) ⋙
      relativeTopDifferentialCoefficientsFunctor (toSpec A ι) n)
    (L := Scheme.Modules.restrictFunctor (ProjectiveSpace.map σ ι))
    (T := Scheme.Modules.pushforward (ProjectiveSpace.map σ ι))
    (Scheme.Modules.restrictAdjunction (ProjectiveSpace.map σ ι))
    (relativeTopDifferentialCoefficientsRestrictionIso (toSpec R ι) (ProjectiveSpace.map σ ι)
      (toSpec A ι) (Spec.map (CommRingCat.ofHom σ)) (ProjectiveSpace.map_toSpec σ ι) n).hom N

/-- The canonical coefficient map is the native restriction adjunct on the same objects. -/
theorem projectiveAffineDifferentialCoefficientsOpenMap_eq_homEquiv
    (n : ℕ) (N : (Spec (.of R)).Modules) :
    letI : IsOpenImmersion (ProjectiveSpace.map σ ι) :=
      MorphismProperty.of_isPullback (ProjectiveSpace.isPullback_map σ ι).flip inferInstance
    projectiveAffineDifferentialCoefficientsOpenMap σ ι n N =
      (Scheme.Modules.restrictAdjunction (ProjectiveSpace.map σ ι)).homEquiv
        ((relativeTopDifferentialCoefficientsFunctor (toSpec R ι) n).obj N)
        ((Scheme.Modules.restrictFunctor (Spec.map (CommRingCat.ofHom σ)) ⋙
          relativeTopDifferentialCoefficientsFunctor (toSpec A ι) n).obj N)
        ((relativeTopDifferentialCoefficientsRestrictionIso (toSpec R ι) (ProjectiveSpace.map σ ι)
          (toSpec A ι) (Spec.map (CommRingCat.ofHom σ))
          (ProjectiveSpace.map_toSpec σ ι) n).hom.app N) := by
  let : IsOpenImmersion (ProjectiveSpace.map σ ι) :=
    MorphismProperty.of_isPullback (ProjectiveSpace.isPullback_map σ ι).flip inferInstance
  exact typedAdjointComponent_eq
    (F := relativeTopDifferentialCoefficientsFunctor (toSpec R ι) n)
    (G := Scheme.Modules.restrictFunctor (Spec.map (CommRingCat.ofHom σ)) ⋙
      relativeTopDifferentialCoefficientsFunctor (toSpec A ι) n)
    (L := Scheme.Modules.restrictFunctor (ProjectiveSpace.map σ ι))
    (T := Scheme.Modules.pushforward (ProjectiveSpace.map σ ι))
    (Scheme.Modules.restrictAdjunction (ProjectiveSpace.map σ ι))
    (relativeTopDifferentialCoefficientsRestrictionIso (toSpec R ι) (ProjectiveSpace.map σ ι)
      (toSpec A ι) (Spec.map (CommRingCat.ofHom σ)) (ProjectiveSpace.map_toSpec σ ι) n).hom N

private theorem affineDifferentialCoefficientOpen_naturality (n : ℕ)
    {N N' : (Spec (.of R)).Modules} (s : N ⟶ N') :
    (relativeTopDifferentialCoefficientsFunctor (toSpec R ι) n).map s ≫
        projectiveAffineDifferentialCoefficientsOpenMap σ ι n N' =
      projectiveAffineDifferentialCoefficientsOpenMap σ ι n N ≫
        (Scheme.Modules.pushforward (ProjectiveSpace.map σ ι)).map
          ((Scheme.Modules.restrictFunctor (Spec.map (CommRingCat.ofHom σ)) ⋙
            relativeTopDifferentialCoefficientsFunctor (toSpec A ι) n).map s) :=
  (affineDifferentialCoefficientOpenNat σ ι n).naturality s


private theorem affineDifferentialCoefficientOpen_unit (n : ℕ) :
    projectiveAffineDifferentialCoefficientsOpenMap σ ι n
      (SheafOfModules.unit (Spec (.of R)).ringCatSheaf) ≫
      (Scheme.Modules.pushforward (ProjectiveSpace.map σ ι)).map
        ((relativeTopDifferentialCoefficientsFunctor (toSpec A ι) n).map
          (restrictUnitIso (Spec.map (CommRingCat.ofHom σ))).hom ≫
            (relativeTopDifferentialCoefficientsUnitIso (toSpec A ι) n).hom) =
    (relativeTopDifferentialCoefficientsUnitIso (toSpec R ι) n).hom ≫
      differentialTopBaseOpenCoefficient σ ι n := by
  let : IsOpenImmersion (ProjectiveSpace.map σ ι) :=
    MorphismProperty.of_isPullback (ProjectiveSpace.isPullback_map σ ι).flip inferInstance
  change (Scheme.Modules.restrictAdjunction (ProjectiveSpace.map σ ι)).homEquiv _ _ _ ≫ _ = _
  rw [← Adjunction.homEquiv_naturality_right,
    relativeTopDifferentialCoefficientsRestrictionIso_unit,
    Adjunction.homEquiv_naturality_left, relativeTopDifferentialRestrictionIso_original]

private theorem affineDifferentialCoefficientOpen_unit_cohomology (n : ℕ)
    (x : Sheaf.H.{u + 1} (moduleAddSheaf (ProjectiveSpace R ι)
      ((relativeTopDifferentialCoefficientsFunctor (toSpec R ι) n).obj
        (SheafOfModules.unit (Spec (.of R)).ringCatSheaf))) n) :
    Sheaf.H.map ((SheafOfModules.toSheaf (ProjectiveSpace A ι).ringCatSheaf).map
      (relativeTopDifferentialCoefficientsUnitIso (toSpec A ι) n).hom) n
        (Sheaf.H.map ((SheafOfModules.toSheaf (ProjectiveSpace A ι).ringCatSheaf).map
          ((relativeTopDifferentialCoefficientsFunctor (toSpec A ι) n).map
            (restrictUnitIso (Spec.map (CommRingCat.ofHom σ))).hom)) n
          (moduleCohomologyMapAlong (ProjectiveSpace.map σ ι)
            (projectiveAffineDifferentialCoefficientsOpenMap σ ι n
              (SheafOfModules.unit (Spec (.of R)).ringCatSheaf)) n x)) =
    moduleCohomologyMapAlong (ProjectiveSpace.map σ ι) (differentialTopBaseOpenCoefficient σ ι n) n
      (Sheaf.H.map ((SheafOfModules.toSheaf (ProjectiveSpace R ι).ringCatSheaf).map
        (relativeTopDifferentialCoefficientsUnitIso (toSpec R ι) n).hom) n x) := by
  rw [← Sheaf.H.map_comp_apply, ← Functor.map_comp]
  let g := ProjectiveSpace.map σ ι
  let φ := projectiveAffineDifferentialCoefficientsOpenMap σ ι n
    (SheafOfModules.unit (Spec (.of R)).ringCatSheaf)
  let β := (relativeTopDifferentialCoefficientsFunctor (toSpec A ι) n).map
    (restrictUnitIso (Spec.map (CommRingCat.ofHom σ))).hom ≫
      (relativeTopDifferentialCoefficientsUnitIso (toSpec A ι) n).hom
  exact (moduleCohomologyMapAlong_postcomp g φ β n x).symm.trans
    ((congrArg (fun c => moduleCohomologyMapAlong g c n x)
      (affineDifferentialCoefficientOpen_unit σ ι n)).trans
        (moduleCohomologyMapAlong_precomp g
          (relativeTopDifferentialCoefficientsUnitIso (toSpec R ι) n).hom
          (differentialTopBaseOpenCoefficient σ ι n) n x))

private theorem affineDifferentialUnitClass_open (n : ℕ) (e : ι ≃ Fin (n + 1)) :
    Sheaf.H.map ((SheafOfModules.toSheaf (ProjectiveSpace A ι).ringCatSheaf).map
      ((relativeTopDifferentialCoefficientsFunctor (toSpec A ι) n).map
        (restrictUnitIso (Spec.map (CommRingCat.ofHom σ))).hom)) n
      (moduleCohomologyMapAlong (ProjectiveSpace.map σ ι)
        (projectiveAffineDifferentialCoefficientsOpenMap σ ι n
          (SheafOfModules.unit (Spec (.of R)).ringCatSheaf)) n
          (affineDifferentialUnitClass R ι n e)) =
      affineDifferentialUnitClass A ι n e := by
  let : IsOpenImmersion (ProjectiveSpace.map σ ι) :=
    MorphismProperty.of_isPullback (ProjectiveSpace.isPullback_map σ ι).flip inferInstance
  let : Fintype ι := Fintype.ofEquiv (Fin (n + 1)) e.symm
  let y := Sheaf.H.map ((SheafOfModules.toSheaf (ProjectiveSpace A ι).ringCatSheaf).map
    ((relativeTopDifferentialCoefficientsFunctor (toSpec A ι) n).map
      (restrictUnitIso (Spec.map (CommRingCat.ofHom σ))).hom)) n
        (moduleCohomologyMapAlong (ProjectiveSpace.map σ ι)
          (projectiveAffineDifferentialCoefficientsOpenMap σ ι n
          (SheafOfModules.unit (Spec (.of R)).ringCatSheaf)) n
            (affineDifferentialUnitClass R ι n e))
  let x := Sheaf.H.map ((SheafOfModules.toSheaf (ProjectiveSpace R ι).ringCatSheaf).map
    (relativeTopDifferentialCoefficientsUnitIso (toSpec R ι) n).hom) n
      (affineDifferentialUnitClass R ι n e)
  have ha := affineDifferentialUnitTrace_apply A ι n e y
  have hc := affineDifferentialCoefficientOpen_unit_cohomology σ ι n
    (affineDifferentialUnitClass R ι n e)
  have ht := congrArg (fun z => projectiveTrace A ι n e
    (Sheaf.H.map ((SheafOfModules.toSheaf (ProjectiveSpace A ι).ringCatSheaf).map
      (differentialResidueTwistingIso A ι n e).hom) n z)) hc
  have ho := projectiveTrace_differential_baseOpen σ ι n e x
  have hu := affineDifferentialUnitTrace_apply R ι n e (affineDifferentialUnitClass R ι n e)
  have h1 := affineDifferentialUnitTrace_class R ι n e
  have hs := (congrArg σ (hu.symm.trans h1)).trans (map_one σ)
  apply affineDifferentialUnitTrace_injective A ι n e
  exact (ha.trans (ht.trans (ho.trans hs))).trans
    (affineDifferentialUnitTrace_class A ι n e).symm

private theorem unitHom_restrict {X Y : Scheme.{u}} (p : X ⟶ Y) [IsOpenImmersion p]
    {N : Y.Modules} (s : SheafOfModules.unit Y.ringCatSheaf ⟶ N) :
    unitHomGlobalSectionsEquiv X (N.restrict p)
      ((restrictUnitIso p).inv ≫ (Scheme.Modules.restrictFunctor p).map s) =
    (((Scheme.Modules.restrictAdjunction p).unit.app N).app ⊤)
      (unitHomGlobalSectionsEquiv Y N s) := by
  have hu := restrictUnitIso_hom_adjoint p
  rw [Adjunction.homEquiv_apply] at hu
  have ht : SheafOfModules.unitToPushforwardObjUnit p.toRingCatSheafHom ≫
      (Scheme.Modules.pushforward p).map
        ((restrictUnitIso p).inv ≫ (Scheme.Modules.restrictFunctor p).map s) =
      s ≫ (Scheme.Modules.restrictAdjunction p).unit.app N := by
    rw [← hu]
    simp only [Functor.map_comp, Category.assoc]
    rw [← Functor.map_comp_assoc, Iso.hom_inv_id, CategoryTheory.Functor.map_id, Category.id_comp]
    exact ((Scheme.Modules.restrictAdjunction p).unit.naturality s).symm
  have hv := congrArg (fun z : SheafOfModules.unit Y.ringCatSheaf ⟶
    (Scheme.Modules.pushforward p).obj (N.restrict p) =>
      Scheme.Modules.Hom.app z ⊤ (1 : Γ(Y, ⊤))) ht
  change (((restrictUnitIso p).inv ≫ (Scheme.Modules.restrictFunctor p).map s).app ⊤)
    (p.appTop (1 : Γ(Y, ⊤))) =
      (((Scheme.Modules.restrictAdjunction p).unit.app N).app ⊤)
        (unitHomGlobalSectionsEquiv Y N s) at hv
  simpa only [map_one, unitHomGlobalSectionsEquiv_apply] using hv

private theorem coefficientCohomology_map_comp
    {C : Type*} [Category* C] (X : Scheme.{u}) (F : C ⥤ X.Modules)
    {A B D : C} (f : A ⟶ B) (g : B ⟶ D) (q : ℕ)
    (x : Sheaf.H.{u + 1} (moduleAddSheaf X (F.obj A)) q) :
    Sheaf.H.map ((SheafOfModules.toSheaf X.ringCatSheaf).map (F.map (f ≫ g))) q x =
      Sheaf.H.map ((SheafOfModules.toSheaf X.ringCatSheaf).map (F.map g)) q
        (Sheaf.H.map ((SheafOfModules.toSheaf X.ringCatSheaf).map (F.map f)) q x) := by
  rw [F.map_comp, Functor.map_comp, Sheaf.H.map_comp_apply]

private theorem affineDifferentialGenerator_open (n : ℕ) (e : ι ≃ Fin (n + 1))
    {N : (Spec (.of R)).Modules}
    (s : (SheafOfModules.unit (Spec (.of R)).ringCatSheaf : (Spec (.of R)).Modules) ⟶ N) :
    moduleCohomologyMapAlong (ProjectiveSpace.map σ ι)
      (projectiveAffineDifferentialCoefficientsOpenMap σ ι n N) n
      (Sheaf.H.map ((SheafOfModules.toSheaf (ProjectiveSpace R ι).ringCatSheaf).map
        ((relativeTopDifferentialCoefficientsFunctor (toSpec R ι) n).map s)) n
          (affineDifferentialUnitClass R ι n e)) =
    Sheaf.H.map ((SheafOfModules.toSheaf (ProjectiveSpace A ι).ringCatSheaf).map
      ((relativeTopDifferentialCoefficientsFunctor (toSpec A ι) n).map
        ((restrictUnitIso (Spec.map (CommRingCat.ofHom σ))).inv ≫
          (Scheme.Modules.restrictFunctor (Spec.map (CommRingCat.ofHom σ))).map s))) n
            (affineDifferentialUnitClass A ι n e) := by
  let j := Spec.map (CommRingCat.ofHom σ)
  let s' := (restrictUnitIso j).inv ≫ (Scheme.Modules.restrictFunctor j).map s
  let c := affineDifferentialUnitClass R ι n e
  let φ := projectiveAffineDifferentialCoefficientsOpenMap σ ι n
    (SheafOfModules.unit (Spec (.of R)).ringCatSheaf)
  let ψ := projectiveAffineDifferentialCoefficientsOpenMap σ ι n N
  let μ := (relativeTopDifferentialCoefficientsFunctor (toSpec R ι) n).map s
  let ν := (relativeTopDifferentialCoefficientsFunctor (toSpec A ι) n).map
    ((Scheme.Modules.restrictFunctor j).map s)
  have hn := moduleCohomologyMapAlong_naturality (ProjectiveSpace.map σ ι) φ ψ μ ν
    (affineDifferentialCoefficientOpen_naturality σ ι n s) n c
  change _ = _ at hn
  have hs : (Scheme.Modules.restrictFunctor j).map s = (restrictUnitIso j).hom ≫ s' := by
    simp only [s', Iso.hom_inv_id_assoc]
  have hc := affineDifferentialUnitClass_open σ ι n e
  change Sheaf.H.map ((SheafOfModules.toSheaf (ProjectiveSpace A ι).ringCatSheaf).map
    ((relativeTopDifferentialCoefficientsFunctor (toSpec A ι) n).map (restrictUnitIso j).hom)) n
      (moduleCohomologyMapAlong (ProjectiveSpace.map σ ι)
        (projectiveAffineDifferentialCoefficientsOpenMap σ ι n
          (SheafOfModules.unit (Spec (.of R)).ringCatSheaf)) n c) =
          affineDifferentialUnitClass A ι n e at hc
  have ht := congrArg (fun z => Sheaf.H.map
    ((SheafOfModules.toSheaf (ProjectiveSpace A ι).ringCatSheaf).map
      ((relativeTopDifferentialCoefficientsFunctor (toSpec A ι) n).map s')) n z) hc
  let z := moduleCohomologyMapAlong (ProjectiveSpace.map σ ι) φ n c
  have hm := congrArg (fun t : (Scheme.Modules.restrict
      (SheafOfModules.unit (Spec (.of R)).ringCatSheaf) j ⟶ N.restrict j) => Sheaf.H.map
        ((SheafOfModules.toSheaf (ProjectiveSpace A ι).ringCatSheaf).map
          ((relativeTopDifferentialCoefficientsFunctor (toSpec A ι) n).map t)) n z) hs
  have hcomp := coefficientCohomology_map_comp (ProjectiveSpace A ι)
    (relativeTopDifferentialCoefficientsFunctor (toSpec A ι) n) (restrictUnitIso j).hom s' n z
  exact hn.trans (hm.trans (hcomp.trans ht))

private theorem affineTrace_open_impl (n : ℕ) (e : ι ≃ Fin (n + 1))
    (N : (Spec (.of R)).Modules) [N.IsQuasicoherent]
    (x : Sheaf.H.{u + 1} (moduleAddSheaf (ProjectiveSpace R ι)
      ((relativeTopDifferentialCoefficientsFunctor (toSpec R ι) n).obj N)) n) :
    projectiveAffineDifferentialTraceLinearEquiv A ι n e
      (N.restrict (Spec.map (CommRingCat.ofHom σ)))
      (moduleCohomologyMapAlong (ProjectiveSpace.map σ ι)
        (projectiveAffineDifferentialCoefficientsOpenMap σ ι n N) n x) =
      (((Scheme.Modules.restrictAdjunction (Spec.map (CommRingCat.ofHom σ))).unit.app N).app ⊤)
        (projectiveAffineDifferentialTraceLinearEquiv R ι n e N x) := by
  let j := Spec.map (CommRingCat.ofHom σ)
  let s := (unitHomGlobalSectionsEquiv (Spec (.of R)) N).symm
    (projectiveAffineDifferentialTraceLinearEquiv R ι n e N x)
  let s' := (restrictUnitIso j).inv ≫ (Scheme.Modules.restrictFunctor j).map s
  have hx := projectiveAffineDifferentialTraceLinearEquiv_generator R ι n e N x
  have hm := (congrArg (moduleCohomologyMapAlong (ProjectiveSpace.map σ ι)
    (projectiveAffineDifferentialCoefficientsOpenMap σ ι n N) n) hx).trans
      (affineDifferentialGenerator_open σ ι n e s)
  have ht := congrArg (projectiveAffineDifferentialTraceLinearEquiv A ι n e (N.restrict j)) hm
  exact ht.trans ((projectiveAffineDifferentialTraceLinearEquiv_unitMap A ι n e s').trans
    ((unitHom_restrict j s).trans (congrArg
      (fun z => (((Scheme.Modules.restrictAdjunction j).unit.app N).app ⊤) z)
        ((unitHomGlobalSectionsEquiv (Spec (.of R)) N).apply_symm_apply _))))

end AlgebraicGeometry.Scheme.Cohomology

namespace AlgebraicGeometry.Scheme.Cohomology
variable (R : Type u) [CommRing R] (ι : Type u) (n : ℕ) (e : ι ≃ Fin (n + 1))

/-- On an actual tilde coefficient, the affine trace is the unchanged coefficient residue trace
through the original ordered differential/twist comparison and the original tilde unit. -/
theorem projectiveAffineDifferentialTraceLinearEquiv_tilde_residue
    (J : ModuleCat.{u} R)
    (x : Sheaf.H.{u + 1} (moduleAddSheaf (ProjectiveSpace R ι)
      ((relativeTopDifferentialCoefficientsFunctor (toSpec R ι) n).obj (tilde J))) n) :
    letI : Fintype ι := Fintype.ofEquiv (Fin (n + 1)) e.symm
    projectiveAffineDifferentialTraceLinearEquiv R ι n e (tilde J) x =
      (tilde.toTildeΓNatIso (R := .of R)).hom.app J
        (projectiveTraceCoefficientsLinearEquiv R ι n e J
          (Sheaf.H.map ((SheafOfModules.toSheaf (ProjectiveSpace R ι).ringCatSheaf).map
            (projectiveDifferentialCoefficientsTwistingIso R ι n e J).hom) n x)) := by
  let : Fintype ι := Fintype.ofEquiv (Fin (n + 1)) e.symm
  exact projectiveAffineDifferentialTraceLinearEquiv_tilde R ι n e J x

/-- The ring coefficient recovers the original differential residue trace using exactly the
native pullback-unit comparison and tensor right unitor. -/
theorem projectiveAffineDifferentialTraceLinearEquiv_unit
    (x : Sheaf.H.{u + 1} (moduleAddSheaf (ProjectiveSpace R ι)
      ((relativeTopDifferentialCoefficientsFunctor (toSpec R ι) n).obj
        (tilde (ModuleCat.of R R)))) n) :
    letI : Fintype ι := Fintype.ofEquiv (Fin (n + 1)) e.symm
    projectiveAffineDifferentialTraceLinearEquiv R ι n e (tilde (ModuleCat.of R R)) x =
      (tilde.toTildeΓNatIso (R := .of R)).hom.app (ModuleCat.of R R)
        (projectiveTrace R ι n e
          (Sheaf.H.map ((SheafOfModules.toSheaf (ProjectiveSpace R ι).ringCatSheaf).map
            (differentialResidueTwistingIso R ι n e).hom) n
              (Sheaf.H.map ((SheafOfModules.toSheaf (ProjectiveSpace R ι).ringCatSheaf).map
                (relativeTopDifferentialCoefficientsUnitIso (toSpec R ι) n).hom) n x))) := by
  let : Fintype ι := Fintype.ofEquiv (Fin (n + 1)) e.symm
  have h₀ := projectiveAffineDifferentialTraceLinearEquiv_tilde R ι n e (ModuleCat.of R R) x
  have h₁ := affineDifferentialTraceCoefficients_self R ι n e x
  exact h₀.trans (congrArg
    (fun z => (tilde.toTildeΓNatIso (R := .of R)).hom.app (ModuleCat.of R R) z) h₁)

/-- The actual original differential Cech residue class has its original scalar value. -/
theorem projectiveAffineDifferentialTraceLinearEquiv_residue (r : R) :
    projectiveAffineDifferentialTraceLinearEquiv R ι n e (tilde (ModuleCat.of R R))
      (Sheaf.H.map ((SheafOfModules.toSheaf (ProjectiveSpace R ι).ringCatSheaf).map
        (relativeTopDifferentialCoefficientsUnitIso (toSpec R ι) n).inv) n
          (differentialResidueCohomologyClass R ι n e r)) =
      (tilde.toTildeΓNatIso (R := .of R)).hom.app (ModuleCat.of R R) r := by
  let : Fintype ι := Fintype.ofEquiv (Fin (n + 1)) e.symm
  let P := ProjectiveSpace R ι
  let α := (toSpec R ι).appTop.hom.comp (Scheme.ΓSpecIso (.of R)).inv.hom
  let E := relativeTopDifferentialCoefficientsUnitIso (toSpec R ι) n
  let c := differentialResidueCohomologyClass R ι n e r
  have hu := projectiveAffineDifferentialTraceLinearEquiv_unit R ι n e
    (Sheaf.H.map ((SheafOfModules.toSheaf P.ringCatSheaf).map E.inv) n c)
  have hc := Iso.inv_hom_id_apply (moduleCohomologyIsoOfHom P α E n) c
  have ht := congrArg (fun z => (tilde.toTildeΓNatIso (R := .of R)).hom.app (ModuleCat.of R R)
    (projectiveTrace R ι n e
      (Sheaf.H.map ((SheafOfModules.toSheaf P.ringCatSheaf).map
        (differentialResidueTwistingIso R ι n e).hom) n z))) hc
  have hr := congrArg
    (fun z => (tilde.toTildeΓNatIso (R := .of R)).hom.app (ModuleCat.of R R) z)
    (differentialResidueCohomologyClass_trace R ι n e r)
  exact hu.trans (ht.trans hr)

end AlgebraicGeometry.Scheme.Cohomology

namespace AlgebraicGeometry.Scheme.Cohomology
variable {R A : Type u} [CommRing R] [CommRing A] (σ : R →+* A) (ι : Type u)
  [IsOpenImmersion (Spec.map (CommRingCat.ofHom σ))]

/-- The original open coefficient map carries the affine trace through native coefficient
restriction. The exact original adjunct is retained by
`projectiveAffineDifferentialCoefficientsOpenMap_eq_homEquiv`. -/
theorem projectiveAffineDifferentialTraceLinearEquiv_open (n : ℕ) (e : ι ≃ Fin (n + 1))
    (N : (Spec (.of R)).Modules) [N.IsQuasicoherent]
    (x : Sheaf.H.{u + 1} (moduleAddSheaf (ProjectiveSpace R ι)
      ((relativeTopDifferentialCoefficientsFunctor (toSpec R ι) n).obj N)) n) :
    projectiveAffineDifferentialTraceLinearEquiv A ι n e
      (N.restrict (Spec.map (CommRingCat.ofHom σ)))
      (moduleCohomologyMapAlong (ProjectiveSpace.map σ ι)
        (projectiveAffineDifferentialCoefficientsOpenMap σ ι n N) n x) =
      (((Scheme.Modules.restrictAdjunction (Spec.map (CommRingCat.ofHom σ))).unit.app N).app ⊤)
        (projectiveAffineDifferentialTraceLinearEquiv R ι n e N x) :=
  affineTrace_open_impl σ ι n e N x

end AlgebraicGeometry.Scheme.Cohomology
