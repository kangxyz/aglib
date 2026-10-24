/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import
  Aglib.AlgebraicGeometry.Cohomology.Duality.Projective.Relative.NormalSurface.Cohomology
public import Aglib.AlgebraicGeometry.Cohomology.Proper.DerivedStructure
public import Aglib.AlgebraicGeometry.Cohomology.Proper.FiniteLength
public import Aglib.AlgebraicGeometry.Cohomology.Proper.ResidueVanishing
public import Aglib.AlgebraicGeometry.Morphisms.Proper.BirationalSurface
public import Aglib.AlgebraicGeometry.Properties.Normal.Affine
public import Aglib.AlgebraicGeometry.FunctionField.GenericFiber
public import Aglib.AlgebraicGeometry.FunctionField.AffineCharts
public import Aglib.Algebra.Homology.ModuleCat.HomComplex.TwoLayer
public import Aglib.Algebra.Homology.ModuleCat.HomComplex.TwoLayer.Cohomology
public import Aglib.Algebra.Homology.ModuleCat.HomComplex.Residue
public import Aglib.Algebra.Homology.ModuleCat.HomComplex.Postnikov
public import Aglib.RingTheory.Nagata.CompleteLocalSurface
public import Mathlib.RingTheory.LocalRing.Length

/-!
# Chosen-embedding Grauert--Riemenschneider vanishing for complete local surfaces

The original structural derived unit and original H1 give an actual
Postnikov triangle. Proper birational geometry supplies finite-length H1,
and finite local scalar restriction supplies its genuine finite-projective
model. The original evaluation and residue-dual maps turn a hypothetical
top dual class into a residue morphism excluded by actual residue vanishing.
The actual chosen-embedding Serre comparison then kills H1 of the literal
normalSurfaceCanonicalModule. No regularity of X, flatness of f, splitting,
perfect-model, trace-compatibility or duality-data premise is introduced.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian
open AlgebraicGeometry TopologicalSpace Opposite
open AlgebraicGeometry.Scheme.Modules AlgebraicGeometry.Scheme.Modules.QuasiCoherent
open CochainComplex.HomComplex

universe u v w

namespace AlgebraicGeometry.Scheme.Cohomology

/-- The literal restricted module, with the original action through sigma. -/
private theorem grFiniteLength_restrictScalars
    {R : Type u} {A : Type v} [CommRing R] [CommRing A]
    [IsLocalRing R] [IsLocalRing A]
    (sigma : R →+* A) [IsLocalHom sigma] (hfinite : sigma.Finite)
    (M : ModuleCat.{w} A) (hM : IsFiniteLength A M) :
    IsFiniteLength R ((ModuleCat.restrictScalars sigma).obj M) := by
  let : Algebra R A := sigma.toAlgebra
  let : Module.Finite R A := hfinite
  let : IsLocalHom (algebraMap R A) := inferInstanceAs (IsLocalHom sigma)
  let : Module R M := Module.compHom M sigma
  let : IsScalarTower R A M :=
    ⟨fun r a x => by
      change (r • a) • x = sigma r • (a • x)
      rw [Algebra.smul_def]
      exact mul_smul _ _ _⟩
  change IsFiniteLength R M
  apply Module.length_ne_top_iff.mp
  rw [IsLocalRing.length_restrictScalars R A M]
  obtain ⟨l, hl⟩ := ENat.ne_top_iff_exists.mp (Module.length_ne_top_iff.mpr hM)
  rw [← hl, Module.length_eq_finrank, ← ENat.natCast_mul]
  exact ENat.natCast_ne_top _

/-- The actual generic-fibre isomorphism proves finiteness of the actual field map. -/
private theorem grFunctionFieldMap_finite
    {X Y : Scheme.{u}} [IsIntegral X] [IsIntegral Y]
    (f : X ⟶ Y) [IsFinite f] [IsDominant f] :
    (Scheme.functionFieldMap f).Finite := by
  let q := pullback.snd f (Y.fromSpecStalk (genericPoint Y))
  let : IsIso (Scheme.genericFibreMap f) := Scheme.genericFibreMap_isIso f
  have hfinite : IsFinite (Scheme.genericFibreMap f ≫ q) := inferInstance
  have hcomp : Scheme.genericFibreMap f ≫ q =
      Spec.map (CommRingCat.ofHom (Scheme.functionFieldMap f)) := by
    dsimp only [q, Scheme.genericFibreMap]
    exact pullback.lift_snd _ _ _
  rw [hcomp] at hfinite
  exact (IsFinite.SpecMap_iff _).mp hfinite

/-- Injectivity is sufficient for the actual affine map to be dominant. -/
private theorem grSpecMap_dominant
    {R A : Type u} [CommRing R] [CommRing A]
    (sigma : R →+* A) (hinj : Function.Injective sigma) :
    IsDominant (Spec.map (CommRingCat.ofHom sigma)) := by
  constructor
  change DenseRange (PrimeSpectrum.comap sigma)
  rw [PrimeSpectrum.denseRange_comap_iff_ker_le_nilRadical,
    (RingHom.injective_iff_ker_eq_bot sigma).mp hinj]
  exact bot_le

/-- The actual structural factorization supplies the required dominance instance. -/
private theorem grEmbeddingMap_dominant
    {R A : Type u} [CommRing R] [CommRing A]
    (sigma : R →+* A) (hinj : Function.Injective sigma)
    (iota : Type u) {X : Scheme.{u}}
    (f : X ⟶ Spec (CommRingCat.of A)) [IsDominant f]
    (i : X ⟶ ProjectiveSpace R iota)
    (hg : i ≫ ProjectiveSpace.toSpec R iota =
      f ≫ Spec.map (CommRingCat.ofHom sigma)) :
    IsDominant (i ≫ ProjectiveSpace.toSpec R iota) := by
  let := grSpecMap_dominant sigma hinj
  rw [hg]
  infer_instance

/-- Finiteness for the original genericImageBaseMap, without a field-finiteness premise. -/
private theorem grGenericImageBaseMap_finite
    {R A : Type u} [CommRing R] [CommRing A] [IsDomain R] [IsDomain A]
    (sigma : R →+* A) (hfinite : sigma.Finite) (hinj : Function.Injective sigma)
    (iota : Type u) {X : Scheme.{u}} [IsIntegral X]
    (f : X ⟶ Spec (CommRingCat.of A)) [IsDominant f]
    (hff : IsIso (CommRingCat.ofHom (Scheme.functionFieldMap f)))
    (i : X ⟶ ProjectiveSpace R iota)
    (hg : i ≫ ProjectiveSpace.toSpec R iota =
      f ≫ Spec.map (CommRingCat.ofHom sigma)) :
    letI := grEmbeddingMap_dominant sigma hinj iota f i hg
    (ProjectiveSpace.genericImageBaseMap R iota i).Finite := by
  let := grEmbeddingMap_dominant sigma hinj iota f i hg
  let s := Spec.map (CommRingCat.ofHom sigma)
  let : IsDominant s := grSpecMap_dominant sigma hinj
  let : IsFinite s := (IsFinite.SpecMap_iff _).mpr hfinite
  let : IsIso (CommRingCat.ofHom (Scheme.functionFieldMap f)) := hff
  have hs : (Scheme.functionFieldMap s).Finite := grFunctionFieldMap_finite s
  have hf : (Scheme.functionFieldMap f).Finite :=
    RingHom.Finite.of_surjective _
      (ConcreteCategory.bijective_of_isIso
        (CommRingCat.ofHom (Scheme.functionFieldMap f))).2
  have hcongr {a b : X ⟶ Spec (CommRingCat.of R)}
      [IsDominant a] [IsDominant b] (hab : a = b) :
      Scheme.functionFieldMap a = Scheme.functionFieldMap b := by
    subst b
    rfl
  have hmap : ProjectiveSpace.genericImageBaseMap R iota i =
      (Scheme.functionFieldMap f).comp (Scheme.functionFieldMap s) := by
    change Scheme.functionFieldMap (i ≫ ProjectiveSpace.toSpec R iota) = _
    exact (hcongr hg).trans (Scheme.functionFieldMap_comp f s)
  rw [hmap]
  exact hf.comp hs


private theorem grSpec_normalStalks (A : Type u) [CommRing A] [IsDomain A]
    [IsIntegrallyClosed A] : NormalStalks (Spec (CommRingCat.of A)) := by
  intro p
  exact (isIntegrallyClosed_and_isDomain_stalk_Spec A p).symm

attribute [local instance] AlgebraicGeometry.Scheme.Modules.standardHasDerivedCategory

/-- The standard derived-category model for modules over the coefficient ring. -/
local instance grModuleDerived (A : Type u) [CommRing A] :
    HasDerivedCategory.{u + 1} (ModuleCat.{u} A) := HasDerivedCategory.standard _

/-- The punctured isomorphism and original section comparison give finite length
for the installed H1, with its original structural action. -/
private theorem grStructure_homologyOne_finiteLength
    {A : Type u} [CommRing A] [IsDomain A] [IsLocalRing A]
    [IsNoetherianRing A] [IsIntegrallyClosed A]
    {X : Scheme.{u}} [IsIntegral X]
    (f : X ⟶ Spec (.of A)) [IsProper f] [IsDominant f]
    (hff : IsIso (CommRingCat.ofHom (Scheme.functionFieldMap f)))
    (hA : ringKrullDim A = 2)
    (IX : InjectiveResolution (SheafOfModules.unit X.ringCatSheaf : X.Modules)) :
    IsFiniteLength A
      ((DerivedCategory.Plus.homologyFunctor (ModuleCat.{u} A) 1).obj
        (moduleDerivedStructure X (normalSurfaceTraceScalar f))) := by
  let O : X.Modules := SheafOfModules.unit X.ringCatSheaf
  let α := normalSurfaceTraceScalar f
  have hiso : IsIso (f ∣_ localPuncturedSpectrum A) :=
    f.isIso_restrict_of_stalk_dimension_le_one hff (grSpec_normalStalks A)
      (localPuncturedSpectrum A) (by
        intro p hp
        exact ringKrullDim_stalk_le_one_of_ne_closedPoint A hA.le p
          ((mem_localPuncturedSpectrum A p).mp hp))
  let := moduleCohomologyModuleOfHom X α O 1
  have hlen : IsFiniteLength A (Sheaf.H.{u + 1} (moduleAddSheaf X O) 1) :=
    moduleCohomology_isFiniteLength_of_proper_of_isIso_puncturedSpectrum
      A f hiso O (affineLocallyFiniteType_unit X) 1 (by decide)
  exact (moduleDerivedGlobalSectionsSingleCohomologyLinearEquiv X α IX 1).symm.isFiniteLength
    hlen

/-- Supplied computational resolutions retain the original geometric and algebraic comparisons. -/
private theorem grCanonicalCohomology_withResolutions
    {R A : Type u} [CommRing R] [CommRing A] [IsDomain R] [IsRegularLocalRing R]
    [IsDomain A] [IsLocalRing A] [IsNoetherianRing A] [IsIntegrallyClosed A]
    [IsAdicComplete (IsLocalRing.maximalIdeal A) A]
    (σ : R →+* A) [IsLocalHom σ] (hσ : σ.Finite) (hσinj : Function.Injective σ)
    (hR : ringKrullDim R = 2) (hA : ringKrullDim A = 2)
    (ι : Type u) {X : Scheme.{u}} [IsIntegral X]
    (f : X ⟶ Spec (.of A)) [IsProper f] [IsDominant f]
    (hff : IsIso (CommRingCat.ofHom (Scheme.functionFieldMap f)))
    (hX : NormalStalks X) (hXdim : topologicalKrullDim X ≤ 2)
    (i : X ⟶ ProjectiveSpace R ι) [IsClosedImmersion i]
    [IsDominant (i ≫ ProjectiveSpace.toSpec R ι)]
    (n : ℕ) (e : ι ≃ Fin (n + 1))
    (hg : i ≫ ProjectiveSpace.toSpec R ι = f ≫ Spec.map (CommRingCat.ofHom σ))
    (hfin : (ProjectiveSpace.genericImageBaseMap R ι i).Finite)
    (IX : InjectiveResolution (SheafOfModules.unit X.ringCatSheaf : X.Modules))
    (IR : InjectiveResolution (ModuleCat.of R R)) :
    Subsingleton (Sheaf.H.{u + 1}
      (moduleAddSheaf X (normalSurfaceCanonicalModule R ι i n)) 1) := by
  let : Algebra R A := σ.toAlgebra
  let : Module.Finite R A := hσ
  let : IsLocalHom (algebraMap R A) := inferInstanceAs (IsLocalHom σ)
  let α := normalSurfaceTraceScalar f
  let Cplus := moduleDerivedStructure X α
  let C := DerivedCategory.Plus.ι.obj Cplus
  let η := moduleDerivedStructureUnit X α
  let H := (DerivedCategory.Plus.homologyFunctor (ModuleCat.{u} A) 1).obj Cplus
  let K := moduleResolutionSectionComplex X α IX
  let J := coinducedCoefficientComplex σ IR.cochainComplex
  let : IR.cochainComplex.IsKInjective :=
    CochainComplex.isKInjective_of_injective IR.cochainComplex 0
  let : J.IsKInjective := coinducedCoefficientComplex_isKInjective σ IR.cochainComplex
  let : CochainComplex.IsKInjective
      (show CochainComplex (ModuleCat.{u} A) ℤ from
        ((ModuleCat.coextendScalars σ).mapHomologicalComplex (.up ℤ)).obj IR.cochainComplex) :=
    coinducedCoefficientComplex_isKInjective σ IR.cochainComplex
  let : Cplus.IsGE 0 := moduleDerivedStructure_isGE X α
  let : Cplus.IsLE 1 := moduleDerivedStructure_isLE_of_complete_surface X f hA hXdim
  let : IsIso ((DerivedCategory.Plus.homologyFunctor (ModuleCat.{u} A) 0).map η) :=
    isIso_moduleDerivedStructureUnit_homology_of_bijective X α
      (Hom.bijective_structuralCoefficients_of_isProper_birational A f
        (grSpec_normalStalks A) hff)
  let : Module.Projective R ((ModuleCat.restrictScalars σ).obj (ModuleCat.of A A)) :=
    restrictedProjective_of_finite_normal_dimension_two σ hσ hσinj hR hA
  let : Module.Finite R ((ModuleCat.restrictScalars σ).obj (ModuleCat.of A A)) := by
    change Module.Finite R A
    exact hσ
  have hHA : IsFiniteLength A H := grStructure_homologyOne_finiteLength f hff hA IX
  have hHR : IsFiniteLength R ((ModuleCat.restrictScalars σ).obj H) :=
    grFiniteLength_restrictScalars σ hσ H hHA
  let : _root_.IsNoetherian R ((ModuleCat.restrictScalars σ).obj H) :=
    (isFiniteLength_iff_isNoetherian_isArtinian.mp hHR).1
  let : Module.Finite R ((ModuleCat.restrictScalars σ).obj H) := inferInstance
  let : IsIso ((derivedEvaluation J).app C) :=
    derivedEvaluation_isIso_of_unitPostnikov.{u, u, u, u + 1, u + 1}
      σ 2 hR (ModuleCat.of A A) Cplus η K (normalSurfaceStructureResolutionIso X α IX)
      (ModuleCat.of R R) (LinearEquiv.refl R R) IR.cochainComplex IR.ι'
  let M : ModuleCat.{u} A := ModuleCat.of A (IsLocalRing.ResidueField A)
  have hMA : IsFiniteLength A M := by
    let : IsSimpleModule A M := by
      change IsSimpleModule A (A ⧸ IsLocalRing.maximalIdeal A)
      exact (isSimpleModule_iff_isCoatom (R := A) (M := A)
        (m := (IsLocalRing.maximalIdeal A : Submodule A A))).mpr
          (Ideal.isMaximal_def.mp (IsLocalRing.maximalIdeal.isMaximal A))
    apply Module.length_ne_top_iff.mp
    rw [Module.length_eq_one]
    exact ENat.natCast_ne_top 1
  have hM : IsFiniteLength R ((ModuleCat.restrictScalars σ).obj M) :=
    grFiniteLength_restrictScalars σ hσ M hMA
  let : _root_.IsNoetherian R ((ModuleCat.restrictScalars σ).obj M) :=
    (isFiniteLength_iff_isNoetherian_isArtinian.mp hM).1
  let : Module.Finite R ((ModuleCat.restrictScalars σ).obj M) := inferInstance
  let E := (DerivedCategory.singleFunctor (ModuleCat.{u} A) 1).obj M
  let : IsIso ((derivedEvaluation J).app E) :=
    derivedEvaluation_single_isIso_of_restrictFinite.{u, u, u, u + 1}
      σ 2 hR M 1 (ModuleCat.of R R) (LinearEquiv.refl R R) IR.cochainComplex IR.ι'
  obtain ⟨ρ⟩ := nonempty_derivedResidueDegreeOneIso_of_injectiveResolution
    (R := R) (A := A) hR IR
  let : ((derivedDual J).obj (op C)).IsLE 1 :=
    TwoLayerDual.unitPostnikov_isLE_one σ IR hR Cplus η hHR
  have hN : IsFiniteLength A
      ((DerivedCategory.homologyFunctor (ModuleCat.{u} A) 1).obj
        ((derivedDual J).obj (op C))) :=
    TwoLayerDual.unitPostnikov_homologyOne_finiteLength σ IR hR Cplus η hHR
  let : Ring.KrullDimLE 2 A := Ring.krullDimLE_iff.mpr hA.le
  have hNag : IsNagataRing.{u, 0} A := IsNagataRing.of_complete_local_dimLE_two A
  have hzero : IsZero
      ((DerivedCategory.homologyFunctor (ModuleCat.{u} A) 1).obj
        ((derivedDual J).obj (op C))) :=
    isZero_dual_topHomology_of_residue_vanishing J C 1 hN ρ (by
      intro β
      exact residueField_hom_derivedGlobalSections_eq_zero_of_isNagata
        f hff hA hX hNag β)
  let := moduleCohomologyModuleOfHom X α (normalSurfaceCanonicalModule R ι i n) 1
  let eH := normalSurfaceCohomologyDualLinearEquiv R ι i hX hXdim n e hfin σ f hg IX IR 1
  let := ModuleCat.subsingleton_of_isZero hzero
  exact ⟨fun x y => eH.injective (Subsingleton.elim _ _)⟩

/-- Chosen-embedding Grauert--Riemenschneider vanishing for the literal canonical
module on a proper normal integral surface over a complete normal local surface base.
The finite generic extension, computational resolutions and algebraic duality inputs
are derived from the actual finite local map and original geometric factorization. -/
public theorem grauertRiemenschneider_chosenEmbedding
    {R A : Type u} [CommRing R] [CommRing A] [IsDomain R] [IsRegularLocalRing R]
    [IsDomain A] [IsLocalRing A] [IsNoetherianRing A] [IsIntegrallyClosed A]
    [IsAdicComplete (IsLocalRing.maximalIdeal A) A]
    (σ : R →+* A) [IsLocalHom σ] (hσ : σ.Finite) (hσinj : Function.Injective σ)
    (hR : ringKrullDim R = 2) (hA : ringKrullDim A = 2)
    (ι : Type u) {X : Scheme.{u}} [IsIntegral X]
    (f : X ⟶ Spec (.of A)) [IsProper f] [IsDominant f]
    (hff : IsIso (CommRingCat.ofHom (Scheme.functionFieldMap f)))
    (hX : NormalStalks X) (hXdim : topologicalKrullDim X ≤ 2)
    (i : X ⟶ ProjectiveSpace R ι) [IsClosedImmersion i]
    (n : ℕ) (e : ι ≃ Fin (n + 1))
    (hg : i ≫ ProjectiveSpace.toSpec R ι = f ≫ Spec.map (CommRingCat.ofHom σ)) :
    Subsingleton (Sheaf.H.{u + 1}
      (moduleAddSheaf X (normalSurfaceCanonicalModule R ι i n)) 1) := by
  let : IsDominant (i ≫ ProjectiveSpace.toSpec R ι) :=
    grEmbeddingMap_dominant σ hσinj ι f i hg
  have hfin : (ProjectiveSpace.genericImageBaseMap R ι i).Finite :=
    grGenericImageBaseMap_finite σ hσ hσinj ι f hff i hg
  let IX := injectiveResolution (SheafOfModules.unit X.ringCatSheaf : X.Modules)
  let IR := injectiveResolution (ModuleCat.of R R)
  exact grCanonicalCohomology_withResolutions σ hσ hσinj hR hA ι f hff hX hXdim
    i n e hg hfin IX IR

end AlgebraicGeometry.Scheme.Cohomology
