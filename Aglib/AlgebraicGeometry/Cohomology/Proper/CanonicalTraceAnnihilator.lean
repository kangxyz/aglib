/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Cohomology.Proper.GrauertRiemenschneider
public import Aglib.AlgebraicGeometry.Cohomology.Proper.DerivedStructure.FiniteLength
public import
  Aglib.AlgebraicGeometry.Cohomology.Duality.Projective.Relative.NormalSurface.Cohomology.UnitTrace
public import Aglib.AlgebraicGeometry.ProjectiveSpace.GenericStalk.FiniteFactorization
public import Aglib.Algebra.Category.ModuleCat.FiniteLength.LocalRestriction
public import Aglib.Algebra.Homology.ModuleCat.HomComplex.TwoLayer.Annihilator

/-!
# Original canonical trace-image annihilation of structural H1

The original chosen-embedding section trace is the literal dual structural
unit. Its image condition and actual GR vanishing feed the existing native
unit-Postnikov annihilator theorem. No rationality or trace-isomorphism
hypothesis, new duality model or compatibility premise is introduced.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian
open AlgebraicGeometry TopologicalSpace Opposite
open AlgebraicGeometry.Scheme.Modules
open CochainComplex.HomComplex

universe u

namespace AlgebraicGeometry.Scheme.Cohomology

attribute [local instance] AlgebraicGeometry.Scheme.Modules.standardHasDerivedCategory

local instance traceAnnihilatorModuleDerived (A : Type u) [CommRing A] :
    HasDerivedCategory.{u + 1} (ModuleCat.{u} A) := HasDerivedCategory.standard _

/-- A scalar in the original canonical trace-image ideal annihilates the original
structural H1. All generic-map, finite-length and dual-vanishing inputs are derived
from the actual finite base map and chosen geometric embedding. -/
theorem structureH1_annihilates_of_chosenEmbedding_trace_image
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
    (hg : i ≫ ProjectiveSpace.toSpec R ι = f ≫ Spec.map (CommRingCat.ofHom σ))
    (d : A) :
    letI := ProjectiveSpace.isDominant_of_injective_base_triangle σ hσinj ι f i hg
    let hfin := ProjectiveSpace.genericImageBaseMap_finite_of_finite_base_triangle
      σ hσ hσinj ι f hff i hg
    letI := moduleCategoryLinearOfHom X (normalSurfaceTraceScalar f)
    letI : Module A Γ(normalSurfaceCanonicalModule R ι i n, ⊤) :=
      Module.compHom _ (normalSurfaceTraceScalar f)
    (∀ φ : (ModuleCat.coextendScalars σ).obj (ModuleCat.of R R),
      d • φ ∈ LinearMap.range
        (normalSurfaceSectionsTraceCoinduced R ι i hX hXdim n e hfin σ f hg)) →
    letI := moduleCohomologyModuleOfHom X (normalSurfaceTraceScalar f)
      (SheafOfModules.unit X.ringCatSheaf) 1
    ∀ x : Sheaf.H.{u + 1}
      (moduleAddSheaf X (SheafOfModules.unit X.ringCatSheaf)) 1, d • x = 0 := by
  dsimp only
  let : IsDominant (i ≫ ProjectiveSpace.toSpec R ι) :=
    ProjectiveSpace.isDominant_of_injective_base_triangle σ hσinj ι f i hg
  let hfin := ProjectiveSpace.genericImageBaseMap_finite_of_finite_base_triangle
    σ hσ hσinj ι f hff i hg
  let α := normalSurfaceTraceScalar f
  let := moduleCategoryLinearOfHom X α
  let : Module A Γ(normalSurfaceCanonicalModule R ι i n, ⊤) := Module.compHom _ α
  intro himage
  let O : X.Modules := SheafOfModules.unit X.ringCatSheaf
  let IX := injectiveResolution O
  let IR := injectiveResolution (ModuleCat.of R R)
  let Cplus := moduleDerivedStructure X α
  let C := DerivedCategory.Plus.ι.obj Cplus
  let η := moduleDerivedStructureUnit X α
  let H := (DerivedCategory.Plus.homologyFunctor (ModuleCat.{u} A) 1).obj Cplus
  let : Cplus.IsGE 0 := moduleDerivedStructure_isGE X α
  let : Cplus.IsLE 1 := moduleDerivedStructure_isLE_of_complete_surface X f hA hXdim
  let : IsIso ((DerivedCategory.Plus.homologyFunctor (ModuleCat.{u} A) 0).map η) :=
    isIso_moduleDerivedStructureUnit_homology_of_bijective X α
      (Hom.bijective_structuralCoefficients_of_isProper_birational A f
        (fun p => (isIntegrallyClosed_and_isDomain_stalk_Spec A p).symm) hff)
  let : Module.Projective R ((ModuleCat.restrictScalars σ).obj (ModuleCat.of A A)) :=
    restrictedProjective_of_finite_normal_dimension_two σ hσ hσinj hR hA
  let : IR.cochainComplex.IsKInjective :=
    CochainComplex.isKInjective_of_injective IR.cochainComplex 0
  let : (TwoLayerDual.resolutionCoefficient σ IR).IsKInjective :=
    coinducedCoefficientComplex_isKInjective σ IR.cochainComplex
  have hHA : IsFiniteLength A H :=
    moduleDerivedStructure_homologyOne_finiteLength_of_proper_birational_surface
      f hff hA IX
  have hHR : IsFiniteLength R ((ModuleCat.restrictScalars σ).obj H) :=
    ModuleCat.finiteLength_restrictScalars_of_finite_local σ hσ H hHA
  let ω : X.Modules := normalSurfaceCanonicalModule R ι i n
  let := moduleCohomologyModuleOfHom X α ω 1
  let eH := normalSurfaceCohomologyDualLinearEquiv
    R ι i hX hXdim n e hfin σ f hg IX IR 1
  let : Subsingleton (Sheaf.H.{u + 1} (moduleAddSheaf X ω) 1) :=
    grauertRiemenschneider_chosenEmbedding σ hσ hσinj hR hA ι f hff hX hXdim i n e hg
  have hdual : IsZero (TwoLayerDual.homology (TwoLayerDual.resolutionCoefficient σ IR) 1 C) := by
    let : Subsingleton (TwoLayerDual.homology
        (TwoLayerDual.resolutionCoefficient σ IR) 1 C) := eH.toEquiv.symm.subsingleton
    exact ModuleCat.isZero_of_subsingleton _
  let := moduleCohomologyModuleOfHom X α ω 0
  let e₀ := normalSurfaceCohomologyDualLinearEquiv
    R ι i hX hXdim n e hfin σ f hg IX IR 0
  let E₀ := Sheaf.H.equiv₀ (moduleAddSheaf X ω) isTerminalTop
  have hunitImage : ∀ φ : coinducedCoefficient σ,
      d • φ ∈ LinearMap.range
        (TwoLayerDual.unitMap σ IR C (DerivedCategory.Plus.ι.map η)) := by
    intro φ
    obtain ⟨s, hs⟩ := himage φ
    let x₀ := E₀.symm s
    refine ⟨e₀ x₀, ?_⟩
    have htrace := normalSurfaceCohomologyDual_unit_trace
      R ι i hX hXdim n e hfin σ f hg IX IR hσ hσinj hR hA x₀
    exact htrace.trans ((congrArg
      (normalSurfaceSectionsTraceCoinduced R ι i hX hXdim n e hfin σ f hg)
      (E₀.apply_symm_apply s)).trans hs)
  have hkill : ∀ m : H, d • m = 0 :=
    TwoLayerDual.unitPostnikov_scalar_annihilates_of_image
      σ IR Cplus η hR hHR hdual d hunitImage
  let := moduleCohomologyModuleOfHom X α O 1
  let E := moduleDerivedGlobalSectionsSingleCohomologyLinearEquiv X α IX 1
  intro x
  obtain ⟨m, rfl⟩ := E.surjective x
  calc
    d • E m = E (d • m) := (E.map_smul d m).symm
    _ = E 0 := congrArg E (hkill m)
    _ = 0 := map_zero E

end AlgebraicGeometry.Scheme.Cohomology
