/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Cohomology.Duality.Projective.Relative.NormalSurface.Trace.Proper
public import Aglib.AlgebraicGeometry.Cohomology.ProjectionFormula.StructureUnit
public import Aglib.AlgebraicGeometry.Modules.Coherent.Projective.Presentation
public import Aglib.AlgebraicGeometry.Modules.Coherent.Subobjects
public import Aglib.AlgebraicGeometry.Modules.QuasiCoherent.Limits

/-!
# Detecting the original proper canonical trace by vector bundles

Actual finite sums of negative twists detect isomorphisms between coherent
module sheaves. This detection uses a coherent kernel and genuine epimorphic
presentations; it is not a faithfulness assertion about global sections.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open AlgebraicGeometry.Scheme.Modules AlgebraicGeometry.Scheme.Modules.QuasiCoherent

universe u

namespace AlgebraicGeometry.Scheme.Modules

/-- Actual finite negative-twist presentations of the target and coherent kernel
make vector-bundle Hom bijectivity detect an isomorphism. -/
theorem isIso_of_coherent_projective_vectorBundleHom_bijective
    (R : Type u) [CommRing R] [IsNoetherianRing R] (ι : Type u) [Finite ι]
    {X : Scheme.{u}} (i : X ⟶ ProjectiveSpace R ι) [IsClosedImmersion i]
    {F G : X.Modules} [F.IsQuasicoherent] [G.IsQuasicoherent]
    (hF : affineLocallyFiniteType X F) (hG : affineLocallyFiniteType X G)
    (a : F ⟶ G)
    (h : ∀ (N : X.Modules), IsFiniteLocallyFree X N →
      Function.Bijective (fun k : N ⟶ F => k ≫ a)) : IsIso a := by
  let : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian i
  obtain ⟨n, hn, I, hI, π, hπ, hfree⟩ :=
    Coherent.Projective.exists_uniformNegativeTwistEpimorphism R ι i G hG 0
  let := hI
  let := hπ
  obtain ⟨k, hk⟩ := (h _ hfree).surjective π
  let : Epi a := epi_of_epi_fac hk
  let : (kernel a).IsQuasicoherent := quasicoherent_kernel a
  have hK : affineLocallyFiniteType X (kernel a) :=
    Coherent.affineLocallyFiniteType_of_quasicoherent_mono (kernel.ι a) hF
  obtain ⟨m, hm, J, hJ, σ, hσ, hfree'⟩ :=
    Coherent.Projective.exists_uniformNegativeTwistEpimorphism R ι i (kernel a) hK 0
  let := hJ
  let := hσ
  have hzero : σ ≫ kernel.ι a = 0 := by
    apply (h _ hfree').injective
    simp only [Category.assoc, kernel.condition, comp_zero, zero_comp]
  let : Mono a := CategoryTheory.Abelian.mono_of_kernel_ι_eq_zero a
    ((cancel_epi σ).mp (by simpa only [comp_zero] using hzero))
  exact isIso_of_mono_of_epi a

end AlgebraicGeometry.Scheme.Modules

namespace AlgebraicGeometry.Scheme.Cohomology

open AlgebraicGeometry.ProjectiveSpace

attribute [local instance] AlgebraicGeometry.Scheme.Modules.standardHasDerivedCategory
local instance canonicalTraceIsoModuleDerived (A : Type u) [CommRing A] :
    HasDerivedCategory.{u + 1} (ModuleCat.{u} A) := HasDerivedCategory.standard _

variable (R : Type u) [CommRing R] [IsDomain R] [IsRegularLocalRing R]
    (ιX ιY : Type u) {X Y : Scheme.{u}} [IsIntegral X] [IsIntegral Y]
    (b : Y ⟶ X) [IsProper b]
    (iX : X ⟶ ProjectiveSpace R ιX) [IsClosedImmersion iX]
    [IsDominant (iX ≫ toSpec R ιX)]
    (iY : Y ⟶ ProjectiveSpace R ιY) [IsClosedImmersion iY]
    [IsDominant (iY ≫ toSpec R ιY)]
    (hb : iY ≫ toSpec R ιY = b ≫ (iX ≫ toSpec R ιX))
    (hX : NormalStalks X) (hXdim : topologicalKrullDim X ≤ 2)
    (hY : NormalStalks Y) (hYdim : topologicalKrullDim Y ≤ 2)
    (nX nY : ℕ) (eX : ιX ≃ Fin (nX + 1)) (eY : ιY ≃ Fin (nY + 1))
    (hfinX : (genericImageBaseMap R ιX iX).Finite)
    (hfinY : (genericImageBaseMap R ιY iY).Finite)
    [IsIso (moduleDerivedPushforwardUnit X b)]

/-- The original structure-unit isomorphism gives bijectivity on Hom from every
finite locally free coefficient, by original adjunction and coherent Serre duality. -/
theorem normalSurfaceProperCanonicalTrace_vectorBundleHom_bijective
    (N : X.Modules) [IsFiniteLocallyFree X N] :
    Function.Bijective (fun a : N ⟶ (pushforward b).obj
        (normalSurfaceCanonicalModule R ιY iY nY) =>
      a ≫ normalSurfaceProperCanonicalTrace R ιX ιY b iX iY hb hX hXdim hY hYdim
        nX nY eX eY hfinX hfinY) := by
  let P : Y.Modules := (Scheme.Modules.pullback b).obj N
  let α := chosenEmbeddingBaseScalar R iX (toSpec R ιX)
  let β := chosenEmbeddingBaseScalar R iY (toSpec R ιY)
  let FX := (moduleGlobalSectionsFunctorOfHom X α).rightDerivedFunctorPlus
  let EX := normalSurfaceFiniteCoherentSerreAddEquiv R ιX iX hX hXdim nX eX hfinX N
    (affineLocallyFiniteType_of_finitePresentation N)
  let EY := normalSurfaceFiniteCoherentSerreAddEquiv R ιY iY hY hYdim nY eY hfinY P
    (affineLocallyFiniteType_of_finitePresentation P)
  let A := (pullbackPushforwardAdjunction b).homEquiv N
    (normalSurfaceCanonicalModule R ιY iY nY)
  let u := (DerivedCategory.Plus.singleFunctor X.Modules 0).map
      ((pullbackPushforwardAdjunction b).unit.app N) ≫
    (pushforward b).rightDerivedSingleUnit P
  let : IsIso u := isIso_derivedPullbackPushforwardUnit_of_structureUnit b N
  let C := properSerreGlobalSectionsComp b α β
    (normalSurfaceFiniteEmbeddingScalar b iX iY hb) P
  let e := asIso (FX.map u) ≪≫ C.symm
  have he : Function.Bijective (fun k : normalSurfaceFiniteSectionsObject Y β P ⟶
      (DerivedCategory.Plus.singleFunctor (ModuleCat.{u} R) 0).obj (ModuleCat.of R R) =>
      e.hom ≫ k) := by
    let E := Iso.homCongr e.symm (Iso.refl
      ((DerivedCategory.Plus.singleFunctor (ModuleCat.{u} R) 0).obj (ModuleCat.of R R)))
    have hE : (fun k : normalSurfaceFiniteSectionsObject Y β P ⟶
        (DerivedCategory.Plus.singleFunctor (ModuleCat.{u} R) 0).obj (ModuleCat.of R R) =>
        e.hom ≫ k) = E := by
      funext k
      simp only [E, Iso.homCongr_apply, Iso.symm_inv, Iso.refl_hom, Category.comp_id]
    rw [hE]
    exact E.bijective
  have hf : (fun a => EX (a ≫ normalSurfaceProperCanonicalTrace R ιX ιY b iX iY hb
      hX hXdim hY hYdim nX nY eX eY hfinX hfinY)) =
      (fun a => e.hom ≫ EY (A.symm a)) := by
    funext a
    change normalSurfaceFiniteCoherentSerreMap R ιX iX hX hXdim nX eX hfinX N
      (a ≫ normalSurfaceProperCanonicalTrace R ιX ιY b iX iY hb
        hX hXdim hY hYdim nX nY eX eY hfinX hfinY) = _
    rw [normalSurfaceProperCanonicalTrace_source, normalSurfaceProperTraceFunctional_mate]
    change FX.map u ≫ C.inv ≫ EY (A.symm a) =
      (FX.map u ≫ C.inv) ≫ EY (A.symm a)
    exact (Category.assoc _ _ _).symm
  have hbij : Function.Bijective (fun a => EX
      (a ≫ normalSurfaceProperCanonicalTrace R ιX ιY b iX iY hb
        hX hXdim hY hYdim nX nY eX eY hfinX hfinY)) := by
    rw [hf]
    exact he.comp (EY.bijective.comp A.symm.bijective)
  exact hbij.of_comp_left EX.injective

/-- The actual proper canonical trace is invertible when the original derived
structure unit is invertible. No invertibility of a coefficient unit or of the
trace is supplied as a hypothesis. -/
theorem normalSurfaceProperCanonicalTrace_isIso_of_structureUnit :
    IsIso (normalSurfaceProperCanonicalTrace R ιX ιY b iX iY hb
      hX hXdim hY hYdim nX nY eX eY hfinX hfinY) := by
  let : Finite ιX := Finite.of_equiv _ eX.symm
  let F := (pushforward b).obj (normalSurfaceCanonicalModule R ιY iY nY)
  have hF : affineLocallyFiniteType X F :=
    normalSurfaceProperCanonicalPushforward_finiteType R ιX ιY b iX iY nX nY eX eY
  let : F.IsQuasicoherent := quasicoherent_of_affineLocallyFiniteType hF
  have hG := normalSurfaceCanonicalModule_finiteType R ιX iX nX eX
  let : (normalSurfaceCanonicalModule R ιX iX nX).IsQuasicoherent :=
    quasicoherent_of_affineLocallyFiniteType hG
  apply isIso_of_coherent_projective_vectorBundleHom_bijective R ιX iX hF hG
  intro N hN
  let := hN
  exact normalSurfaceProperCanonicalTrace_vectorBundleHom_bijective
    R ιX ιY b iX iY hb hX hXdim hY hYdim nX nY eX eY hfinX hfinY N

end AlgebraicGeometry.Scheme.Cohomology
