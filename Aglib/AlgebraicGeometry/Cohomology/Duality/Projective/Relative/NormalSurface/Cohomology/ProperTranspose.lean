/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Cohomology.Duality.Projective.Relative.NormalSurface.Cohomology.Finite

/-!
# Original global Serre transposition of the one-pole derived morphism

The transpose is constructed by the actual coherent-source Serre inverse.
Its normalization retains the original global-sections composition, the
supplied native derived morphism, and the ordinary coefficient map.
The native one-pole producer is a separate geometric dependency.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian AlgebraicGeometry
open AlgebraicGeometry.ProjectiveSpace AlgebraicGeometry.Scheme.Modules
open AlgebraicGeometry.Scheme.Modules.QuasiCoherent
open Opposite HomologicalComplex

universe u

private theorem properSerre_functional_comp
    {C D : Type*} [Category* C] [Category* D] (F : C ⥤ D)
    {K L M : C} {S T : D} (c : S ⟶ F.obj K) (ψ : K ⟶ L) (φ : L ⟶ M)
    (q : F.obj L ⟶ T) (t : F.obj M ⟶ T) (hq : q = F.map φ ≫ t) :
    c ≫ F.map ψ ≫ q = c ≫ F.map (ψ ≫ φ) ≫ t := by
  rw [hq, F.map_comp]
  simp only [Category.assoc]

private theorem properSerre_source_paste
    {C D : Type*} [Category* C] [Category* D] (F : C ⥤ D)
    {K K' L : C} {S S' T : D}
    (m : K' ⟶ K) (ψ : K ⟶ L) (c' : S' ⟶ F.obj K') (c : S ⟶ F.obj K)
    (a : S' ⟶ S) (q : F.obj L ⟶ T) (hc : a ≫ c = c' ≫ F.map m) :
    c' ≫ F.map (m ≫ ψ) ≫ q = a ≫ c ≫ F.map ψ ≫ q := by
  rw [F.map_comp]
  simpa only [Category.assoc] using
    congrArg (fun z => z ≫ F.map ψ ≫ q) hc.symm

private theorem properSerre_unit_section_paste
    {C D : Type*} [Category* C] [Category* D] (F : C ⥤ D)
    {K₀ K₁ K₂ K₃ : C} {A B E T : D}
    (u : K₀ ⟶ K₁) (s : K₁ ⟶ K₂) (ψ : K₂ ⟶ K₃)
    (ηX : A ⟶ F.obj K₀) (ηY : A ⟶ B) (k : B ⟶ E)
    (cO : B ⟶ F.obj K₁) (cL : E ⟶ F.obj K₂) (q : F.obj K₃ ⟶ T)
    (hη : ηY ≫ cO = ηX ≫ F.map u) (hk : k ≫ cL = cO ≫ F.map s) :
    ηY ≫ k ≫ cL ≫ F.map ψ ≫ q = ηX ≫ F.map (u ≫ s ≫ ψ) ≫ q := by
  rw [F.map_comp, F.map_comp]
  calc
    _ = ηY ≫ (k ≫ cL) ≫ F.map ψ ≫ q := by simp only [Category.assoc]
    _ = ηY ≫ (cO ≫ F.map s) ≫ F.map ψ ≫ q :=
      congrArg (fun z => ηY ≫ z ≫ F.map ψ ≫ q) hk
    _ = (ηY ≫ cO) ≫ F.map s ≫ F.map ψ ≫ q := by simp only [Category.assoc]
    _ = (ηX ≫ F.map u) ≫ F.map s ≫ F.map ψ ≫ q :=
      congrArg (fun z => z ≫ F.map s ≫ F.map ψ ≫ q) hη
    _ = _ := by simp only [Category.assoc]

namespace AlgebraicGeometry.Scheme.Cohomology

attribute [local instance] AlgebraicGeometry.Scheme.Modules.standardHasDerivedCategory
local instance properSerreTransposeModuleDerived (A : Type u) [CommRing A] :
    HasDerivedCategory.{u + 1} (ModuleCat.{u} A) := HasDerivedCategory.standard _

/-- Original global-sections composition with scalar equality from the actual triangle. -/
def properSerreGlobalSectionsComp
    {R : Type u} [CommRing R] {X Y : Scheme.{u}}
    (b : Y ⟶ X) (α : R →+* Γ(X, ⊤)) (β : R →+* Γ(Y, ⊤))
    (hβ : b.appTop.hom.comp α = β) (M : Y.Modules) :
    normalSurfaceFiniteSectionsObject Y β M ≅
      (moduleGlobalSectionsFunctorOfHom X α).rightDerivedFunctorPlus.obj
        ((derivedPushforwardPlus b).obj
          ((DerivedCategory.Plus.singleFunctor Y.Modules 0).obj M)) :=
  eqToIso (congrArg (fun γ => normalSurfaceFiniteSectionsObject Y γ M) hβ.symm) ≪≫
    (moduleDerivedGlobalSectionsPushforwardCompIso b α).app
      ((DerivedCategory.Plus.singleFunctor Y.Modules 0).obj M)

/-- Every original ordinary source map is retained by the same composition. -/
theorem properSerreGlobalSectionsComp_naturality
    {R : Type u} [CommRing R] {X Y : Scheme.{u}}
    (b : Y ⟶ X) (α : R →+* Γ(X, ⊤)) (β : R →+* Γ(Y, ⊤))
    (hβ : b.appTop.hom.comp α = β) {M N : Y.Modules} (m : M ⟶ N) :
    (moduleGlobalSectionsFunctorOfHom Y β).rightDerivedFunctorPlus.map
        ((DerivedCategory.Plus.singleFunctor Y.Modules 0).map m) ≫
        (properSerreGlobalSectionsComp b α β hβ N).hom =
      (properSerreGlobalSectionsComp b α β hβ M).hom ≫
        (moduleGlobalSectionsFunctorOfHom X α).rightDerivedFunctorPlus.map
          ((derivedPushforwardPlus b).map
            ((DerivedCategory.Plus.singleFunctor Y.Modules 0).map m)) := by
  subst β
  simp only [properSerreGlobalSectionsComp, eqToIso_refl]
  erw [Iso.refl_trans, Iso.refl_trans]
  convert (moduleDerivedGlobalSectionsPushforwardCompIso b α).hom.naturality
    ((DerivedCategory.Plus.singleFunctor Y.Modules 0).map m) using 1
  rfl

/-- The actual proper global-sections composition retains the original structural unit. -/
theorem properSerreGlobalSectionsComp_structureUnit
    {R : Type u} [CommRing R] {X Y : Scheme.{u}}
    (b : Y ⟶ X) (α : R →+* Γ(X, ⊤)) (β : R →+* Γ(Y, ⊤))
    (hβ : b.appTop.hom.comp α = β) :
    moduleDerivedStructureUnit Y β ≫
        (properSerreGlobalSectionsComp b α β hβ (normalSurfaceUnit Y)).hom =
      moduleDerivedStructureUnit X α ≫
        (moduleGlobalSectionsFunctorOfHom X α).rightDerivedFunctorPlus.map
          (moduleDerivedPushforwardUnit X b) := by
  subst β
  simp only [properSerreGlobalSectionsComp, eqToIso_refl]
  erw [Iso.refl_trans]
  convert (moduleDerivedStructureUnit_pushforward b α).symm using 1
  rfl

variable (R : Type u) [CommRing R] [IsDomain R] [IsRegularLocalRing R]
    (ιX ιY : Type u) {X Y : Scheme.{u}} [IsIntegral X] [IsIntegral Y]
    (b : Y ⟶ X)
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

include hb hX hXdim hY hYdim eX eY hfinX hfinY

/-- Transpose the actual derived one-pole arrow followed by the actual ordinary
coefficient map, using the original coherent-source Serre inverse. -/
def normalSurfaceProperSerreTranspose
    (LX : X.Modules) (LY : Y.Modules) [LY.IsQuasicoherent]
    (hLY : affineLocallyFiniteType Y LY)
    (Ψ : (derivedPushforwardPlus b).obj
        ((DerivedCategory.Plus.singleFunctor Y.Modules 0).obj LY) ⟶
      (DerivedCategory.Plus.singleFunctor X.Modules 0).obj LX)
    (φX : LX ⟶ normalSurfaceCanonicalModule R ιX iX nX) :
    LY ⟶ normalSurfaceCanonicalModule R ιY iY nY := by
  let α := chosenEmbeddingBaseScalar R iX (toSpec R ιX)
  let β := chosenEmbeddingBaseScalar R iY (toSpec R ιY)
  let c := properSerreGlobalSectionsComp b α β
    (normalSurfaceFiniteEmbeddingScalar b iX iY hb) LY
  let F := (moduleGlobalSectionsFunctorOfHom X α).rightDerivedFunctorPlus
  let EX := normalSurfaceFiniteCoherentSerreMap R ιX iX hX hXdim nX eX hfinX LX
  let EY := normalSurfaceFiniteCoherentSerreAddEquiv R ιY iY hY hYdim nY eY hfinY LY hLY
  exact EY.symm (c.hom ≫ F.map Ψ ≫ EX φX)

/-- The defining normalization uses the SAME original map, rather than a supplied
trace-compatibility condition. -/
theorem normalSurfaceProperSerreTranspose_normalization
    (LX : X.Modules) (LY : Y.Modules) [LY.IsQuasicoherent]
    (hLY : affineLocallyFiniteType Y LY)
    (Ψ : (derivedPushforwardPlus b).obj
        ((DerivedCategory.Plus.singleFunctor Y.Modules 0).obj LY) ⟶
      (DerivedCategory.Plus.singleFunctor X.Modules 0).obj LX)
    (φX : LX ⟶ normalSurfaceCanonicalModule R ιX iX nX) :
    let α := chosenEmbeddingBaseScalar R iX (toSpec R ιX)
    let β := chosenEmbeddingBaseScalar R iY (toSpec R ιY)
    let c := properSerreGlobalSectionsComp b α β
      (normalSurfaceFiniteEmbeddingScalar b iX iY hb) LY
    normalSurfaceFiniteCoherentSerreMap R ιY iY hY hYdim nY eY hfinY LY
        (normalSurfaceProperSerreTranspose R ιX ιY b iX iY hb
          hX hXdim hY hYdim nX nY eX eY hfinX hfinY LX LY hLY Ψ φX) =
      c.hom ≫ (moduleGlobalSectionsFunctorOfHom X α).rightDerivedFunctorPlus.map Ψ ≫
        normalSurfaceFiniteCoherentSerreMap R ιX iX hX hXdim nX eX hfinX LX φX := by
  let EY := normalSurfaceFiniteCoherentSerreAddEquiv R ιY iY hY hYdim nY eY hfinY LY hLY
  exact EY.apply_symm_apply _

/-- The original ordinary coefficient map is explicitly composed with Ψ before
the original canonical trace of X. This is an equality of actual R-derived arrows. -/
theorem normalSurfaceProperSerreTranspose_canonical_functional
    (LX : X.Modules) (LY : Y.Modules) [LY.IsQuasicoherent]
    (hLY : affineLocallyFiniteType Y LY)
    (Ψ : (derivedPushforwardPlus b).obj
        ((DerivedCategory.Plus.singleFunctor Y.Modules 0).obj LY) ⟶
      (DerivedCategory.Plus.singleFunctor X.Modules 0).obj LX)
    (φX : LX ⟶ normalSurfaceCanonicalModule R ιX iX nX) :
    let α := chosenEmbeddingBaseScalar R iX (toSpec R ιX)
    let β := chosenEmbeddingBaseScalar R iY (toSpec R ιY)
    let c := properSerreGlobalSectionsComp b α β
      (normalSurfaceFiniteEmbeddingScalar b iX iY hb) LY
    normalSurfaceFiniteCoherentSerreMap R ιY iY hY hYdim nY eY hfinY LY
        (normalSurfaceProperSerreTranspose R ιX ιY b iX iY hb
          hX hXdim hY hYdim nX nY eX eY hfinX hfinY LX LY hLY Ψ φX) =
      c.hom ≫ (moduleGlobalSectionsFunctorOfHom X α).rightDerivedFunctorPlus.map
        (Ψ ≫ (DerivedCategory.Plus.singleFunctor X.Modules 0).map φX) ≫
        normalSurfaceFiniteCoherentSerreMap R ιX iX hX hXdim nX eX hfinX
          (normalSurfaceCanonicalModule R ιX iX nX) (𝟙 _) := by
  let α := chosenEmbeddingBaseScalar R iX (toSpec R ιX)
  let β := chosenEmbeddingBaseScalar R iY (toSpec R ιY)
  let c := properSerreGlobalSectionsComp b α β
    (normalSurfaceFiniteEmbeddingScalar b iX iY hb) LY
  let F := (moduleGlobalSectionsFunctorOfHom X α).rightDerivedFunctorPlus
  let S := DerivedCategory.Plus.singleFunctor X.Modules 0
  let ω : X.Modules := normalSurfaceCanonicalModule R ιX iX nX
  let q := normalSurfaceFiniteCoherentSerreMap R ιX iX hX hXdim nX eX hfinX LX φX
  let τ := normalSurfaceFiniteCoherentSerreMap R ιX iX hX hXdim nX eX hfinX ω (𝟙 ω)
  have hq : q = F.map (S.map φX) ≫ τ :=
    (congrArg (normalSurfaceFiniteCoherentSerreMap R ιX iX hX hXdim nX eX hfinX LX)
      (Category.comp_id φX)).symm.trans
        (normalSurfaceFiniteCoherentSerreMap_precomp R ιX iX hX hXdim nX eX hfinX
          φX (𝟙 ω))
  exact (normalSurfaceProperSerreTranspose_normalization R ιX ιY b iX iY hb
    hX hXdim hY hYdim nX nY eX eY hfinX hfinY LX LY hLY Ψ φX).trans
      (properSerre_functional_comp F c.hom Ψ (S.map φX) q τ hq)

/-- The transpose preserves every original ordinary source map. -/
theorem normalSurfaceProperSerreTranspose_source
    (LX : X.Modules) {MY LY : Y.Modules} [MY.IsQuasicoherent] [LY.IsQuasicoherent]
    (hMY : affineLocallyFiniteType Y MY) (hLY : affineLocallyFiniteType Y LY)
    (k : MY ⟶ LY)
    (Ψ : (derivedPushforwardPlus b).obj
        ((DerivedCategory.Plus.singleFunctor Y.Modules 0).obj LY) ⟶
      (DerivedCategory.Plus.singleFunctor X.Modules 0).obj LX)
    (φX : LX ⟶ normalSurfaceCanonicalModule R ιX iX nX) :
    normalSurfaceProperSerreTranspose R ιX ιY b iX iY hb
        hX hXdim hY hYdim nX nY eX eY hfinX hfinY LX MY hMY
          ((derivedPushforwardPlus b).map
            ((DerivedCategory.Plus.singleFunctor Y.Modules 0).map k) ≫ Ψ) φX =
      k ≫ normalSurfaceProperSerreTranspose R ιX ιY b iX iY hb
        hX hXdim hY hYdim nX nY eX eY hfinX hfinY LX LY hLY Ψ φX := by
  let α := chosenEmbeddingBaseScalar R iX (toSpec R ιX)
  let β := chosenEmbeddingBaseScalar R iY (toSpec R ιY)
  let cM := properSerreGlobalSectionsComp b α β
    (normalSurfaceFiniteEmbeddingScalar b iX iY hb) MY
  let cL := properSerreGlobalSectionsComp b α β
    (normalSurfaceFiniteEmbeddingScalar b iX iY hb) LY
  let F := (moduleGlobalSectionsFunctorOfHom X α).rightDerivedFunctorPlus
  let G := (moduleGlobalSectionsFunctorOfHom Y β).rightDerivedFunctorPlus
  let S := DerivedCategory.Plus.singleFunctor Y.Modules 0
  let m := (derivedPushforwardPlus b).map (S.map k)
  let a := G.map (S.map k)
  let q := normalSurfaceFiniteCoherentSerreMap R ιX iX hX hXdim nX eX hfinX LX φX
  let φY := normalSurfaceProperSerreTranspose R ιX ιY b iX iY hb
    hX hXdim hY hYdim nX nY eX eY hfinX hfinY LX LY hLY Ψ φX
  let EM := normalSurfaceFiniteCoherentSerreAddEquiv R ιY iY hY hYdim nY eY hfinY MY hMY
  have hc : a ≫ cL.hom = cM.hom ≫ F.map m :=
    properSerreGlobalSectionsComp_naturality b α β
      (normalSurfaceFiniteEmbeddingScalar b iX iY hb) k
  have hL : normalSurfaceFiniteCoherentSerreMap R ιY iY hY hYdim nY eY hfinY LY φY =
      cL.hom ≫ F.map Ψ ≫ q :=
    normalSurfaceProperSerreTranspose_normalization R ιX ιY b iX iY hb
      hX hXdim hY hYdim nX nY eX eY hfinX hfinY LX LY hLY Ψ φX
  apply EM.injective
  calc
    _ = cM.hom ≫ F.map (m ≫ Ψ) ≫ q :=
      normalSurfaceProperSerreTranspose_normalization R ιX ιY b iX iY hb
        hX hXdim hY hYdim nX nY eX eY hfinX hfinY LX MY hMY (m ≫ Ψ) φX
    _ = a ≫ cL.hom ≫ F.map Ψ ≫ q :=
      properSerre_source_paste F m Ψ cM.hom cL.hom a q hc
    _ = a ≫ normalSurfaceFiniteCoherentSerreMap R ιY iY hY hYdim nY eY hfinY LY φY :=
      congrArg (fun z => a ≫ z) hL.symm
    _ = _ := (normalSurfaceFiniteCoherentSerreMap_precomp
      R ιY iY hY hYdim nY eY hfinY k φY).symm


/-- The original structural unit evaluates every transposed ordinary section through
the actual one-pole arrow and the unchanged coefficient map. -/
theorem normalSurfaceProperSerreTranspose_section_trace
    (LX : X.Modules) (LY : Y.Modules) [LY.IsQuasicoherent]
    (hLY : affineLocallyFiniteType Y LY)
    (Ψ : (derivedPushforwardPlus b).obj
        ((DerivedCategory.Plus.singleFunctor Y.Modules 0).obj LY) ⟶
      (DerivedCategory.Plus.singleFunctor X.Modules 0).obj LX)
    (φX : LX ⟶ normalSurfaceCanonicalModule R ιX iX nX)
    (s : (normalSurfaceUnit Y : Y.Modules) ⟶ LY) :
    normalSurfaceSectionsTraceBase R ιY iY hY hYdim nY eY hfinY
        (normalSurfaceFiniteUnitHomSections Y (normalSurfaceCanonicalModule R ιY iY nY)
          (s ≫ normalSurfaceProperSerreTranspose R ιX ιY b iX iY hb
            hX hXdim hY hYdim nX nY eX eY hfinX hfinY LX LY hLY Ψ φX)) =
      normalSurfaceFiniteEndEvaluation R
        (moduleDerivedStructureUnit X (chosenEmbeddingBaseScalar R iX (toSpec R ιX)) ≫
          (moduleGlobalSectionsFunctorOfHom X
            (chosenEmbeddingBaseScalar R iX (toSpec R ιX))).rightDerivedFunctorPlus.map
              (moduleDerivedPushforwardUnit X b ≫
                (derivedPushforwardPlus b).map
                  ((DerivedCategory.Plus.singleFunctor Y.Modules 0).map s) ≫ Ψ) ≫
          normalSurfaceFiniteCoherentSerreMap R ιX iX hX hXdim nX eX hfinX LX φX) := by
  let α := chosenEmbeddingBaseScalar R iX (toSpec R ιX)
  let β := chosenEmbeddingBaseScalar R iY (toSpec R ιY)
  let hβ := normalSurfaceFiniteEmbeddingScalar b iX iY hb
  let F := (moduleGlobalSectionsFunctorOfHom X α).rightDerivedFunctorPlus
  let G := (moduleGlobalSectionsFunctorOfHom Y β).rightDerivedFunctorPlus
  let S := DerivedCategory.Plus.singleFunctor Y.Modules 0
  let cO := properSerreGlobalSectionsComp b α β hβ (normalSurfaceUnit Y)
  let cL := properSerreGlobalSectionsComp b α β hβ LY
  let u := moduleDerivedPushforwardUnit X b
  let k := G.map (S.map s)
  let rb := (derivedPushforwardPlus b).map (S.map s)
  let ηX := moduleDerivedStructureUnit X α
  let ηY := moduleDerivedStructureUnit Y β
  let q := normalSurfaceFiniteCoherentSerreMap R ιX iX hX hXdim nX eX hfinX LX φX
  let φY := normalSurfaceProperSerreTranspose R ιX ιY b iX iY hb
    hX hXdim hY hYdim nX nY eX eY hfinX hfinY LX LY hLY Ψ φX
  let H := normalSurfaceFiniteUnitHomSections Y (normalSurfaceCanonicalModule R ιY iY nY)
  have hL : normalSurfaceFiniteCoherentSerreMap R ιY iY hY hYdim nY eY hfinY LY φY =
      cL.hom ≫ F.map Ψ ≫ q :=
    normalSurfaceProperSerreTranspose_normalization R ιX ιY b iX iY hb
      hX hXdim hY hYdim nX nY eX eY hfinX hfinY LX LY hLY Ψ φX
  have hSection :
      normalSurfaceFiniteSectionSerreEquiv R ιY iY hY hYdim nY eY hfinY (H (s ≫ φY)) =
        k ≫ cL.hom ≫ F.map Ψ ≫ q :=
    (normalSurfaceFiniteSectionSerreEquiv_unitHom
      R ιY iY hY hYdim nY eY hfinY (s ≫ φY)).trans
        ((normalSurfaceFiniteCoherentSerreMap_precomp
          R ιY iY hY hYdim nY eY hfinY s φY).trans
            (congrArg (fun z => k ≫ z) hL))
  have hη : ηY ≫ cO.hom = ηX ≫ F.map u :=
    properSerreGlobalSectionsComp_structureUnit b α β hβ
  have hk : k ≫ cL.hom = cO.hom ≫ F.map rb :=
    properSerreGlobalSectionsComp_naturality b α β hβ s
  calc
    _ = normalSurfaceFiniteEndEvaluation R
        (ηY ≫ normalSurfaceFiniteSectionSerreEquiv
          R ιY iY hY hYdim nY eY hfinY (H (s ≫ φY))) :=
      normalSurfaceFiniteSectionSerreEquiv_trace
        R ιY iY hY hYdim nY eY hfinY (H (s ≫ φY))
    _ = normalSurfaceFiniteEndEvaluation R (ηY ≫ k ≫ cL.hom ≫ F.map Ψ ≫ q) :=
      congrArg (fun z => normalSurfaceFiniteEndEvaluation R (ηY ≫ z)) hSection
    _ = _ := congrArg (normalSurfaceFiniteEndEvaluation R)
      (properSerre_unit_section_paste F u rb Ψ ηX ηY k cO.hom cL.hom q hη hk)

end AlgebraicGeometry.Scheme.Cohomology
