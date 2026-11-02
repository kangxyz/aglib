/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Cohomology.Duality.Projective.Relative.NormalSurface.Cohomology.ProperTranspose
public import Aglib.AlgebraicGeometry.Cohomology.Duality.Projective.Relative.NormalSurface.Trace.Proper

/-!
# Original coefficient normalization through proper Serre transposition

A derived coefficient equation implies the ordinary canonical-trace equation
for the existing proper Serre transpose. The actual source stays unchanged.
Only the source and upstairs transpose input are coherent; the intermediate
parent coefficient module need not be coherent. Neither global sections,
bidual evaluation nor a general derived single unit is canceled.
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry
open AlgebraicGeometry.ProjectiveSpace AlgebraicGeometry.Scheme.Modules
open AlgebraicGeometry.Scheme.Modules.QuasiCoherent

universe u

namespace AlgebraicGeometry.Scheme.Cohomology

attribute [local instance] AlgebraicGeometry.Scheme.Modules.standardHasDerivedCategory
local instance properTransposeCoefficientModuleDerived (R : Type u) [CommRing R] :
    HasDerivedCategory.{u + 1} (ModuleCat.{u} R) := HasDerivedCategory.standard _

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

/-- A proved original derived coefficient equation gives the ordinary trace
normalization of the same Serre transpose. No coherence is required of LX. -/
theorem normalSurfaceProperSerreTranspose_coefficient
    (MX LX : X.Modules) (LY : Y.Modules)
    [MX.IsQuasicoherent] (hMX : affineLocallyFiniteType X MX)
    [LY.IsQuasicoherent] (hLY : affineLocallyFiniteType Y LY)
    (C : MX ⟶ (pushforward b).obj LY) (φ : MX ⟶ LX)
    (Ψ : (derivedPushforwardPlus b).obj
        ((DerivedCategory.Plus.singleFunctor Y.Modules 0).obj LY) ⟶
      (DerivedCategory.Plus.singleFunctor X.Modules 0).obj LX)
    (h : (DerivedCategory.Plus.singleFunctor X.Modules 0).map C ≫
        (pushforward b).rightDerivedSingleUnit LY ≫ Ψ =
      (DerivedCategory.Plus.singleFunctor X.Modules 0).map φ)
    (ΦX : LX ⟶ normalSurfaceCanonicalModule R ιX iX nX) :
    C ≫ (pushforward b).map
        (normalSurfaceProperSerreTranspose R ιX ιY b iX iY hb
          hX hXdim hY hYdim nX nY eX eY hfinX hfinY LX LY hLY Ψ ΦX) ≫
      normalSurfaceProperCanonicalTrace R ιX ιY b iX iY hb
        hX hXdim hY hYdim nX nY eX eY hfinX hfinY = φ ≫ ΦX := by
  let α := chosenEmbeddingBaseScalar R iX (toSpec R ιX)
  let β := chosenEmbeddingBaseScalar R iY (toSpec R ιY)
  let hβ := normalSurfaceFiniteEmbeddingScalar b iX iY hb
  let H := pushforward b
  let SX := DerivedCategory.Plus.singleFunctor X.Modules 0
  let SY := DerivedCategory.Plus.singleFunctor Y.Modules 0
  let F := (moduleGlobalSectionsFunctorOfHom X α).rightDerivedFunctorPlus
  let G := (moduleGlobalSectionsFunctorOfHom Y β).rightDerivedFunctorPlus
  let ωY : Y.Modules := normalSurfaceCanonicalModule R ιY iY nY
  let ΦY : LY ⟶ ωY := normalSurfaceProperSerreTranspose R ιX ιY b iX iY hb
    hX hXdim hY hYdim nX nY eX eY hfinX hfinY LX LY hLY Ψ ΦX
  let cL := properSerreGlobalSectionsComp b α β hβ LY
  let cW := properSerreGlobalSectionsComp b α β hβ ωY
  let m : (derivedPushforwardPlus b).obj (SY.obj LY) ⟶
      (derivedPushforwardPlus b).obj (SY.obj ωY) :=
    (derivedPushforwardPlus b).map (SY.map ΦY)
  let d : SX.obj MX ⟶ (derivedPushforwardPlus b).obj (SY.obj LY) :=
    SX.map C ≫ H.rightDerivedSingleUnit LY
  let q := normalSurfaceFiniteCoherentSerreMap R ιX iX hX hXdim nX eX hfinX LX ΦX
  let τY := normalSurfaceFiniteCoherentSerreMap R ιY iY hY hYdim nY eY hfinY ωY (𝟙 ωY)
  let EY := normalSurfaceFiniteCoherentSerreMap R ιY iY hY hYdim nY eY hfinY LY
  have hs : SX.map (C ≫ H.map ΦY) ≫ H.rightDerivedSingleUnit ωY = d ≫ m := by
    dsimp only [d, m]
    rw [SX.map_comp, Category.assoc, H.rightDerivedSingleUnit_naturality]
    exact (Category.assoc _ _ _).symm
  have hc : F.map m ≫ cW.inv = cL.inv ≫ G.map (SY.map ΦY) := by
    have hn := properSerreGlobalSectionsComp_naturality b α β hβ ΦY
    change G.map (SY.map ΦY) ≫ cW.hom = cL.hom ≫ F.map m at hn
    apply (cancel_epi cL.hom).mp
    erw [Iso.hom_inv_id_assoc, ← Category.assoc, ← hn,
      Category.assoc, Iso.hom_inv_id, Category.comp_id]
  have he : EY ΦY = G.map (SY.map ΦY) ≫ τY := by
    simpa only [Category.comp_id] using
      normalSurfaceFiniteCoherentSerreMap_precomp R ιY iY hY hYdim nY eY hfinY ΦY (𝟙 ωY)
  have ht : EY ΦY = cL.hom ≫ F.map Ψ ≫ q :=
    normalSurfaceProperSerreTranspose_normalization R ιX ιY b iX iY hb
      hX hXdim hY hYdim nX nY eX eY hfinX hfinY LX LY hLY Ψ ΦX
  have hf : normalSurfaceProperTraceFunctional R ιX ιY b iX iY hb
      hY hYdim nY eY hfinY (C ≫ H.map ΦY) = F.map d ≫ F.map Ψ ≫ q := by
    have hsm : F.map (SX.map (C ≫ H.map ΦY) ≫ H.rightDerivedSingleUnit ωY) =
        F.map (d ≫ m) :=
      congrArg (fun z : SX.obj MX ⟶ (derivedPushforwardPlus b).obj (SY.obj ωY) =>
        F.map z) hs
    calc
      _ = F.map (d ≫ m) ≫ cW.inv ≫ τY :=
        congrArg (fun z : F.obj (SX.obj MX) ⟶
          F.obj ((derivedPushforwardPlus b).obj (SY.obj ωY)) => z ≫ cW.inv ≫ τY) hsm
      _ = (F.map d ≫ F.map m) ≫ cW.inv ≫ τY :=
        congrArg (fun z : F.obj (SX.obj MX) ⟶
          F.obj ((derivedPushforwardPlus b).obj (SY.obj ωY)) => z ≫ cW.inv ≫ τY)
          (F.map_comp d m)
      _ = F.map d ≫ (F.map m ≫ cW.inv) ≫ τY := by simp only [Category.assoc]
      _ = F.map d ≫ (cL.inv ≫ G.map (SY.map ΦY)) ≫ τY :=
        congrArg (fun z => F.map d ≫ z ≫ τY) hc
      _ = F.map d ≫ cL.inv ≫ EY ΦY := by rw [he]; simp only [Category.assoc]
      _ = F.map d ≫ cL.inv ≫ (cL.hom ≫ F.map Ψ ≫ q) :=
        congrArg (fun z => F.map d ≫ cL.inv ≫ z) ht
      _ = _ := by simp only [Iso.inv_hom_id_assoc]
  have hh : d ≫ Ψ = SX.map φ :=
    (Category.assoc (SX.map C) (H.rightDerivedSingleUnit LY) Ψ).trans h
  have hp : F.map d ≫ F.map Ψ ≫ q =
      normalSurfaceFiniteCoherentSerreMap R ιX iX hX hXdim nX eX hfinX MX (φ ≫ ΦX) := by
    calc
      _ = (F.map d ≫ F.map Ψ) ≫ q := (Category.assoc _ _ _).symm
      _ = F.map (d ≫ Ψ) ≫ q :=
        congrArg (fun z : F.obj (SX.obj MX) ⟶ F.obj (SX.obj LX) => z ≫ q)
          (F.map_comp d Ψ).symm
      _ = F.map (SX.map φ) ≫ q :=
        congrArg (fun z : SX.obj MX ⟶ SX.obj LX => F.map z ≫ q) hh
      _ = _ := (normalSurfaceFiniteCoherentSerreMap_precomp
        R ιX iX hX hXdim nX eX hfinX φ ΦX).symm
  have hsource : normalSurfaceFiniteCoherentSerreMap R ιX iX hX hXdim nX eX hfinX MX
        ((C ≫ H.map ΦY) ≫ normalSurfaceProperCanonicalTrace R ιX ιY b iX iY hb
          hX hXdim hY hYdim nX nY eX eY hfinX hfinY) =
      normalSurfaceFiniteCoherentSerreMap R ιX iX hX hXdim nX eX hfinX MX (φ ≫ ΦX) :=
    (normalSurfaceProperCanonicalTrace_source R ιX ιY b iX iY hb
      hX hXdim hY hYdim nX nY eX eY hfinX hfinY (C ≫ H.map ΦY)).trans (hf.trans hp)
  have hassoc : (C ≫ H.map ΦY) ≫ normalSurfaceProperCanonicalTrace R ιX ιY b iX iY hb
        hX hXdim hY hYdim nX nY eX eY hfinX hfinY =
      C ≫ H.map ΦY ≫ normalSurfaceProperCanonicalTrace R ιX ιY b iX iY hb
        hX hXdim hY hYdim nX nY eX eY hfinX hfinY := Category.assoc _ _ _
  exact (normalSurfaceFiniteCoherentSerreMap_bijective
    R ιX iX hX hXdim nX eX hfinX MX hMX).1
      ((congrArg (normalSurfaceFiniteCoherentSerreMap R ιX iX hX hXdim nX eX hfinX MX)
        hassoc).symm.trans hsource)

end AlgebraicGeometry.Scheme.Cohomology
