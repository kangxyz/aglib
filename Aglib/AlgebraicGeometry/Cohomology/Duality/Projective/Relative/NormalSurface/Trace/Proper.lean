/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Cohomology.Duality.Projective.Relative.NormalSurface.Cohomology.ProperTranspose
public import Aglib.AlgebraicGeometry.Cohomology.DirectImage.Proper.Coherent

/-!
# The coherent-source ordinary proper canonical trace

The trace is constructed on the actual coherent direct image of the own-homology
canonical module. Its functional uses the original derived single unit and the
original global-sections composition, not a proper exceptional inverse image.
Coherent Serre injectivity proves the representing equation on every coherent
source; no faithfulness assertion about global sections is used.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian AlgebraicGeometry
open AlgebraicGeometry.ProjectiveSpace AlgebraicGeometry.Scheme.Modules
open AlgebraicGeometry.Scheme.Modules.QuasiCoherent

universe u

namespace AlgebraicGeometry.Scheme.Cohomology

attribute [local instance] AlgebraicGeometry.Scheme.Modules.standardHasDerivedCategory
/-- The standard derived-category instance for modules over the original coefficient ring. -/
local instance properCanonicalTraceModuleDerived (A : Type u) [CommRing A] :
    HasDerivedCategory.{u + 1} (ModuleCat.{u} A) := HasDerivedCategory.standard _

/-- Coherence of the actual canonical module, before any direct image. -/
theorem normalSurfaceCanonicalModule_finiteType
    (R : Type u) [CommRing R] [IsNoetherianRing R] (ι : Type u)
    {X : Scheme.{u}} (i : X ⟶ ProjectiveSpace R ι) [IsClosedImmersion i]
    (n : ℕ) (e : ι ≃ Fin (n + 1)) :
    affineLocallyFiniteType X (normalSurfaceCanonicalModule R ι i n) := by
  let : (normalSurfaceCanonicalModule R ι i n).IsFinitePresentation :=
    normalSurfaceHomology_finitePresentation R ι i n e (n : ℤ)
  exact affineLocallyFiniteType_of_finitePresentation _

/-- Proper finiteness applies to the actual canonical direct image. The target's
Noetherian condition is obtained from its given embedding over the same base. -/
theorem normalSurfaceProperCanonicalPushforward_finiteType
    (R : Type u) [CommRing R] [IsNoetherianRing R] (ιX ιY : Type u)
    {X Y : Scheme.{u}} (b : Y ⟶ X) [IsProper b]
    (iX : X ⟶ ProjectiveSpace R ιX) [IsClosedImmersion iX]
    (iY : Y ⟶ ProjectiveSpace R ιY) [IsClosedImmersion iY]
    (nX nY : ℕ) (eX : ιX ≃ Fin (nX + 1)) (eY : ιY ≃ Fin (nY + 1)) :
    affineLocallyFiniteType X
      ((pushforward b).obj (normalSurfaceCanonicalModule R ιY iY nY)) := by
  let : Finite ιX := Finite.of_equiv _ eX.symm
  let : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian iX
  exact (affineLocallyFiniteType X).prop_of_iso
    ((pushforward b).rightDerivedZeroIsoSelf.app _)
    (moduleHigherDirectImage_coherent_of_proper b _
      (normalSurfaceCanonicalModule_finiteType R ιY iY nY eY) 0)

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

/-- The original functional on an ordinary source arrow into the canonical direct
image. The comparison from the ordinary image to the derived image is the native
single unit; it is not assumed invertible. -/
def normalSurfaceProperTraceFunctional {M : X.Modules}
    (a : M ⟶ (pushforward b).obj (normalSurfaceCanonicalModule R ιY iY nY)) :
    normalSurfaceFiniteSectionsObject X (chosenEmbeddingBaseScalar R iX (toSpec R ιX)) M ⟶
      (DerivedCategory.Plus.singleFunctor (ModuleCat.{u} R) 0).obj (ModuleCat.of R R) :=
  (moduleGlobalSectionsFunctorOfHom X
      (chosenEmbeddingBaseScalar R iX (toSpec R ιX))).rightDerivedFunctorPlus.map
        ((DerivedCategory.Plus.singleFunctor X.Modules 0).map a ≫
          (pushforward b).rightDerivedSingleUnit (normalSurfaceCanonicalModule R ιY iY nY)) ≫
    (properSerreGlobalSectionsComp b
      (chosenEmbeddingBaseScalar R iX (toSpec R ιX))
      (chosenEmbeddingBaseScalar R iY (toSpec R ιY))
      (normalSurfaceFiniteEmbeddingScalar b iX iY hb)
      (normalSurfaceCanonicalModule R ιY iY nY)).inv ≫
    normalSurfaceFiniteCoherentSerreMap R ιY iY hY hYdim nY eY hfinY
      (normalSurfaceCanonicalModule R ιY iY nY) (𝟙 _)

omit [IsIntegral X] [IsClosedImmersion iX] [IsDominant (iX ≫ toSpec R ιX)] in
/-- Contravariant naturality holds before any Serre inverse is taken. -/
theorem normalSurfaceProperTraceFunctional_precomp {M N : X.Modules} (m : M ⟶ N)
    (a : N ⟶ (pushforward b).obj (normalSurfaceCanonicalModule R ιY iY nY)) :
    normalSurfaceProperTraceFunctional R ιX ιY b iX iY hb hY hYdim nY eY hfinY (m ≫ a) =
      (moduleGlobalSectionsFunctorOfHom X
        (chosenEmbeddingBaseScalar R iX (toSpec R ιX))).rightDerivedFunctorPlus.map
          ((DerivedCategory.Plus.singleFunctor X.Modules 0).map m) ≫
        normalSurfaceProperTraceFunctional R ιX ιY b iX iY hb hY hYdim nY eY hfinY a := by
  simp only [normalSurfaceProperTraceFunctional, Functor.map_comp, Category.assoc]

omit [IsIntegral X] [IsClosedImmersion iX] [IsDominant (iX ≫ toSpec R ιX)] in
/-- The source functional is exactly the transpose formed with the original
pullback unit and the original ordinary adjunction mate. In particular at the
identity source its mate is the original counit. -/
theorem normalSurfaceProperTraceFunctional_mate {M : X.Modules}
    (a : M ⟶ (pushforward b).obj (normalSurfaceCanonicalModule R ιY iY nY)) :
    let α := chosenEmbeddingBaseScalar R iX (toSpec R ιX)
    let β := chosenEmbeddingBaseScalar R iY (toSpec R ιY)
    let P := (Scheme.Modules.pullback b).obj M
    let k := ((pullbackPushforwardAdjunction b).homEquiv M
      (normalSurfaceCanonicalModule R ιY iY nY)).symm a
    normalSurfaceProperTraceFunctional R ιX ιY b iX iY hb hY hYdim nY eY hfinY a =
      (moduleGlobalSectionsFunctorOfHom X α).rightDerivedFunctorPlus.map
        ((DerivedCategory.Plus.singleFunctor X.Modules 0).map
          ((pullbackPushforwardAdjunction b).unit.app M) ≫
            (pushforward b).rightDerivedSingleUnit P) ≫
      (properSerreGlobalSectionsComp b α β
        (normalSurfaceFiniteEmbeddingScalar b iX iY hb) P).inv ≫
      normalSurfaceFiniteCoherentSerreMap R ιY iY hY hYdim nY eY hfinY P k := by
  let α := chosenEmbeddingBaseScalar R iX (toSpec R ιX)
  let β := chosenEmbeddingBaseScalar R iY (toSpec R ιY)
  let ω := normalSurfaceCanonicalModule R ιY iY nY
  let P := (Scheme.Modules.pullback b).obj M
  let A := pullbackPushforwardAdjunction b
  let k := (A.homEquiv M ω).symm a
  let SX := DerivedCategory.Plus.singleFunctor X.Modules 0
  let SY := DerivedCategory.Plus.singleFunctor Y.Modules 0
  let FX := (moduleGlobalSectionsFunctorOfHom X α).rightDerivedFunctorPlus
  let FY := (moduleGlobalSectionsFunctorOfHom Y β).rightDerivedFunctorPlus
  let G := pushforward b
  let CP := properSerreGlobalSectionsComp b α β
    (normalSurfaceFiniteEmbeddingScalar b iX iY hb) P
  let CW := properSerreGlobalSectionsComp b α β
    (normalSurfaceFiniteEmbeddingScalar b iX iY hb) ω
  have ha : A.unit.app M ≫ G.map k = a := by
    exact (A.homEquiv_unit M ω k).symm.trans ((A.homEquiv M ω).apply_symm_apply a)
  have hs : SX.map a ≫ G.rightDerivedSingleUnit ω =
      (SX.map (A.unit.app M) ≫ G.rightDerivedSingleUnit P) ≫
        (derivedPushforwardPlus b).map (SY.map k) := by
    rw [← ha, SX.map_comp, Category.assoc, G.rightDerivedSingleUnit_naturality]
    exact (Category.assoc _ _ _).symm
  have hc : FX.map ((derivedPushforwardPlus b).map (SY.map k)) ≫ CW.inv =
      CP.inv ≫ FY.map (SY.map k) := by
    have hn := properSerreGlobalSectionsComp_naturality b α β
      (normalSurfaceFiniteEmbeddingScalar b iX iY hb) k
    change FY.map (SY.map k) ≫ CW.hom =
      CP.hom ≫ FX.map ((derivedPushforwardPlus b).map (SY.map k)) at hn
    apply (cancel_epi CP.hom).mp
    erw [Iso.hom_inv_id_assoc, ← Category.assoc, ← hn,
      Category.assoc, Iso.hom_inv_id, Category.comp_id]
  have he : normalSurfaceFiniteCoherentSerreMap R ιY iY hY hYdim nY eY hfinY P k =
      FY.map (SY.map k) ≫
        normalSurfaceFiniteCoherentSerreMap R ιY iY hY hYdim nY eY hfinY ω (𝟙 ω) := by
    simpa only [Category.comp_id] using
      normalSurfaceFiniteCoherentSerreMap_precomp R ιY iY hY hYdim nY eY hfinY k (𝟙 ω)
  change FX.map (SX.map a ≫ G.rightDerivedSingleUnit ω) ≫ CW.inv ≫ _ =
    FX.map (SX.map (A.unit.app M) ≫ G.rightDerivedSingleUnit P) ≫ CP.inv ≫ _
  erw [hs, FX.map_comp, he]
  simp only [Category.assoc]
  erw [← Category.assoc (FX.map ((derivedPushforwardPlus b).map (SY.map k))), hc]
  simp only [Category.assoc]
  rfl

variable [IsProper b]

/-- The genuine ordinary canonical trace, evaluated on the identity of the actual
coherent direct image. All embedding and generic finiteness hypotheses are retained. -/
def normalSurfaceProperCanonicalTrace :
    (pushforward b).obj (normalSurfaceCanonicalModule R ιY iY nY) ⟶
      normalSurfaceCanonicalModule R ιX iX nX := by
  let F := (pushforward b).obj (normalSurfaceCanonicalModule R ιY iY nY)
  have hF : affineLocallyFiniteType X F :=
    normalSurfaceProperCanonicalPushforward_finiteType R ιX ιY b iX iY nX nY eX eY
  let : F.IsQuasicoherent := quasicoherent_of_affineLocallyFiniteType hF
  exact (normalSurfaceFiniteCoherentSerreAddEquiv R ιX iX hX hXdim nX eX hfinX F hF).symm
    (normalSurfaceProperTraceFunctional R ιX ιY b iX iY hb hY hYdim nY eY hfinY (𝟙 F))

/-- The trace has its original functional, by the inverse law of that same Serre map. -/
theorem normalSurfaceProperCanonicalTrace_normalization :
    normalSurfaceFiniteCoherentSerreMap R ιX iX hX hXdim nX eX hfinX
        ((pushforward b).obj (normalSurfaceCanonicalModule R ιY iY nY))
        (normalSurfaceProperCanonicalTrace R ιX ιY b iX iY hb hX hXdim hY hYdim
          nX nY eX eY hfinX hfinY) =
      normalSurfaceProperTraceFunctional R ιX ιY b iX iY hb hY hYdim nY eY hfinY (𝟙 _) := by
  let F := (pushforward b).obj (normalSurfaceCanonicalModule R ιY iY nY)
  have hF : affineLocallyFiniteType X F :=
    normalSurfaceProperCanonicalPushforward_finiteType R ιX ιY b iX iY nX nY eX eY
  let : F.IsQuasicoherent := quasicoherent_of_affineLocallyFiniteType hF
  dsimp only [normalSurfaceProperCanonicalTrace, normalSurfaceFiniteCoherentSerreAddEquiv]
  exact AddEquiv.ofBijective_apply_symm_apply _ _

/-- Every original source arrow has the expected functional. This is equality in
the actual derived category of base modules, not cancellation of global sections. -/
theorem normalSurfaceProperCanonicalTrace_source {M : X.Modules}
    (a : M ⟶ (pushforward b).obj (normalSurfaceCanonicalModule R ιY iY nY)) :
    normalSurfaceFiniteCoherentSerreMap R ιX iX hX hXdim nX eX hfinX M
        (a ≫ normalSurfaceProperCanonicalTrace R ιX ιY b iX iY hb hX hXdim hY hYdim
          nX nY eX eY hfinX hfinY) =
      normalSurfaceProperTraceFunctional R ιX ιY b iX iY hb hY hYdim nY eY hfinY a := by
  rw [normalSurfaceFiniteCoherentSerreMap_precomp,
    normalSurfaceProperCanonicalTrace_normalization]
  simpa only [Category.comp_id] using
    (normalSurfaceProperTraceFunctional_precomp R ιX ιY b iX iY hb hY hYdim
      nY eY hfinY a (𝟙 _)).symm

/-- Coherent Yoneda realization: taking the original Serre inverse on any coherent
source equals composition with the constructed sheaf trace. -/
theorem normalSurfaceProperCanonicalTrace_represents
    (M : X.Modules) [M.IsQuasicoherent] (hM : affineLocallyFiniteType X M)
    (a : M ⟶ (pushforward b).obj (normalSurfaceCanonicalModule R ιY iY nY)) :
    (normalSurfaceFiniteCoherentSerreAddEquiv R ιX iX hX hXdim nX eX hfinX M hM).symm
        (normalSurfaceProperTraceFunctional R ιX ιY b iX iY hb hY hYdim nY eY hfinY a) =
      a ≫ normalSurfaceProperCanonicalTrace R ιX ιY b iX iY hb hX hXdim hY hYdim
        nX nY eX eY hfinX hfinY := by
  let E := normalSurfaceFiniteCoherentSerreAddEquiv R ιX iX hX hXdim nX eX hfinX M hM
  apply E.injective
  exact (E.apply_symm_apply _).trans
    (normalSurfaceProperCanonicalTrace_source R ιX ιY b iX iY hb hX hXdim hY hYdim
      nX nY eX eY hfinX hfinY a).symm

end AlgebraicGeometry.Scheme.Cohomology
