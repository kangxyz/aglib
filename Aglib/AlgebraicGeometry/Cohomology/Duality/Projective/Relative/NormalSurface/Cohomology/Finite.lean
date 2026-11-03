/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Cohomology.Duality.Projective.Relative.NormalSurface.Cohomology.UnitTrace
public import Aglib.AlgebraicGeometry.Cohomology.DirectImage.Affine.GlobalSections
public import Aglib.AlgebraicGeometry.Cohomology.Duality.Projective.Relative.ClosedEmbedding.Linear
public import Aglib.AlgebraicGeometry.Modules.QuasiCoherent.FiniteType.Locality

/-!
# Degree-zero finite-cover Serre comparison with the original units

The original coherent-source Serre maps for actual chosen embeddings and ordinary
affine direct image identify finite-cover canonical Hom with upstairs canonical
sections. Their native source, structural-unit and trace equations retain the
actual coefficient factorization through its map to the canonical module.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian AlgebraicGeometry
open AlgebraicGeometry.ProjectiveSpace AlgebraicGeometry.Scheme.Modules
open AlgebraicGeometry.Scheme.Modules.QuasiCoherent
open Opposite HomologicalComplex

universe u

private theorem normalSurfaceFinite_postcompose_iso_bijective
    {C : Type*} [Category* C] {X Y Z : C} (e : Y ≅ Z) :
    Function.Bijective (fun f : X ⟶ Y => f ≫ e.hom) := by
  constructor
  · intro f g h
    exact (cancel_mono e.hom).mp h
  · intro f
    refine ⟨f ≫ e.inv, ?_⟩
    change (f ≫ e.inv) ≫ e.hom = f
    rw [Category.assoc, e.inv_hom_id, Category.comp_id]

private theorem normalSurfaceFinite_precompose_iso_bijective
    {C : Type*} [Category* C] {X Y Z : C} (e : X ≅ Y) :
    Function.Bijective (fun f : Y ⟶ Z => e.hom ≫ f) := by
  constructor
  · intro f g h
    exact (cancel_epi e.hom).mp h
  · intro f
    refine ⟨e.inv ≫ f, ?_⟩
    change e.hom ≫ e.inv ≫ f = f
    rw [Iso.hom_inv_id_assoc]

private theorem normalSurfaceFinite_preimage_bijective
    {C D : Type*} [Category* C] [Category* D]
    (F : C ⥤ D) [F.Full] [F.Faithful] (X Y : C) :
    Function.Bijective (F.preimage (X := X) (Y := Y)) := by
  constructor
  · intro f g h
    exact (F.map_preimage f).symm.trans ((congrArg F.map h).trans (F.map_preimage g))
  · intro f
    exact ⟨F.map f, F.preimage_map f⟩

private theorem normalSurfaceFinite_map_bijective_targetIso
    {C D : Type*} [Category* C] [Category* D]
    (F : C ⥤ D) {X Y Z : C} (e : Y ≅ Z)
    (h : Function.Bijective (F.map (X := X) (Y := Y))) :
    Function.Bijective (F.map (X := X) (Y := Z)) := by
  constructor
  · intro f g hfg
    apply (cancel_mono e.inv).mp
    apply h.1
    rw [F.map_comp, F.map_comp, hfg]
  · intro f
    obtain ⟨g, hg⟩ := h.2 (f ≫ F.map e.inv)
    refine ⟨g ≫ e.hom, ?_⟩
    rw [F.map_comp, hg]
    let t := F.mapIso e
    change (f ≫ t.inv) ≫ t.hom = f
    rw [Category.assoc, t.inv_hom_id, Category.comp_id]

private theorem normalSurfaceFinite_map_bijective_natIso
    {C D : Type*} [Category* C] [Category* D] {F G : C ⥤ D}
    (e : F ≅ G) (M N : C)
    (h : Function.Bijective (G.map (X := M) (Y := N))) :
    Function.Bijective (F.map (X := M) (Y := N)) := by
  let E := Iso.homCongr (e.app M) (e.app N)
  have he : E ∘ (F.map (X := M) (Y := N)) = G.map := by
    funext f
    change e.inv.app M ≫ F.map f ≫ e.hom.app N = G.map f
    rw [e.hom.naturality, Iso.inv_hom_id_app_assoc]
  exact (Equiv.comp_bijective _ E).mp (he ▸ h)

private theorem normalSurfaceFinite_preimage_source
    {C D : Type*} [Category* C] [Category* D]
    (F : C ⥤ D) [F.Full] [F.Faithful]
    {K K' L : C} (m : K ⟶ K')
    (q : F.obj K ⟶ F.obj L) (q' : F.obj K' ⟶ F.obj L)
    (h : q = F.map m ≫ q') :
    F.preimage q = m ≫ F.preimage q' := by
  apply F.map_injective
  rw [F.map_preimage, F.map_comp, F.map_preimage]
  exact h

private theorem normalSurfaceFinite_mapped_source
    {C D : Type*} [Category* C] [Category* D]
    (F : C ⥤ D) {K K' L : C} {S S' T : D}
    (m : K ⟶ K') (q : K ⟶ L) (q' : K' ⟶ L)
    (c : S ⟶ F.obj K) (c' : S' ⟶ F.obj K') (d : F.obj L ⟶ T)
    (a : S ⟶ S') (hq : q = m ≫ q') (hc : a ≫ c' = c ≫ F.map m) :
    c ≫ F.map q ≫ d = a ≫ c' ≫ F.map q' ≫ d := by
  rw [hq, F.map_comp]
  simpa only [Category.assoc] using
    congrArg (fun k => k ≫ F.map q' ≫ d) hc.symm

namespace AlgebraicGeometry.Scheme.Cohomology

attribute [local instance] AlgebraicGeometry.Scheme.Modules.standardHasDerivedCategory
/-- The standard derived-category instance for modules over the original coefficient ring. -/
local instance normalSurfaceFiniteModuleDerived (A : Type u) [CommRing A] :
    HasDerivedCategory.{u + 1} (ModuleCat.{u} A) := HasDerivedCategory.standard _

local instance normalSurfaceFiniteStructureUnitQuasicoherent (Z : Scheme.{u}) :
    (normalSurfaceUnit Z).IsQuasicoherent := isQuasicoherent_unit Z

/-- The original unit/section equivalence with its native module Hom fixed first. -/
def normalSurfaceFiniteUnitHomSections (Z : Scheme.{u}) (N : Z.Modules) :
    (@Quiver.Hom Z.Modules _ (normalSurfaceUnit Z) N) ≃+ Γ(N, ⊤) :=
  unitHomGlobalSectionsAddEquiv Z N

/-- The native finite presentation of the structure module supplies its finite-type predicate. -/
theorem normalSurfaceFiniteUnit_finiteType (Z : Scheme.{u}) :
    affineLocallyFiniteType Z (normalSurfaceUnit Z) := by
  let : (normalSurfaceUnit Z).IsFinitePresentation := normalSurfaceUnit_isFinitePresentation Z
  exact affineLocallyFiniteType_of_finitePresentation (normalSurfaceUnit Z)

/-- The native module-valued derived sections of the specified ordinary module. -/
abbrev normalSurfaceFiniteSectionsObject {A : Type u} [CommRing A]
    (X : Scheme.{u}) (α : A →+* Γ(X, ⊤)) (M : X.Modules) :=
  (moduleGlobalSectionsFunctorOfHom X α).rightDerivedFunctorPlus.obj
    ((DerivedCategory.Plus.singleFunctor X.Modules 0).obj M)

/-- The actual affine comparison carries the original structure unit through the
ordinary structure-module coefficient arrow. -/
theorem normalSurfaceFiniteAffine_structureUnit
    {A : Type u} [CommRing A] {X Y : Scheme.{u}}
    (π : Y ⟶ X) [IsAffineHom π] (α : A →+* Γ(X, ⊤)) :
    moduleDerivedStructureUnit X α ≫
        (moduleGlobalSectionsFunctorOfHom X α).rightDerivedFunctorPlus.map
          ((DerivedCategory.Plus.singleFunctor X.Modules 0).map
            (SheafOfModules.unitToPushforwardObjUnit π.toRingCatSheafHom)) ≫
        (moduleDerivedGlobalSectionsAffineSingleIso π α
          (normalSurfaceUnit Y)).hom =
      moduleDerivedStructureUnit Y (π.appTop.hom.comp α) := by
  let OX : X.Modules := normalSurfaceUnit X
  let OY : Y.Modules := normalSurfaceUnit Y
  let : OY.IsQuasicoherent := isQuasicoherent_unit Y
  let FX := moduleGlobalSectionsFunctorOfHom X α
  let FY := moduleGlobalSectionsFunctorOfHom Y (π.appTop.hom.comp α)
  let SX := DerivedCategory.Plus.singleFunctor X.Modules 0
  let S := DerivedCategory.Plus.singleFunctor (ModuleCat.{u} A) 0
  let φ : OX ⟶ (pushforward π).obj OY :=
    SheafOfModules.unitToPushforwardObjUnit π.toRingCatSheafHom
  let C := moduleDerivedGlobalSectionsAffineSingleIso π α OY
  let E := modulePushforwardGlobalSectionsIso π α
  let a := moduleStructuralSectionsMap X α
  let b := FX.map φ ≫ E.hom.app OY
  let c := moduleStructuralSectionsMap Y (π.appTop.hom.comp α)
  let uX := FX.rightDerivedSingleUnit OX
  let uY := FY.rightDerivedSingleUnit OY
  let m := FX.rightDerivedFunctorPlus.map (SX.map φ)
  have hc : a ≫ b = c := by
    apply ConcreteCategory.hom_ext
    intro r
    rfl
  have hu : uX ≫ m ≫ C.hom = S.map b ≫ uY :=
    moduleDerivedGlobalSectionsAffineSingleIso_coefficientUnit π α φ
  change (S.map a ≫ uX) ≫ m ≫ C.hom = S.map c ≫ uY
  calc
    _ = S.map a ≫ (uX ≫ m ≫ C.hom) := by simp only [Category.assoc]
    _ = S.map a ≫ S.map b ≫ uY := congrArg (fun q => S.map a ≫ q) hu
    _ = S.map (a ≫ b) ≫ uY :=
      (Category.assoc (S.map a) (S.map b) uY).symm.trans
        (congrArg (fun q => q ≫ uY) (S.map_comp a b).symm)
    _ = _ := congrArg (fun q => S.map q ≫ uY) hc


/-- Bijectivity of the SAME native affine derived-sections map at an ordinary single target. -/
theorem normalSurfaceFinite_affineMap_bijective
    {R : Type u} [CommRing R] {Z : Scheme.{u}}
    (p : Z ⟶ Spec (.of R)) [QuasiCompact p] [QuasiSeparated p]
    (M : Z.Modules) [M.IsQuasicoherent] :
    let N : (Spec (.of R)).Modules := normalSurfaceUnit (Spec (.of R))
    let K := (derivedPushforwardPlus p).obj
      ((DerivedCategory.Plus.singleFunctor Z.Modules 0).obj M)
    let L := (DerivedCategory.Plus.singleFunctor (Spec (.of R)).Modules 0).obj N
    Function.Bijective
      ((moduleGlobalSectionsFunctorOfHom (Spec (.of R))
        (ΓSpecIso (.of R)).inv.hom).rightDerivedFunctorPlus.map (X := K) (Y := L)) := by
  let N : (Spec (.of R)).Modules := normalSurfaceUnit (Spec (.of R))
  let K := (derivedPushforwardPlus p).obj
    ((DerivedCategory.Plus.singleFunctor Z.Modules 0).obj M)
  let L := (DerivedCategory.Plus.singleFunctor (Spec (.of R)).Modules 0).obj N
  let F := moduleGlobalSectionsFunctorOfHom (Spec (.of R)) (ΓSpecIso (.of R)).inv.hom
  let G : (Spec (.of R)).Modules ⥤ ModuleCat.{u} R := moduleSpecΓFunctor
  let : G.Additive := moduleSpecΓFunctor_additive (.of R)
  let D : F.rightDerivedFunctorPlus ≅ G.rightDerivedFunctorPlus :=
    F.rightDerivedFunctorPlusIso (moduleAffineGlobalSectionsIso (.of R)).symm
  have hG : Function.Bijective
      (G.rightDerivedFunctorPlus.map (X := K) (Y := L⟦(0 : ℤ)⟧)) :=
    moduleSpecDerivedPushforwardSectionsHom_bijective p M N 0 0
  have hG₀ : Function.Bijective (G.rightDerivedFunctorPlus.map (X := K) (Y := L)) :=
    normalSurfaceFinite_map_bijective_targetIso G.rightDerivedFunctorPlus
      ((CategoryTheory.shiftFunctorZero
        (DerivedCategory.Plus (Spec (.of R)).Modules) ℤ).app L) hG
  exact normalSurfaceFinite_map_bijective_natIso D K L hG₀

section SingleEmbedding

/-- Evaluation of the actual native degree-zero scalar arrow at one. -/
def normalSurfaceFiniteEndEvaluation (R : Type u) [CommRing R]
    (f : (DerivedCategory.Plus.singleFunctor (ModuleCat.{u} R) 0).obj (ModuleCat.of R R) ⟶
      (DerivedCategory.Plus.singleFunctor (ModuleCat.{u} R) 0).obj (ModuleCat.of R R)) : R :=
  ((DerivedCategory.singleFunctor (ModuleCat.{u} R) 0).preimage
    (X := ModuleCat.of R R) (Y := ModuleCat.of R R) (DerivedCategory.Plus.ι.map f)) 1

variable (R : Type u) [CommRing R] [IsDomain R] [IsRegularLocalRing R]
    (ι : Type u) {X : Scheme.{u}} [IsIntegral X]
    (i : X ⟶ ProjectiveSpace R ι) [IsClosedImmersion i]
    [IsDominant (i ≫ toSpec R ι)]
    (hX : NormalStalks X) (hXdim : topologicalKrullDim X ≤ 2)
    (n : ℕ) (e : ι ≃ Fin (n + 1))
    (hfin : (genericImageBaseMap R ι i).Finite)

/-- Original coherent-module morphisms enter the actual concentration-normalized Serre source. -/
def normalSurfaceFiniteCanonicalInputEquiv (M : X.Modules) :
    (M ⟶ normalSurfaceCanonicalModule R ι i n) ≃+
      relativeClosedEmbeddingUnitTraceSource i (toSpec R ι) n
        (normalSurfaceUnit (Spec (.of R))) M :=
  (DerivedCategory.singleFunctor X.Modules 0).sectionsHomAddEquiv
    (AddEquiv.refl _) (normalSurfaceCanonicalShiftIso R ι i hX hXdim n e hfin)

/-- The original coherent-source degree-zero Serre map, followed by actual affine sections. -/
def normalSurfaceFiniteCoherentSerreMap (M : X.Modules) :
    (M ⟶ normalSurfaceCanonicalModule R ι i n) →+
      (normalSurfaceFiniteSectionsObject X (chosenEmbeddingBaseScalar R i (toSpec R ι)) M ⟶
        (DerivedCategory.Plus.singleFunctor (ModuleCat.{u} R) 0).obj (ModuleCat.of R R)) := by
  let S := DerivedCategory.Plus.singleFunctor X.Modules 0
  let N : (Spec (.of R)).Modules := normalSurfaceUnit (Spec (.of R))
  let K := (derivedPushforwardPlus (i ≫ toSpec R ι)).obj (S.obj M)
  let L := (DerivedCategory.Plus.singleFunctor (Spec (.of R)).Modules 0).obj N
  let E := normalSurfaceFiniteCanonicalInputEquiv R ι i hX hXdim n e hfin M
  let Φ := relativeClosedEmbeddingDegreeZeroSerreMap i (toSpec R ι) R ι
    (𝟙 _) (𝟙 _) (IsPullback.id_horiz (toSpec R ι)) n e N M
  let F := (moduleGlobalSectionsFunctorOfHom (Spec (.of R))
    (ΓSpecIso (.of R)).inv.hom).rightDerivedFunctorPlus
  let C := moduleDerivedGlobalSectionsPushforwardCompIso (i ≫ toSpec R ι)
    (ΓSpecIso (.of R)).inv.hom
  let T := affineDerivedStructureTargetIso (.of R)
  exact (Preadditive.leftComp _ (C.hom.app (S.obj M))).comp
    ((Preadditive.rightComp _ T.hom).comp
      ((F.mapAddHom (X := K) (Y := L)).comp
        ((DerivedCategory.Plus.ι.preimageAddHom K L).comp (Φ.comp E.toAddMonoidHom))))

/-- Its forward value keeps the original source, Serre arrow, affine map and target unit. -/
theorem normalSurfaceFiniteCoherentSerreMap_apply (M : X.Modules)
    (f : M ⟶ normalSurfaceCanonicalModule R ι i n) :
    let S := DerivedCategory.Plus.singleFunctor X.Modules 0
    let N : (Spec (.of R)).Modules := normalSurfaceUnit (Spec (.of R))
    let K := (derivedPushforwardPlus (i ≫ toSpec R ι)).obj (S.obj M)
    let L := (DerivedCategory.Plus.singleFunctor (Spec (.of R)).Modules 0).obj N
    let E := normalSurfaceFiniteCanonicalInputEquiv R ι i hX hXdim n e hfin M
    let Φ := relativeClosedEmbeddingDegreeZeroSerreMap i (toSpec R ι) R ι
      (𝟙 _) (𝟙 _) (IsPullback.id_horiz (toSpec R ι)) n e N M
    let F := (moduleGlobalSectionsFunctorOfHom (Spec (.of R))
      (ΓSpecIso (.of R)).inv.hom).rightDerivedFunctorPlus
    normalSurfaceFiniteCoherentSerreMap R ι i hX hXdim n e hfin M f =
      (moduleDerivedGlobalSectionsPushforwardCompIso (i ≫ toSpec R ι)
        (ΓSpecIso (.of R)).inv.hom).hom.app (S.obj M) ≫
        F.map (DerivedCategory.Plus.ι.preimage (X := K) (Y := L) (Φ (E f))) ≫
        (affineDerivedStructureTargetIso (.of R)).hom := rfl

/-- Coherence supplies bijectivity of this SAME original map. -/
theorem normalSurfaceFiniteCoherentSerreMap_bijective (M : X.Modules) [M.IsQuasicoherent]
    (hM : affineLocallyFiniteType X M) :
    Function.Bijective (normalSurfaceFiniteCoherentSerreMap R ι i hX hXdim n e hfin M) := by
  let : Fintype ι := Fintype.ofEquiv (Fin (n + 1)) e.symm
  let S := DerivedCategory.Plus.singleFunctor X.Modules 0
  let N : (Spec (.of R)).Modules := normalSurfaceUnit (Spec (.of R))
  let K := (derivedPushforwardPlus (i ≫ toSpec R ι)).obj (S.obj M)
  let L := (DerivedCategory.Plus.singleFunctor (Spec (.of R)).Modules 0).obj N
  let E := normalSurfaceFiniteCanonicalInputEquiv R ι i hX hXdim n e hfin M
  let Φ := relativeClosedEmbeddingDegreeZeroSerreMap i (toSpec R ι) R ι
    (𝟙 _) (𝟙 _) (IsPullback.id_horiz (toSpec R ι)) n e N M
  let F := (moduleGlobalSectionsFunctorOfHom (Spec (.of R))
    (ΓSpecIso (.of R)).inv.hom).rightDerivedFunctorPlus
  let C := (moduleDerivedGlobalSectionsPushforwardCompIso (i ≫ toSpec R ι)
    (ΓSpecIso (.of R)).inv.hom).app (S.obj M)
  let T := affineDerivedStructureTargetIso (.of R)
  have hΦ : Function.Bijective Φ :=
    (normalSurfaceFinite_postcompose_iso_bijective (relativeClosedEmbeddingTraceTargetIso n N)).comp
      (relativeClosedEmbeddingSerreMap_bijective i (toSpec R ι) R ι
        (𝟙 _) (𝟙 _) (IsPullback.id_horiz (toSpec R ι)) n e N M hM n)
  have hF : Function.Bijective (F.map (X := K) (Y := L)) :=
    normalSurfaceFinite_affineMap_bijective (i ≫ toSpec R ι) M
  change Function.Bijective (fun f =>
    C.hom ≫ F.map (DerivedCategory.Plus.ι.preimage (X := K) (Y := L) (Φ (E f))) ≫ T.hom)
  exact (normalSurfaceFinite_precompose_iso_bijective C).comp
    ((normalSurfaceFinite_postcompose_iso_bijective T).comp
      (hF.comp ((normalSurfaceFinite_preimage_bijective DerivedCategory.Plus.ι K L).comp
        (hΦ.comp E.bijective))))

/-- The native coherent-source H0 comparison, with its original forward map. -/
def normalSurfaceFiniteCoherentSerreAddEquiv (M : X.Modules) [M.IsQuasicoherent]
    (hM : affineLocallyFiniteType X M) :
    (M ⟶ normalSurfaceCanonicalModule R ι i n) ≃+
      (normalSurfaceFiniteSectionsObject X (chosenEmbeddingBaseScalar R i (toSpec R ι)) M ⟶
        (DerivedCategory.Plus.singleFunctor (ModuleCat.{u} R) 0).obj (ModuleCat.of R R)) :=
  AddEquiv.ofBijective (normalSurfaceFiniteCoherentSerreMap R ι i hX hXdim n e hfin M)
    (normalSurfaceFiniteCoherentSerreMap_bijective R ι i hX hXdim n e hfin M hM)

/-- Every original coefficient morphism is retained, including the actual finite-cover unit. -/
theorem normalSurfaceFiniteCoherentSerreMap_precomp
    {M M' : X.Modules} (m : M ⟶ M')
    (f : M' ⟶ normalSurfaceCanonicalModule R ι i n) :
    normalSurfaceFiniteCoherentSerreMap R ι i hX hXdim n e hfin M (m ≫ f) =
      (moduleGlobalSectionsFunctorOfHom X
        (chosenEmbeddingBaseScalar R i (toSpec R ι))).rightDerivedFunctorPlus.map
          ((DerivedCategory.Plus.singleFunctor X.Modules 0).map m) ≫
        normalSurfaceFiniteCoherentSerreMap R ι i hX hXdim n e hfin M' f := by
  let S := DerivedCategory.Plus.singleFunctor X.Modules 0
  let N : (Spec (.of R)).Modules := normalSurfaceUnit (Spec (.of R))
  let P := derivedPushforwardPlus (i ≫ toSpec R ι)
  let U : DerivedCategory.Plus (Spec (.of R)).Modules ⥤
      DerivedCategory (Spec (.of R)).Modules := DerivedCategory.Plus.ι
  let F := (moduleGlobalSectionsFunctorOfHom (Spec (.of R))
    (ΓSpecIso (.of R)).inv.hom).rightDerivedFunctorPlus
  let C := moduleDerivedGlobalSectionsPushforwardCompIso (i ≫ toSpec R ι)
    (ΓSpecIso (.of R)).inv.hom
  let T := affineDerivedStructureTargetIso (.of R)
  let L := (DerivedCategory.Plus.singleFunctor (Spec (.of R)).Modules 0).obj N
  let E := normalSurfaceFiniteCanonicalInputEquiv R ι i hX hXdim n e hfin M
  let E' := normalSurfaceFiniteCanonicalInputEquiv R ι i hX hXdim n e hfin M'
  let Φ := relativeClosedEmbeddingDegreeZeroSerreMap i (toSpec R ι) R ι
    (𝟙 _) (𝟙 _) (IsPullback.id_horiz (toSpec R ι)) n e N M
  let Φ' := relativeClosedEmbeddingDegreeZeroSerreMap i (toSpec R ι) R ι
    (𝟙 _) (𝟙 _) (IsPullback.id_horiz (toSpec R ι)) n e N M'
  have hin : E (m ≫ f) = (DerivedCategory.singleFunctor X.Modules 0).map m ≫ E' f := by
    change ((DerivedCategory.singleFunctor X.Modules 0).map (m ≫ f)) ≫
        (normalSurfaceCanonicalShiftIso R ι i hX hXdim n e hfin).inv =
      (DerivedCategory.singleFunctor X.Modules 0).map m ≫
        ((DerivedCategory.singleFunctor X.Modules 0).map f) ≫
        (normalSurfaceCanonicalShiftIso R ι i hX hXdim n e hfin).inv
    rw [Functor.map_comp, Category.assoc]
  let t := P.map (S.map m)
  have hΦ : Φ (E (m ≫ f)) = U.map t ≫ Φ' (E' f) :=
    (congrArg Φ hin).trans
      (relativeClosedEmbeddingDegreeZeroSerreMap_precomp i (toSpec R ι) R ι
        (𝟙 _) (𝟙 _) (IsPullback.id_horiz (toSpec R ι)) n e N m (E' f))
  have hp : U.preimage (X := P.obj (S.obj M)) (Y := L) (Φ (E (m ≫ f))) =
      t ≫ U.preimage (X := P.obj (S.obj M')) (Y := L) (Φ' (E' f)) :=
    normalSurfaceFinite_preimage_source U t _ _ hΦ
  have hc :
      (moduleGlobalSectionsFunctorOfHom X
        (chosenEmbeddingBaseScalar R i (toSpec R ι))).rightDerivedFunctorPlus.map (S.map m) ≫
          C.hom.app (S.obj M') = C.hom.app (S.obj M) ≫ F.map t :=
    C.hom.naturality (S.map m)
  exact normalSurfaceFinite_mapped_source F t _ _ (C.hom.app (S.obj M))
    (C.hom.app (S.obj M')) T.hom
    ((moduleGlobalSectionsFunctorOfHom X
      (chosenEmbeddingBaseScalar R i (toSpec R ι))).rightDerivedFunctorPlus.map (S.map m))
    hp hc

include hX hXdim e hfin in
/-- The structure-source case, with the original literal section coordinate. -/
def normalSurfaceFiniteSectionSerreEquiv :
    Γ(normalSurfaceCanonicalModule R ι i n, ⊤) ≃+
      (normalSurfaceFiniteSectionsObject X (chosenEmbeddingBaseScalar R i (toSpec R ι))
          (normalSurfaceUnit X) ⟶
        (DerivedCategory.Plus.singleFunctor (ModuleCat.{u} R) 0).obj (ModuleCat.of R R)) :=
  (normalSurfaceFiniteUnitHomSections X (normalSurfaceCanonicalModule R ι i n)).symm.trans
    (normalSurfaceFiniteCoherentSerreAddEquiv R ι i hX hXdim n e hfin
      (normalSurfaceUnit X) (normalSurfaceFiniteUnit_finiteType X))

/-- The structure-source specialization is the SAME old normalized Serre map. -/
theorem normalSurfaceFiniteSectionSerreEquiv_apply
    (s : Γ(normalSurfaceCanonicalModule R ι i n, ⊤)) :
    normalSurfaceFiniteSectionSerreEquiv R ι i hX hXdim n e hfin s =
      chosenEmbeddingModuleSerreMap R ι i (toSpec R ι) (𝟙 _)
        (IsPullback.id_horiz (toSpec R ι)) n e
        (normalSurfaceCanonicalSectionsAddEquiv R ι i hX hXdim n e hfin s) := rfl

/-- No new section map is introduced by the structure-source specialization. -/
theorem normalSurfaceFiniteSectionSerreEquiv_unitHom
    (f : (normalSurfaceUnit X : X.Modules) ⟶ normalSurfaceCanonicalModule R ι i n) :
    normalSurfaceFiniteSectionSerreEquiv R ι i hX hXdim n e hfin
        (normalSurfaceFiniteUnitHomSections X (normalSurfaceCanonicalModule R ι i n) f) =
      normalSurfaceFiniteCoherentSerreMap R ι i hX hXdim n e hfin (normalSurfaceUnit X) f := by
  let G := normalSurfaceFiniteUnitHomSections X (normalSurfaceCanonicalModule R ι i n)
  change normalSurfaceFiniteCoherentSerreMap R ι i hX hXdim n e hfin
    (normalSurfaceUnit X) (G.symm (G f)) = _
  rw [G.symm_apply_apply]

/-- The actual old trace is the original unit followed by this same comparison. -/
theorem normalSurfaceFiniteSectionSerreEquiv_trace
    (s : Γ(normalSurfaceCanonicalModule R ι i n, ⊤)) :
    normalSurfaceSectionsTraceBase R ι i hX hXdim n e hfin s =
      normalSurfaceFiniteEndEvaluation R
        (moduleDerivedStructureUnit X (chosenEmbeddingBaseScalar R i (toSpec R ι)) ≫
          normalSurfaceFiniteSectionSerreEquiv R ι i hX hXdim n e hfin s) := by
  exact congrArg (fun Φ => normalSurfaceFiniteEndEvaluation R
    (moduleDerivedStructureUnit X (chosenEmbeddingBaseScalar R i (toSpec R ι)) ≫ Φ))
      (normalSurfaceFiniteSectionSerreEquiv_apply R ι i hX hXdim n e hfin s).symm

end SingleEmbedding


/-- The actual affine comparison with scalar equality derived from a structural triangle. -/
def normalSurfaceFiniteAffineComparison
    {R : Type u} [CommRing R] {X Y : Scheme.{u}}
    (π : Y ⟶ X) [IsAffineHom π] (α : R →+* Γ(X, ⊤))
    (β : R →+* Γ(Y, ⊤)) (hβ : π.appTop.hom.comp α = β)
    (M : Y.Modules) [M.IsQuasicoherent] :
    normalSurfaceFiniteSectionsObject X α ((pushforward π).obj M) ≅
      normalSurfaceFiniteSectionsObject Y β M :=
  moduleDerivedGlobalSectionsAffineSingleIso π α M ≪≫
    eqToIso (congrArg (fun γ => normalSurfaceFiniteSectionsObject Y γ M) hβ)

/-- Scalar transport changes neither the original affine unit nor its coefficient map. -/
theorem normalSurfaceFiniteAffineComparison_unit
    {R : Type u} [CommRing R] {X Y : Scheme.{u}}
    (π : Y ⟶ X) [IsAffineHom π] (α : R →+* Γ(X, ⊤))
    (β : R →+* Γ(Y, ⊤)) (hβ : π.appTop.hom.comp α = β) :
    moduleDerivedStructureUnit X α ≫
        (moduleGlobalSectionsFunctorOfHom X α).rightDerivedFunctorPlus.map
          ((DerivedCategory.Plus.singleFunctor X.Modules 0).map
            (SheafOfModules.unitToPushforwardObjUnit π.toRingCatSheafHom)) ≫
        (normalSurfaceFiniteAffineComparison π α β hβ (normalSurfaceUnit Y)).hom =
      moduleDerivedStructureUnit Y β := by
  subst β
  simpa only [normalSurfaceFiniteAffineComparison, eqToIso_refl, Iso.trans_refl] using
    normalSurfaceFiniteAffine_structureUnit π α

/-- The same scalar transport retains every original coefficient morphism. -/
theorem normalSurfaceFiniteAffineComparison_naturality
    {R : Type u} [CommRing R] {X Y : Scheme.{u}}
    (π : Y ⟶ X) [IsAffineHom π] (α : R →+* Γ(X, ⊤))
    (β : R →+* Γ(Y, ⊤)) (hβ : π.appTop.hom.comp α = β)
    {M N : Y.Modules} [M.IsQuasicoherent] [N.IsQuasicoherent] (m : M ⟶ N) :
    (moduleGlobalSectionsFunctorOfHom X α).rightDerivedFunctorPlus.map
        ((DerivedCategory.Plus.singleFunctor X.Modules 0).map ((pushforward π).map m)) ≫
        (normalSurfaceFiniteAffineComparison π α β hβ N).hom =
      (normalSurfaceFiniteAffineComparison π α β hβ M).hom ≫
        (moduleGlobalSectionsFunctorOfHom Y β).rightDerivedFunctorPlus.map
          ((DerivedCategory.Plus.singleFunctor Y.Modules 0).map m) := by
  subst β
  simpa only [normalSurfaceFiniteAffineComparison, eqToIso_refl, Iso.trans_refl] using
    moduleDerivedGlobalSectionsAffineSingleIso_naturality π α m

/-- The actual commuting embedding triangle determines the scalar equality. -/
theorem normalSurfaceFiniteEmbeddingScalar
    {R : Type u} [CommRing R] {X Y : Scheme.{u}} (π : Y ⟶ X)
    {ιX ιY : Type u} (iX : X ⟶ ProjectiveSpace R ιX)
    (iY : Y ⟶ ProjectiveSpace R ιY)
    (hπ : iY ≫ toSpec R ιY = π ≫ (iX ≫ toSpec R ιX)) :
    π.appTop.hom.comp (chosenEmbeddingBaseScalar R iX (toSpec R ιX)) =
      chosenEmbeddingBaseScalar R iY (toSpec R ιY) := by
  ext r
  change π.appTop ((iX ≫ toSpec R ιX).appTop ((ΓSpecIso (.of R)).inv r)) =
    (iY ≫ toSpec R ιY).appTop ((ΓSpecIso (.of R)).inv r)
  rw [hπ, Scheme.Hom.comp_appTop]
  rfl

/-- Compose the two original Serre equivalences through the actual sections isomorphism. -/
def normalSurfaceFiniteSerreHomComparison
    {C : Type*} [Category* C] [Preadditive C]
    {L S : Type*} [AddCommGroup L] [AddCommGroup S] {U V W : C}
    (E : L ≃+ (U ⟶ W)) (G : S ≃+ (V ⟶ W)) (c : U ≅ V) : L ≃+ S :=
  E.trans ((Linear.homCongr ℤ c (Iso.refl W)).toAddEquiv.trans G.symm)

private theorem normalSurfaceFinite_homComparison_apply
    {C : Type*} [Category* C] [Preadditive C]
    {L S : Type*} [AddCommGroup L] [AddCommGroup S] {U V W : C}
    (E : L ≃+ (U ⟶ W)) (G : S ≃+ (V ⟶ W)) (c : U ≅ V) (f : L) :
    normalSurfaceFiniteSerreHomComparison E G c f = G.symm (c.inv ≫ E f) := by
  change G.symm ((c.inv ≫ E f) ≫ 𝟙 W) = _
  rw [Category.comp_id]

private theorem normalSurfaceFinite_homEquiv_normalization
    {C : Type*} [Category* C] [Preadditive C]
    {L S : Type*} [AddCommGroup L] [AddCommGroup S] {U V W : C}
    (E : L ≃+ (U ⟶ W)) (G : S ≃+ (V ⟶ W)) (c : U ≅ V) (f : L) :
    c.hom ≫ G
        (normalSurfaceFiniteSerreHomComparison E G c f) =
      E f := by
  change c.hom ≫ G (G.symm ((c.inv ≫ E f) ≫ 𝟙 W)) = E f
  rw [G.apply_symm_apply, Category.comp_id, Iso.hom_inv_id_assoc]

section FiniteCover

variable (R : Type u) [CommRing R] [IsDomain R] [IsRegularLocalRing R]
    (ιX ιY : Type u) {X Y : Scheme.{u}} [IsIntegral X] [IsIntegral Y]
    (π : Y ⟶ X) [IsFinite π]
    (iX : X ⟶ ProjectiveSpace R ιX) [IsClosedImmersion iX]
    [IsDominant (iX ≫ toSpec R ιX)]
    (iY : Y ⟶ ProjectiveSpace R ιY) [IsClosedImmersion iY]
    [IsDominant (iY ≫ toSpec R ιY)]
    (hπ : iY ≫ toSpec R ιY = π ≫ (iX ≫ toSpec R ιX))
    (hX : NormalStalks X) (hXdim : topologicalKrullDim X ≤ 2)
    (hY : NormalStalks Y) (hYdim : topologicalKrullDim Y ≤ 2)
    (nX nY : ℕ) (eX : ιX ≃ Fin (nX + 1)) (eY : ιY ≃ Fin (nY + 1))
    (hfinX : (genericImageBaseMap R ιX iX).Finite)
    (hfinY : (genericImageBaseMap R ιY iY).Finite)

include hπ hX hXdim hY hYdim eX eY hfinX hfinY

/-- Degree-zero finite-cover duality from the two ORIGINAL Serre maps and actual affine pi.
No finite exceptional inverse-image functor or canonical comparison is supplied. -/
def normalSurfaceFiniteCanonicalSectionsEquiv :
    ((pushforward π).obj (normalSurfaceUnit Y) ⟶
      normalSurfaceCanonicalModule R ιX iX nX) ≃+
        Γ(normalSurfaceCanonicalModule R ιY iY nY, ⊤) := by
  let F : X.Modules := (pushforward π).obj (normalSurfaceUnit Y)
  have hF : affineLocallyFiniteType X F :=
    Scheme.Modules.QuasiCoherent.FiniteMorphism.affineLocallyFiniteType_pushforward π
      (normalSurfaceFiniteUnit_finiteType Y)
  let : F.IsQuasicoherent := quasicoherent_of_affineLocallyFiniteType hF
  let α := chosenEmbeddingBaseScalar R iX (toSpec R ιX)
  let β := chosenEmbeddingBaseScalar R iY (toSpec R ιY)
  let c := normalSurfaceFiniteAffineComparison π α β
    (normalSurfaceFiniteEmbeddingScalar π iX iY hπ)
    (normalSurfaceUnit Y)
  let EX := normalSurfaceFiniteCoherentSerreAddEquiv R ιX iX hX hXdim nX eX hfinX F hF
  let EY := normalSurfaceFiniteSectionSerreEquiv R ιY iY hY hYdim nY eY hfinY
  exact normalSurfaceFiniteSerreHomComparison EX EY c

/-- The finite-cover comparison has the exact original Serre normalization. -/
theorem normalSurfaceFiniteCanonicalSectionsEquiv_normalization
    (f : (pushforward π).obj (normalSurfaceUnit Y) ⟶
      normalSurfaceCanonicalModule R ιX iX nX) :
    let α := chosenEmbeddingBaseScalar R iX (toSpec R ιX)
    let β := chosenEmbeddingBaseScalar R iY (toSpec R ιY)
    let c := normalSurfaceFiniteAffineComparison π α β
      (normalSurfaceFiniteEmbeddingScalar π iX iY hπ)
      (normalSurfaceUnit Y)
    c.hom ≫ normalSurfaceFiniteSectionSerreEquiv R ιY iY hY hYdim nY eY hfinY
        (normalSurfaceFiniteCanonicalSectionsEquiv R ιX ιY π iX iY hπ
          hX hXdim hY hYdim nX nY eX eY hfinX hfinY f) =
      normalSurfaceFiniteCoherentSerreMap R ιX iX hX hXdim nX eX hfinX
        ((pushforward π).obj (normalSurfaceUnit Y)) f := by
  let F : X.Modules := (pushforward π).obj (normalSurfaceUnit Y)
  have hF : affineLocallyFiniteType X F :=
    Scheme.Modules.QuasiCoherent.FiniteMorphism.affineLocallyFiniteType_pushforward π
      (normalSurfaceFiniteUnit_finiteType Y)
  let : F.IsQuasicoherent := quasicoherent_of_affineLocallyFiniteType hF
  let EX := normalSurfaceFiniteCoherentSerreAddEquiv R ιX iX hX hXdim nX eX hfinX F hF
  let EY := normalSurfaceFiniteSectionSerreEquiv R ιY iY hY hYdim nY eY hfinY
  let c := normalSurfaceFiniteAffineComparison π
    (chosenEmbeddingBaseScalar R iX (toSpec R ιX))
    (chosenEmbeddingBaseScalar R iY (toSpec R ιY))
    (normalSurfaceFiniteEmbeddingScalar π iX iY hπ) (normalSurfaceUnit Y)
  dsimp only [normalSurfaceFiniteCanonicalSectionsEquiv]
  rw [normalSurfaceFinite_homComparison_apply]
  erw [AddEquiv.apply_symm_apply, Iso.hom_inv_id_assoc]
  rfl

/-- The actual affine coefficient unit and original Serre source naturality give
the literal unit compatibility. No derived generic-uniqueness argument is used. -/
theorem normalSurfaceFiniteCanonicalSectionsEquiv_unit
    (f : (pushforward π).obj (normalSurfaceUnit Y) ⟶
      normalSurfaceCanonicalModule R ιX iX nX) :
    moduleDerivedStructureUnit Y (chosenEmbeddingBaseScalar R iY (toSpec R ιY)) ≫
        normalSurfaceFiniteSectionSerreEquiv R ιY iY hY hYdim nY eY hfinY
          (normalSurfaceFiniteCanonicalSectionsEquiv R ιX ιY π iX iY hπ
            hX hXdim hY hYdim nX nY eX eY hfinX hfinY f) =
      moduleDerivedStructureUnit X (chosenEmbeddingBaseScalar R iX (toSpec R ιX)) ≫
        normalSurfaceFiniteCoherentSerreMap R ιX iX hX hXdim nX eX hfinX (normalSurfaceUnit X)
          (SheafOfModules.unitToPushforwardObjUnit π.toRingCatSheafHom ≫ f) := by
  let α := chosenEmbeddingBaseScalar R iX (toSpec R ιX)
  let β := chosenEmbeddingBaseScalar R iY (toSpec R ιY)
  let c := normalSurfaceFiniteAffineComparison π α β
    (normalSurfaceFiniteEmbeddingScalar π iX iY hπ)
    (normalSurfaceUnit Y)
  let u : (normalSurfaceUnit X : X.Modules) ⟶ (pushforward π).obj (normalSurfaceUnit Y) :=
    SheafOfModules.unitToPushforwardObjUnit π.toRingCatSheafHom
  let m := (moduleGlobalSectionsFunctorOfHom X α).rightDerivedFunctorPlus.map
    ((DerivedCategory.Plus.singleFunctor X.Modules 0).map u)
  let a := moduleDerivedStructureUnit X α
  let b := moduleDerivedStructureUnit Y β
  let s := normalSurfaceFiniteCanonicalSectionsEquiv R ιX ιY π iX iY hπ
    hX hXdim hY hYdim nX nY eX eY hfinX hfinY f
  let Φ := normalSurfaceFiniteSectionSerreEquiv R ιY iY hY hYdim nY eY hfinY s
  let Ψ := normalSurfaceFiniteCoherentSerreMap R ιX iX hX hXdim nX eX hfinX
    ((pushforward π).obj (normalSurfaceUnit Y)) f
  have hu : a ≫ m ≫ c.hom = b :=
    normalSurfaceFiniteAffineComparison_unit π α β
      (normalSurfaceFiniteEmbeddingScalar π iX iY hπ)
  have hΦ : c.hom ≫ Φ = Ψ :=
    normalSurfaceFiniteCanonicalSectionsEquiv_normalization R ιX ιY π iX iY hπ
      hX hXdim hY hYdim nX nY eX eY hfinX hfinY f
  have hΨ : normalSurfaceFiniteCoherentSerreMap R ιX iX hX hXdim nX eX hfinX
      (normalSurfaceUnit X) (u ≫ f) = m ≫ Ψ :=
    normalSurfaceFiniteCoherentSerreMap_precomp R ιX iX hX hXdim nX eX hfinX u f
  calc
    b ≫ Φ = (a ≫ m ≫ c.hom) ≫ Φ := congrArg (fun z => z ≫ Φ) hu.symm
    _ = a ≫ m ≫ (c.hom ≫ Φ) :=
      (Category.assoc a (m ≫ c.hom) Φ).trans
        (congrArg (fun q => a ≫ q) (Category.assoc m c.hom Φ))
    _ = a ≫ m ≫ Ψ := congrArg (fun z => a ≫ m ≫ z) hΦ
    _ = _ := congrArg (fun z => a ≫ z) hΨ.symm

/-- Evaluation at the original finite-cover unit gives the exact original base trace. -/
theorem normalSurfaceFiniteCanonicalSectionsEquiv_trace
    (f : (pushforward π).obj (normalSurfaceUnit Y) ⟶
      normalSurfaceCanonicalModule R ιX iX nX) :
    normalSurfaceSectionsTraceBase R ιY iY hY hYdim nY eY hfinY
        (normalSurfaceFiniteCanonicalSectionsEquiv R ιX ιY π iX iY hπ
          hX hXdim hY hYdim nX nY eX eY hfinX hfinY f) =
      normalSurfaceSectionsTraceBase R ιX iX hX hXdim nX eX hfinX
        (normalSurfaceFiniteUnitHomSections X (normalSurfaceCanonicalModule R ιX iX nX)
          (SheafOfModules.unitToPushforwardObjUnit π.toRingCatSheafHom ≫ f)) := by
  let u : (normalSurfaceUnit X : X.Modules) ⟶ (pushforward π).obj (normalSurfaceUnit Y) :=
    SheafOfModules.unitToPushforwardObjUnit π.toRingCatSheafHom
  let s := normalSurfaceFiniteCanonicalSectionsEquiv R ιX ιY π iX iY hπ
    hX hXdim hY hYdim nX nY eX eY hfinX hfinY f
  let G := normalSurfaceFiniteUnitHomSections X (normalSurfaceCanonicalModule R ιX iX nX)
  let a := moduleDerivedStructureUnit X (chosenEmbeddingBaseScalar R iX (toSpec R ιX))
  calc
    _ = normalSurfaceFiniteEndEvaluation R
        (moduleDerivedStructureUnit Y (chosenEmbeddingBaseScalar R iY (toSpec R ιY)) ≫
          normalSurfaceFiniteSectionSerreEquiv R ιY iY hY hYdim nY eY hfinY s) :=
      normalSurfaceFiniteSectionSerreEquiv_trace R ιY iY hY hYdim nY eY hfinY s
    _ = normalSurfaceFiniteEndEvaluation R
        (a ≫ normalSurfaceFiniteCoherentSerreMap R ιX iX hX hXdim nX eX hfinX
          (normalSurfaceUnit X) (u ≫ f)) :=
      congrArg (normalSurfaceFiniteEndEvaluation R)
        (normalSurfaceFiniteCanonicalSectionsEquiv_unit R ιX ιY π iX iY hπ
          hX hXdim hY hYdim nX nY eX eY hfinX hfinY f)
    _ = normalSurfaceFiniteEndEvaluation R
        (a ≫ normalSurfaceFiniteSectionSerreEquiv R ιX iX hX hXdim nX eX hfinX (G (u ≫ f))) :=
      congrArg (fun z => normalSurfaceFiniteEndEvaluation R (a ≫ z))
        (normalSurfaceFiniteSectionSerreEquiv_unitHom R ιX iX hX hXdim nX eX hfinX (u ≫ f)).symm
    _ = _ := (normalSurfaceFiniteSectionSerreEquiv_trace
      R ιX iX hX hXdim nX eX hfinX (G (u ≫ f))).symm


/-- Original coefficient endomorphisms correspond to their ordinary source action on sections. -/
theorem normalSurfaceFiniteCanonicalSectionsEquiv_source
    (m : (normalSurfaceUnit Y : Y.Modules) ⟶ normalSurfaceUnit Y)
    (f : (pushforward π).obj (normalSurfaceUnit Y) ⟶
      normalSurfaceCanonicalModule R ιX iX nX) :
    normalSurfaceFiniteCanonicalSectionsEquiv R ιX ιY π iX iY hπ
        hX hXdim hY hYdim nX nY eX eY hfinX hfinY ((pushforward π).map m ≫ f) =
      normalSurfaceFiniteUnitHomSections Y (normalSurfaceCanonicalModule R ιY iY nY)
        (m ≫ (normalSurfaceFiniteUnitHomSections Y
          (normalSurfaceCanonicalModule R ιY iY nY)).symm
            (normalSurfaceFiniteCanonicalSectionsEquiv R ιX ιY π iX iY hπ
              hX hXdim hY hYdim nX nY eX eY hfinX hfinY f)) := by
  let α := chosenEmbeddingBaseScalar R iX (toSpec R ιX)
  let β := chosenEmbeddingBaseScalar R iY (toSpec R ιY)
  let c := normalSurfaceFiniteAffineComparison π α β
    (normalSurfaceFiniteEmbeddingScalar π iX iY hπ)
    (normalSurfaceUnit Y)
  let E := normalSurfaceFiniteCanonicalSectionsEquiv R ιX ιY π iX iY hπ
    hX hXdim hY hYdim nX nY eX eY hfinX hfinY
  let G := normalSurfaceFiniteUnitHomSections Y (normalSurfaceCanonicalModule R ιY iY nY)
  let EY := normalSurfaceFiniteSectionSerreEquiv R ιY iY hY hYdim nY eY hfinY
  let Φ := normalSurfaceFiniteCoherentSerreMap R ιX iX hX hXdim nX eX hfinX
    ((pushforward π).obj (normalSurfaceUnit Y))
  let ΦY := normalSurfaceFiniteCoherentSerreMap R ιY iY hY hYdim nY eY hfinY (normalSurfaceUnit Y)
  let s := E f
  let mX := (moduleGlobalSectionsFunctorOfHom X α).rightDerivedFunctorPlus.map
    ((DerivedCategory.Plus.singleFunctor X.Modules 0).map ((pushforward π).map m))
  let mY := (moduleGlobalSectionsFunctorOfHom Y β).rightDerivedFunctorPlus.map
    ((DerivedCategory.Plus.singleFunctor Y.Modules 0).map m)
  have hC : mX ≫ c.hom = c.hom ≫ mY :=
    normalSurfaceFiniteAffineComparison_naturality π α β
      (normalSurfaceFiniteEmbeddingScalar π iX iY hπ) m
  have hs : ΦY (G.symm s) = EY s :=
    (normalSurfaceFiniteSectionSerreEquiv_unitHom
      R ιY iY hY hYdim nY eY hfinY (G.symm s)).symm.trans
        (congrArg EY (G.apply_symm_apply s))
  have hYmap : EY (G (m ≫ G.symm s)) = mY ≫ EY s :=
    (normalSurfaceFiniteSectionSerreEquiv_unitHom
      R ιY iY hY hYdim nY eY hfinY (m ≫ G.symm s)).trans
        ((normalSurfaceFiniteCoherentSerreMap_precomp
          R ιY iY hY hYdim nY eY hfinY m (G.symm s)).trans
            (congrArg (fun q => mY ≫ q) hs))
  have hXmap : Φ ((pushforward π).map m ≫ f) = mX ≫ Φ f :=
    normalSurfaceFiniteCoherentSerreMap_precomp
      R ιX iX hX hXdim nX eX hfinX ((pushforward π).map m) f
  have hf : c.hom ≫ EY s = Φ f :=
    normalSurfaceFiniteCanonicalSectionsEquiv_normalization R ιX ιY π iX iY hπ
      hX hXdim hY hYdim nX nY eX eY hfinX hfinY f
  apply EY.injective
  apply (cancel_epi c.hom).mp
  calc
    _ = Φ ((pushforward π).map m ≫ f) :=
      normalSurfaceFiniteCanonicalSectionsEquiv_normalization R ιX ιY π iX iY hπ
        hX hXdim hY hYdim nX nY eX eY hfinX hfinY ((pushforward π).map m ≫ f)
    _ = mX ≫ Φ f := hXmap
    _ = mX ≫ (c.hom ≫ EY s) := congrArg (fun q => mX ≫ q) hf.symm
    _ = (mX ≫ c.hom) ≫ EY s := (Category.assoc _ _ _).symm
    _ = (c.hom ≫ mY) ≫ EY s := congrArg (fun q => q ≫ EY s) hC
    _ = c.hom ≫ (mY ≫ EY s) := Category.assoc _ _ _
    _ = _ := congrArg (fun q => c.hom ≫ q) hYmap.symm

/-- Pointwise source/unit evaluation is retained before any field or differential comparison. -/
theorem normalSurfaceFiniteCanonicalSectionsEquiv_trace_source
    (m : (normalSurfaceUnit Y : Y.Modules) ⟶ normalSurfaceUnit Y)
    (f : (pushforward π).obj (normalSurfaceUnit Y) ⟶
      normalSurfaceCanonicalModule R ιX iX nX) :
    normalSurfaceSectionsTraceBase R ιY iY hY hYdim nY eY hfinY
        (normalSurfaceFiniteUnitHomSections Y (normalSurfaceCanonicalModule R ιY iY nY)
          (m ≫ (normalSurfaceFiniteUnitHomSections Y
            (normalSurfaceCanonicalModule R ιY iY nY)).symm
              (normalSurfaceFiniteCanonicalSectionsEquiv R ιX ιY π iX iY hπ
                hX hXdim hY hYdim nX nY eX eY hfinX hfinY f))) =
      normalSurfaceSectionsTraceBase R ιX iX hX hXdim nX eX hfinX
        (normalSurfaceFiniteUnitHomSections X (normalSurfaceCanonicalModule R ιX iX nX)
          (SheafOfModules.unitToPushforwardObjUnit π.toRingCatSheafHom ≫
            ((pushforward π).map m ≫ f))) := by
  let ωY : Y.Modules := normalSurfaceCanonicalModule R ιY iY nY
  let G : (@Quiver.Hom Y.Modules _ (normalSurfaceUnit Y) ωY) ≃+ Γ(ωY, ⊤) :=
    normalSurfaceFiniteUnitHomSections Y ωY
  let E := normalSurfaceFiniteCanonicalSectionsEquiv R ιX ιY π iX iY hπ
    hX hXdim hY hYdim nX nY eX eY hfinX hfinY
  let t : Γ(ωY, ⊤) → R :=
    normalSurfaceSectionsTraceBase R ιY iY hY hYdim nY eY hfinY
  have hs : E ((pushforward π).map m ≫ f) = G (m ≫ G.symm (E f)) :=
    normalSurfaceFiniteCanonicalSectionsEquiv_source R ιX ιY π iX iY hπ
      hX hXdim hY hYdim nX nY eX eY hfinX hfinY m f
  exact (congrArg t hs).symm.trans
    (normalSurfaceFiniteCanonicalSectionsEquiv_trace R ιX ιY π iX iY hπ
      hX hXdim hY hYdim nX nY eX eY hfinX hfinY ((pushforward π).map m ≫ f))

/-- The ordinary coefficient line is retained as its own sheaf. Composing its actual
map to the canonical module is sufficient; no equality with that module is required. -/
theorem normalSurfaceFiniteCanonicalSectionsEquiv_trace_coefficient
    (L : X.Modules) (ψ : (pushforward π).obj (normalSurfaceUnit Y) ⟶ L)
    (φ : L ⟶ normalSurfaceCanonicalModule R ιX iX nX) :
    normalSurfaceSectionsTraceBase R ιY iY hY hYdim nY eY hfinY
        (normalSurfaceFiniteCanonicalSectionsEquiv R ιX ιY π iX iY hπ
          hX hXdim hY hYdim nX nY eX eY hfinX hfinY (ψ ≫ φ)) =
      normalSurfaceSectionsTraceBase R ιX iX hX hXdim nX eX hfinX
        (normalSurfaceFiniteUnitHomSections X (normalSurfaceCanonicalModule R ιX iX nX)
          ((SheafOfModules.unitToPushforwardObjUnit π.toRingCatSheafHom ≫ ψ) ≫ φ)) := by
  let O : X.Modules := normalSurfaceUnit X
  let ω : X.Modules := normalSurfaceCanonicalModule R ιX iX nX
  let u : O ⟶ (pushforward π).obj (normalSurfaceUnit Y) :=
    SheafOfModules.unitToPushforwardObjUnit π.toRingCatSheafHom
  let t : (@Quiver.Hom X.Modules _ O ω) → R := fun z =>
    normalSurfaceSectionsTraceBase R ιX iX hX hXdim nX eX hfinX
      (normalSurfaceFiniteUnitHomSections X ω z)
  have h := normalSurfaceFiniteCanonicalSectionsEquiv_trace R ιX ιY π iX iY hπ
    hX hXdim hY hYdim nX nY eX eY hfinX hfinY (ψ ≫ φ)
  exact h.trans (congrArg t (Category.assoc u ψ φ).symm)


/-- Finite canonical duality for an arbitrary actual coherent upstairs coefficient.
The forward map uses the same original Serre maps and affine comparison as the
structure-source specialization; no finite exceptional inverse image is supplied. -/
def normalSurfaceFiniteCanonicalHomEquiv (M : Y.Modules)
    (hM : affineLocallyFiniteType Y M) :
    ((pushforward π).obj M ⟶ normalSurfaceCanonicalModule R ιX iX nX) ≃+
      (M ⟶ normalSurfaceCanonicalModule R ιY iY nY) := by
  let : M.IsQuasicoherent := quasicoherent_of_affineLocallyFiniteType hM
  let F := (pushforward π).obj M
  have hF : affineLocallyFiniteType X F :=
    Scheme.Modules.QuasiCoherent.FiniteMorphism.affineLocallyFiniteType_pushforward π hM
  let : F.IsQuasicoherent := quasicoherent_of_affineLocallyFiniteType hF
  let c := normalSurfaceFiniteAffineComparison π
    (chosenEmbeddingBaseScalar R iX (toSpec R ιX))
    (chosenEmbeddingBaseScalar R iY (toSpec R ιY))
    (normalSurfaceFiniteEmbeddingScalar π iX iY hπ) M
  let EX := normalSurfaceFiniteCoherentSerreAddEquiv R ιX iX hX hXdim nX eX hfinX F hF
  let EY := normalSurfaceFiniteCoherentSerreAddEquiv R ιY iY hY hYdim nY eY hfinY M hM
  exact normalSurfaceFiniteSerreHomComparison EX EY c

/-- The full coherent-coefficient comparison is normalized by exactly the original
affine comparison and the two unchanged coherent Serre functionals. -/
theorem normalSurfaceFiniteCanonicalHomEquiv_normalization
    (M : Y.Modules) [M.IsQuasicoherent] (hM : affineLocallyFiniteType Y M)
    (f : (pushforward π).obj M ⟶ normalSurfaceCanonicalModule R ιX iX nX) :
    let c := normalSurfaceFiniteAffineComparison π
      (chosenEmbeddingBaseScalar R iX (toSpec R ιX))
      (chosenEmbeddingBaseScalar R iY (toSpec R ιY))
      (normalSurfaceFiniteEmbeddingScalar π iX iY hπ) M
    c.hom ≫ normalSurfaceFiniteCoherentSerreMap R ιY iY hY hYdim nY eY hfinY M
        (normalSurfaceFiniteCanonicalHomEquiv R ιX ιY π iX iY hπ
          hX hXdim hY hYdim nX nY eX eY hfinX hfinY M hM f) =
      normalSurfaceFiniteCoherentSerreMap R ιX iX hX hXdim nX eX hfinX
        ((pushforward π).obj M) f := by
  let F := (pushforward π).obj M
  have hF : affineLocallyFiniteType X F :=
    Scheme.Modules.QuasiCoherent.FiniteMorphism.affineLocallyFiniteType_pushforward π hM
  let : F.IsQuasicoherent := quasicoherent_of_affineLocallyFiniteType hF
  let EX := normalSurfaceFiniteCoherentSerreAddEquiv R ιX iX hX hXdim nX eX hfinX F hF
  let EY := normalSurfaceFiniteCoherentSerreAddEquiv R ιY iY hY hYdim nY eY hfinY M hM
  let c := normalSurfaceFiniteAffineComparison π
    (chosenEmbeddingBaseScalar R iX (toSpec R ιX))
    (chosenEmbeddingBaseScalar R iY (toSpec R ιY))
    (normalSurfaceFiniteEmbeddingScalar π iX iY hπ) M
  change c.hom ≫ EY
      (normalSurfaceFiniteCanonicalHomEquiv R ιX ιY π iX iY hπ
        hX hXdim hY hYdim nX nY eX eY hfinX hfinY M hM f) = EX f
  dsimp only [normalSurfaceFiniteCanonicalHomEquiv]
  rw [normalSurfaceFinite_homEquiv_normalization]

end FiniteCover

end AlgebraicGeometry.Scheme.Cohomology
