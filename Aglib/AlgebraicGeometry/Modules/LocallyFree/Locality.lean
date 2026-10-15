/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Aglib.AlgebraicGeometry.Modules.LocallyFree.Restriction
/-!
# Locality of finite local freeness

Finite bases on genuine open subschemes are transported to the corresponding
slice sites and their covers are composed. Consequently finite local freeness
is detected on any genuine open cover, without global projectivity assumptions.
-/
@[expose] public section


noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u v w w' t t'
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace

namespace AlgebraicGeometry.Scheme.Modules

section Presentation
variable {C : Type w} [Category.{w'} C] {J : GrothendieckTopology C}
  {R : Sheaf J RingCat.{u}} [HasSheafify J AddCommGrpCat.{u}]
  [J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  {D : Type t} [Category.{t'} D] {K : GrothendieckTopology D}
  {S : Sheaf K RingCat.{u}} [HasSheafify K AddCommGrpCat.{u}]
  [K.WEqualsLocallyBijective AddCommGrpCat.{u}]

/-- Transporting a presentation with a basis along an isomorphism preserves
its basis property. -/
theorem presentationOfIsIso_generators_isIso {M N : SheafOfModules.{u} R}
    (P : M.Presentation) (f : M ⟶ N) [IsIso f] (hP : IsIso P.generators.π) :
    IsIso (P.ofIsIso f).generators.π := by
  have := hP
  exact generatingSections_ofEpi_isIso P.generators f

/-- A colimit-preserving functor carrying units to units preserves the basis
property of a presentation. -/
theorem presentationMap_generators_isIso {M : SheafOfModules.{u} R}
    (P : M.Presentation)
    (F : SheafOfModules.{u} R ⥤ SheafOfModules.{u} S)
    [PreservesColimitsOfSize.{u, u} F]
    (η : SheafOfModules.unit S ≅ F.obj (SheafOfModules.unit R))
    (hP : IsIso P.generators.π) :
    IsIso (P.map F η).generators.π := by
  have := hP
  rw [SheafOfModules.Presentation.map_π_eq]
  infer_instance

end Presentation

section BasisTransport
variable {C : Type w} [Category.{w'} C] {J : GrothendieckTopology C}
  {R : Sheaf J RingCat.{u}}
  [∀ U, HasSheafify (J.over U) AddCommGrpCat.{u}]
  [∀ U, (J.over U).WEqualsLocallyBijective AddCommGrpCat.{u}]

/-- Transport finite local bases along an isomorphism on an arbitrary site. -/
theorem finiteLocalBasis_of_sheafIso {M N : SheafOfModules.{u} R}
    (e : M ≅ N) (q : SheafOfModules.LocalGeneratorsData.{v} M)
    [hq : q.IsLocallyFreeData] [hf : q.IsFiniteType] :
    ∃ q' : SheafOfModules.LocalGeneratorsData.{v} N,
      q'.IsLocallyFreeData ∧ q'.IsFiniteType := by
  let q' : SheafOfModules.LocalGeneratorsData.{v} N :=
    { I := q.I
      X := q.X
      coversTop := q.coversTop
      generators i := (q.generators i).ofEpi
        ((SheafOfModules.overFunctor R (q.X i)).mapIso e).hom }
  refine ⟨q', ?_, ?_⟩
  · constructor
    intro i
    exact generatingSections_ofEpi_isIso (q.generators i)
      ((SheafOfModules.overFunctor R (q.X i)).mapIso e).hom
  · constructor
    intro i
    constructor
    exact (hf.isFiniteType i).finite

end BasisTransport

section BasisBinding
variable {C : Type w} [Category.{w'} C] {J : GrothendieckTopology C}
  {R : Sheaf J RingCat.{u}}
  [∀ U, HasSheafify (J.over U) AddCommGrpCat.{u}]
  [∀ U, (J.over U).WEqualsLocallyBijective AddCommGrpCat.{u}]
  [∀ U V, HasSheafify ((J.over U).over V) AddCommGrpCat.{u}]
  [∀ U V, ((J.over U).over V).WEqualsLocallyBijective AddCommGrpCat.{u}]

/-- Compose a cover with finite local bases on its slice sites. -/
theorem finiteLocalBasis_bind (M : SheafOfModules.{u} R) {ι : Type u}
    (U : ι → C) (hU : J.CoversTop U)
    (q : ∀ i, SheafOfModules.LocalGeneratorsData.{u} (M.over (U i)))
    (hq : ∀ i, (q i).IsLocallyFreeData) (hf : ∀ i, (q i).IsFiniteType) :
    ∃ q' : SheafOfModules.LocalGeneratorsData.{u} M,
      q'.IsLocallyFreeData ∧ q'.IsFiniteType := by
  let (i : ι) : (q i).IsLocallyFreeData := hq i
  let (i : ι) : (q i).IsFiniteType := hf i
  let q' := SheafOfModules.QuasicoherentData.bind M U hU (fun i => (q i).quasiCoherentData)
  refine ⟨q'.localGeneratorsData, ?_, ?_⟩
  · constructor
    intro i
    dsimp only [q', SheafOfModules.QuasicoherentData.localGeneratorsData,
      SheafOfModules.QuasicoherentData.bind]
    apply presentationOfIsIso_generators_isIso
    apply presentationMap_generators_isIso
    exact (hq i.1).isIso i.2
  · constructor
    intro i
    constructor
    change Finite ((q i.1).generators i.2).I
    exact ((hf i.1).isFiniteType i.2).finite

end BasisBinding

/-- Finite local bases on an open subscheme give finite local bases on its
slice site. -/
theorem finiteLocalBasis_over_of_restrict {X : Scheme.{u}} (M : X.Modules)
    (U : X.Opens) [hM : IsFiniteLocallyFree U.toScheme (M.restrict U.ι)] :
    ∃ q : SheafOfModules.LocalGeneratorsData.{u} (M.over U),
      q.IsLocallyFreeData ∧ q.IsFiniteType := by
  let E := Scheme.Modules.overEquiv U
  let φ := (U.sheafRestrictSheafEquivOver.app X.ringCatSheaf).inv
  have := U.instIsDenseSubsiteOverSubtypeMemOverGrothendieckTopologyFunctorOverEquivalence
  have : U.overEquivalence.functor.IsContinuous
      ((Opens.grothendieckTopology X).over U) (Opens.grothendieckTopology U.toScheme) :=
    inferInstanceAs (U.overEquivalence.functor.IsContinuous
      ((Opens.grothendieckTopology X).over U) (Opens.grothendieckTopology U.carrier))
  have : Functor.PreservesOneHypercovers.{u} U.overEquivalence.functor
      ((Opens.grothendieckTopology X).over U) (Opens.grothendieckTopology U.toScheme) :=
    Functor.PreservesOneHypercovers.of_coverPreserving
      (CoverPreserving.of_isContinuous _ _ _)
  have hpost (A : Over U) :
      (Over.post (X := A) U.overEquivalence.functor).IsContinuous
        (((Opens.grothendieckTopology X).over U).over A)
        ((Opens.grothendieckTopology U.toScheme).over (U.overEquivalence.functor.obj A)) := by
    exact Functor.isContinuous_of_preservesOneHypercovers _ _ _
  obtain ⟨q, hq, hf⟩ := hM.exists_localBasis
  let hpost' : ∀ A : Over U,
      (Over.post (X := A) U.overEquivalence.functor).IsContinuous
        (((Opens.grothendieckTopology X).over U).over A)
        ((Opens.grothendieckTopology U.carrier).over (U.overEquivalence.functor.obj A)) := hpost
  let q' := pushforwardLocalBasis U.overEquivalence.functor φ
    (U.sheafOfModulesEquivOverInverseUnit X.ringCatSheaf) q
  have hq' : q'.IsLocallyFreeData :=
    pushforwardLocalBasis_isLocallyFreeData U.overEquivalence.functor φ
      (U.sheafOfModulesEquivOverInverseUnit X.ringCatSheaf) q
  have hf' : q'.IsFiniteType :=
    pushforwardLocalBasis_isFiniteType U.overEquivalence.functor φ
      (U.sheafOfModulesEquivOverInverseUnit X.ringCatSheaf) q
  let e : E.inverse.obj (M.restrict U.ι) ≅ M.over U :=
    (E.inverse.mapIso ((Scheme.Modules.overFunctorEquiv U).app M)).symm ≪≫
      (E.unitIso.app (M.over U)).symm
  exact finiteLocalBasis_of_sheafIso (R := X.ringCatSheaf.over U) e q'

/-- Finite local freeness is local on an arbitrary cover by open subsets. -/
theorem finiteLocallyFree_of_openCover {X : Scheme.{u}} (M : X.Modules)
    {ι : Type u} (U : ι → X.Opens) (hU : IsOpenCover U)
    (hM : ∀ i, IsFiniteLocallyFree (U i).toScheme (M.restrict (U i).ι)) :
    IsFiniteLocallyFree X M := by
  classical
  have h (i : ι) := @finiteLocalBasis_over_of_restrict _ M (U i) (hM i)
  choose q hq hf using h
  have hc : (Opens.grothendieckTopology X).CoversTop U :=
    (Opens.coversTop_iff X U).mpr hU
  exact ⟨finiteLocalBasis_bind (R := X.ringCatSheaf) M U hc q hq hf⟩

/-- Replace an open immersion by the inclusion of its actual open image. -/
theorem finiteLocallyFree_restrict_opensRange {Y X : Scheme.{u}} (M : X.Modules)
    (j : Y ⟶ X) [IsOpenImmersion j]
    [IsFiniteLocallyFree Y (M.restrict j)] :
    IsFiniteLocallyFree j.opensRange.toScheme (M.restrict j.opensRange.ι) := by
  have := finiteLocallyFree_restrict j.isoOpensRange.inv (M.restrict j)
  let e : (M.restrict j).restrict j.isoOpensRange.inv ≅ M.restrict j.opensRange.ι :=
    ((Scheme.Modules.restrictFunctorComp j.isoOpensRange.inv j).app M).symm ≪≫
      (Scheme.Modules.restrictFunctorCongr j.isoOpensRange_inv_comp).app M
  exact finiteLocallyFree_of_iso e

/-- Jointly surjective open immersions detect finite local freeness. The
index type of the cover need not be small relative to the scheme. -/
theorem finiteLocallyFree_of_openImmersionCover {X : Scheme.{u}} (M : X.Modules)
    {ι : Type v} (Y : ι → Scheme.{u}) (j : ∀ i, Y i ⟶ X)
    [∀ i, IsOpenImmersion (j i)]
    (hj : ∀ x : X, ∃ i, ∃ y : Y i, j i y = x)
    (hM : ∀ i, IsFiniteLocallyFree (Y i) (M.restrict (j i))) :
    IsFiniteLocallyFree X M := by
  classical
  choose index point heq using hj
  let U : X → X.Opens := fun x => (j (index x)).opensRange
  have hU : IsOpenCover U := by
    apply IsOpenCover.mk
    apply Opens.ext
    rw [Opens.coe_iSup]
    apply Set.eq_univ_of_forall
    intro x
    apply Set.mem_iUnion.mpr
    exact ⟨x, point x, heq x⟩
  apply finiteLocallyFree_of_openCover M U hU
  intro x
  have := hM (index x)
  exact finiteLocallyFree_restrict_opensRange M (j (index x))

/-- A genuine scheme-theoretic open cover detects finite local freeness. -/
theorem finiteLocallyFree_of_schemeOpenCover {X : Scheme.{u}} (M : X.Modules)
    (U : Scheme.OpenCover.{v} X)
    (hM : ∀ i, IsFiniteLocallyFree (U.X i) (M.restrict (U.f i))) :
    IsFiniteLocallyFree X M :=
  finiteLocallyFree_of_openImmersionCover M U.X U.f
    (fun x => ⟨U.idx x, U.covers x⟩) hM

/-- Finite local freeness is equivalent to finite local freeness on every
member of any specified genuine open cover. -/
theorem finiteLocallyFree_iff_schemeOpenCover {X : Scheme.{u}} (M : X.Modules)
    (U : Scheme.OpenCover.{v} X) :
    IsFiniteLocallyFree X M ↔
      ∀ i, IsFiniteLocallyFree (U.X i) (M.restrict (U.f i)) :=
  ⟨fun _ i => finiteLocallyFree_restrict (U.f i) M,
    finiteLocallyFree_of_schemeOpenCover M U⟩

/-- A jointly surjective family of actual affine open charts detects finite
local freeness. -/
theorem finiteLocallyFree_of_affineCharts {X : Scheme.{u}} (M : X.Modules)
    {ι : Type v} (R : ι → CommRingCat.{u}) (j : ∀ i, Spec (R i) ⟶ X)
    [∀ i, IsOpenImmersion (j i)]
    (hj : ∀ x : X, ∃ i, ∃ y : Spec (R i), j i y = x)
    (hM : ∀ i, IsFiniteLocallyFree (Spec (R i)) (M.restrict (j i))) :
    IsFiniteLocallyFree X M :=
  finiteLocallyFree_of_openImmersionCover M (fun i => Spec (R i)) j hj hM

end AlgebraicGeometry.Scheme.Modules
