/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Aglib.AlgebraicGeometry.Modules.LocallyFree.Restriction
public import Aglib.Algebra.Category.ModuleCat.Sheaf.LocallyFree.Locality
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
  let q' := SheafOfModules.pushforwardLocalBasis U.overEquivalence.functor φ
    (U.sheafOfModulesEquivOverInverseUnit X.ringCatSheaf) q
  have hq' : q'.IsLocallyFreeData :=
    SheafOfModules.pushforwardLocalBasis_isLocallyFreeData U.overEquivalence.functor φ
      (U.sheafOfModulesEquivOverInverseUnit X.ringCatSheaf) q
  have hf' : q'.IsFiniteType :=
    SheafOfModules.pushforwardLocalBasis_isFiniteType U.overEquivalence.functor φ
      (U.sheafOfModulesEquivOverInverseUnit X.ringCatSheaf) q
  let e : E.inverse.obj (M.restrict U.ι) ≅ M.over U :=
    (E.inverse.mapIso ((Scheme.Modules.overFunctorEquiv U).app M)).symm ≪≫
      (E.unitIso.app (M.over U)).symm
  exact SheafOfModules.finiteLocalBasis_of_sheafIso (R := X.ringCatSheaf.over U) e q'

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
  exact ⟨SheafOfModules.finiteLocalBasis_bind (R := X.ringCatSheaf) M U hc q hq hf⟩

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
