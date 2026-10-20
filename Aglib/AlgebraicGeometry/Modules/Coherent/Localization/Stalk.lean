/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.CategoryTheory.Localization.SerreKernel
public import Aglib.Algebra.Category.ModuleCat.Localization.BaseChange
public import Aglib.AlgebraicGeometry.Modules.Coherent.Localization.Equivalence
public import Aglib.Algebra.Category.FGModuleCat.Localization.Quotient
public import Aglib.AlgebraicGeometry.Modules.Coherent.FlatPullback
public import Aglib.AlgebraicGeometry.Modules.QuasiCoherent.Affine.FiniteTypeComparison
public import Aglib.AlgebraicGeometry.Modules.QuasiCoherent.Affine.Pullback
public import Aglib.AlgebraicGeometry.Morphisms.Flat.AffineStalk

/-!
Native migration from `R5Lab.Aglib.AlgebraicGeometry.Modules.Coherent.Localization.Stalk` at R5
revision
`f8a3314ddecffcada2ec721d26d56a937bed9690`, SHA-256
`fd3f46288651c62842d6a59021070da27e6f54b1a5278c8724ff6298b720dc83`.
Original objects, maps, universes and explicit hypotheses are retained.
Native providers replace duplicate implementations.
-/

@[expose] public section

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open _root_.AlgebraicGeometry.Scheme.Modules.Coherent
  (coherentExactPullback coherentExactStructure coherentPullback coherentPullbackCompIso
      coherentRestrictionIsoPullback)
open _root_.AlgebraicGeometry.Scheme.Modules.QuasiCoherent
  (AffineQuasicoherent FiniteTypeSheaves affineFiniteType affineQuasicoherentPullbackIso
      finiteTypeSheavesAffineEquivalence finiteTypeSheavesRestriction
      finiteTypeSheavesSpecModuleEquivalence finiteTypeSheavesToModules)
attribute [local instance] Abelian.hasFiniteBiproducts Scheme.fromSpecStalk_flat
namespace AlgebraicGeometry.Scheme.Modules.Coherent.Localization.Stalk
universe u

/-- Actual coherent restriction to an affine chart, its global sections,
and actual scalar localization. This functor has no supplied quotient or
generic-image hypotheses. -/
abbrev chartLocalization {X : Scheme.{u}} [IsNoetherian X]
    (R : CommRingCat.{u}) [IsNoetherianRing R]
    (j : Spec R ⟶ X) [IsOpenImmersion j] (S : Submonoid R) :
    FiniteTypeSheaves X ⥤ FGModuleCat.{u} (Localization S) :=
  (finiteTypeSheavesRestriction j ⋙ (finiteTypeSheavesSpecModuleEquivalence R).functor) ⋙
    _root_.ModuleCat.FiniteLocalization.functor S

theorem chartLocalization_isLocalization {X : Scheme.{u}} [IsNoetherian X]
    (R : CommRingCat.{u}) [IsNoetherianRing R]
    (j : Spec R ⟶ X) [IsOpenImmersion j] (S : Submonoid R) :
    (chartLocalization R j S).IsLocalization (chartLocalization R j S).kernel.isoModSerre := by
  let E := (finiteTypeSheavesSpecModuleEquivalence R).functor
  have : E.IsLocalization E.kernel.isoModSerre :=
      CategoryTheory.Functor.isLocalization_kernel_of_equivalence E
  have : (finiteTypeSheavesRestriction j ⋙ E).IsLocalization
      (finiteTypeSheavesRestriction j ⋙ E).kernel.isoModSerre :=
    CategoryTheory.Functor.isLocalization_comp_kernel (finiteTypeSheavesRestriction j) E
  have : (_root_.ModuleCat.FiniteLocalization.functor S).IsLocalization
      (_root_.ModuleCat.FiniteLocalization.functor S).kernel.isoModSerre :=
    _root_.ModuleCat.FiniteLocalization.functor_isLocalization S
  exact CategoryTheory.Functor.isLocalization_comp_kernel (finiteTypeSheavesRestriction j ⋙ E)
    (_root_.ModuleCat.FiniteLocalization.functor S)


attribute [local instance] chartLocalization_isLocalization

instance chartLocalization_additive {X : Scheme.{u}} [IsNoetherian X]
    (R : CommRingCat.{u}) [IsNoetherianRing R]
    (j : Spec R ⟶ X) [IsOpenImmersion j] (S : Submonoid R) :
    (chartLocalization R j S).Additive := by
  let := preservesBinaryBiproducts_of_preservesBinaryProducts (chartLocalization R j S)
  exact Functor.additive_of_preservesBinaryBiproducts _

/-- The exact functor uses the unchanged coherent and finite-module abelian
structures, so its K-map is the actual chart restriction/localization map. -/
abbrev chartLocalizationExact {X : Scheme.{u}} [IsNoetherian X]
    (R : CommRingCat.{u}) [IsNoetherianRing R]
    (j : Spec R ⟶ X) [IsOpenImmersion j] (S : Submonoid R) :
    _root_.CategoryTheory.ExactCategory.ExactFunctor (coherentExactStructure X)
      (_root_.CategoryTheory.ExactCategory.abelianExactStructure (FGModuleCat.{u} (Localization
          S))) where
  toFunctor := chartLocalization R j S
  map_conflation _ h := h.map_of_exact _

abbrev affineLocalizationFunctor (R : CommRingCat.{u}) [IsNoetherianRing R]
    (S : Submonoid R) :
    FiniteTypeSheaves (Spec R) ⥤ FiniteTypeSheaves (Spec (CommRingCat.of (Localization S))) :=
  ((finiteTypeSheavesSpecModuleEquivalence R).functor ⋙
    _root_.ModuleCat.FiniteLocalization.functor S) ⋙
      (finiteTypeSheavesSpecModuleEquivalence (CommRingCat.of (Localization S))).inverse

theorem affineLocalizationFunctor_isLocalization
    (R : CommRingCat.{u}) [IsNoetherianRing R] (S : Submonoid R) :
    (affineLocalizationFunctor R S).IsLocalization
      (affineLocalizationFunctor R S).kernel.isoModSerre := by
  let E := (finiteTypeSheavesSpecModuleEquivalence R).functor
  let E' := (finiteTypeSheavesSpecModuleEquivalence (CommRingCat.of (Localization S))).inverse
  have : E.IsLocalization E.kernel.isoModSerre :=
      CategoryTheory.Functor.isLocalization_kernel_of_equivalence E
  have : E'.IsLocalization E'.kernel.isoModSerre :=
      CategoryTheory.Functor.isLocalization_kernel_of_equivalence E'
  have : (_root_.ModuleCat.FiniteLocalization.functor S).IsLocalization
      (_root_.ModuleCat.FiniteLocalization.functor S).kernel.isoModSerre :=
    _root_.ModuleCat.FiniteLocalization.functor_isLocalization S
  have : (E ⋙ _root_.ModuleCat.FiniteLocalization.functor S).IsLocalization
      (E ⋙ _root_.ModuleCat.FiniteLocalization.functor S).kernel.isoModSerre :=
    CategoryTheory.Functor.isLocalization_comp_kernel E
        (_root_.ModuleCat.FiniteLocalization.functor S)
  exact CategoryTheory.Functor.isLocalization_comp_kernel (E ⋙
      _root_.ModuleCat.FiniteLocalization.functor S) E'

/-- The comparison concerns the actual affine coherent pullback; its tensor
map and localization map have been compared explicitly above. -/
def coherentLocalizationPullbackIso
    (R : CommRingCat.{u}) [IsNoetherianRing R] (S : Submonoid R) :
    coherentPullback (Spec.map (CommRingCat.ofHom (algebraMap R (Localization S)))) ≅
      affineLocalizationFunctor R S := by
  apply Functor.fullyFaithfulCancelRight
    (finiteTypeSheavesToModules (Spec (CommRingCat.of (Localization S))))
  let Q : FiniteTypeSheaves (Spec R) ⥤ AffineQuasicoherent R :=
    (finiteTypeSheavesAffineEquivalence R).functor ⋙ (affineFiniteType R).ι
  exact (Functor.isoWhiskerLeft Q (affineQuasicoherentPullbackIso
      (CommRingCat.ofHom (algebraMap R (Localization S))))) ≪≫
    (Functor.isoWhiskerLeft (Q ⋙ (tildeEquiv (R := R)).inverse)
      (Functor.isoWhiskerRight (ModuleCat.tensorLocalizationNatIso S)
        (tilde.functor (CommRingCat.of (Localization S)))))


local instance coherentPullback_finiteLimits {X Y : Scheme.{u}}
    [IsLocallyNoetherian X] [IsLocallyNoetherian Y] (f : X ⟶ Y) [Flat f] :
    PreservesFiniteLimits (coherentPullback f) :=
  (Functor.preservesFiniteLimits_iff_forall_exact_map_and_mono (coherentPullback f)).mpr
    (fun S hS => ⟨((coherentExactPullback f).map_conflation S hS).exact,
      ((coherentExactPullback f).map_conflation S hS).mono_f⟩)

local instance coherentPullback_finiteColimits {X Y : Scheme.{u}}
    [IsLocallyNoetherian X] [IsLocallyNoetherian Y] (f : X ⟶ Y) [Flat f] :
    PreservesFiniteColimits (coherentPullback f) :=
  (Functor.preservesFiniteColimits_iff_forall_exact_map_and_epi (coherentPullback f)).mpr
    (fun S hS => ⟨((coherentExactPullback f).map_conflation S hS).exact,
      ((coherentExactPullback f).map_conflation S hS).epi_g⟩)

local instance canonicalLocalizationFlat (R : CommRingCat.{u}) (S : Submonoid R) :
    Flat (Spec.map (CommRingCat.ofHom (algebraMap R (Localization S)))) := by
  apply Flat.SpecMap_iff.mpr
  exact RingHom.flat_algebraMap_iff.mpr (IsLocalization.flat (Localization S) S)

theorem coherentCanonicalLocalization_isLocalization
    (R : CommRingCat.{u}) [IsNoetherianRing R] (S : Submonoid R) :
    (coherentPullback (Spec.map (CommRingCat.ofHom (algebraMap R (Localization S))))).IsLocalization
      (coherentPullback (Spec.map (CommRingCat.ofHom
        (algebraMap R (Localization S))))).kernel.isoModSerre := by
  have : (affineLocalizationFunctor R S).IsLocalization
      (affineLocalizationFunctor R S).kernel.isoModSerre :=
    affineLocalizationFunctor_isLocalization R S
  exact CategoryTheory.Functor.isLocalization_kernel_of_natIso (coherentLocalizationPullbackIso
      R S).symm


/-- Actual restriction equivalence for a scheme isomorphism. This is the
construction in the pinned `ClosedImmersion/AffineReflection.lean:45`,
reproduced here because that optional module has no installed olean. -/
def coherentIsoEquivalence {Z X : Scheme.{u}} (e : Z ≅ X) :
    FiniteTypeSheaves Z ≌ FiniteTypeSheaves X :=
  CategoryTheory.Equivalence.mk (finiteTypeSheavesRestriction e.inv)
    (finiteTypeSheavesRestriction e.hom)
    (Functor.fullyFaithfulCancelRight (finiteTypeSheavesToModules Z)
      (Functor.isoWhiskerLeft (finiteTypeSheavesToModules Z)
        (Scheme.Modules.restrictFunctorId.symm ≪≫
          Scheme.Modules.restrictFunctorCongr e.hom_inv_id.symm ≪≫
          Scheme.Modules.restrictFunctorComp e.hom e.inv)))
    (Functor.fullyFaithfulCancelRight (finiteTypeSheavesToModules X)
      (Functor.isoWhiskerLeft (finiteTypeSheavesToModules X)
        ((Scheme.Modules.restrictFunctorComp e.inv e.hom).symm ≪≫
          Scheme.Modules.restrictFunctorCongr e.inv_hom_id ≪≫
          Scheme.Modules.restrictFunctorId)))

section ArbitraryLocalization
variable (R A : CommRingCat.{u}) [IsNoetherianRing R] [IsNoetherianRing A]
  [Algebra R A]

omit [IsNoetherianRing R] [IsNoetherianRing A] in
theorem scalarLocalization_flat (S : Submonoid R) [IsLocalization S A] :
    Flat (Spec.map (CommRingCat.ofHom (algebraMap R A))) := by
  apply Flat.SpecMap_iff.mpr
  exact RingHom.flat_algebraMap_iff.mpr (IsLocalization.flat A S)

/-- Scalar localization in any actual target ring, not only the chosen
`Localization S` implementation, is actual coherent Serre localization. -/
theorem coherentLocalization_isLocalization (S : Submonoid R) [IsLocalization S A]
    [Flat (Spec.map (CommRingCat.ofHom (algebraMap R A)))] :
    (coherentPullback (Spec.map (CommRingCat.ofHom (algebraMap R A)))).IsLocalization
      (coherentPullback (Spec.map (CommRingCat.ofHom (algebraMap R A)))).kernel.isoModSerre := by
  let e := IsLocalization.algEquiv S (Localization S) A
  let ee : Spec A ≅ Spec (CommRingCat.of (Localization S)) :=
    Scheme.Spec.mapIso e.toRingEquiv.toCommRingCatIso.op
  let f := Spec.map (CommRingCat.ofHom (algebraMap R (Localization S)))
  let g := ee.hom
  have : (finiteTypeSheavesRestriction g).IsEquivalence :=
    (coherentIsoEquivalence ee.symm).isEquivalence_functor
  have : (coherentPullback g).IsEquivalence :=
    Functor.isEquivalence_of_iso (coherentRestrictionIsoPullback g)
  have : (coherentPullback g).IsLocalization (coherentPullback g).kernel.isoModSerre :=
    CategoryTheory.Functor.isLocalization_kernel_of_equivalence _
  have : (coherentPullback f).IsLocalization (coherentPullback f).kernel.isoModSerre :=
    coherentCanonicalLocalization_isLocalization R S
  have : (coherentPullback f ⋙ coherentPullback g).IsLocalization
      (coherentPullback f ⋙ coherentPullback g).kernel.isoModSerre :=
    CategoryTheory.Functor.isLocalization_comp_kernel _ _
  have h : g ≫ f = Spec.map (CommRingCat.ofHom (algebraMap R A)) := by
    change Spec.map (CommRingCat.ofHom e.toRingEquiv.toRingHom) ≫
      Spec.map (CommRingCat.ofHom (algebraMap R (Localization S))) = _
    rw [← Spec.map_comp]
    congr 1
    ext r
    exact e.commutes r
  let ec : coherentPullback (Spec.map (CommRingCat.ofHom (algebraMap R A))) ≅
      coherentPullback f ⋙ coherentPullback g :=
    eqToIso (congrArg coherentPullback h.symm) ≪≫ coherentPullbackCompIso g f
  exact CategoryTheory.Functor.isLocalization_kernel_of_natIso ec.symm

end ArbitraryLocalization


/-- Actual coherent pullback to every stalk of a Noetherian scheme is
localization by its actual kernel. The proof uses one original affine chart,
its proved open restriction localization, and scalar localization at its
actual prime. No generic or residue quotient equivalence is a hypothesis. -/
theorem coherentStalkPullback_isLocalization
    (X : Scheme.{u}) [IsNoetherian X] (x : X) :
    (coherentPullback (X.fromSpecStalk x)).IsLocalization
      (coherentPullback (X.fromSpecStalk x)).kernel.isoModSerre := by
  let U := (X.affineCover.f (X.affineCover.idx x)).opensRange
  let hU : IsAffineOpen U := isAffineOpen_opensRange (X.affineCover.f (X.affineCover.idx x))
  have hx : x ∈ U := X.affineCover.covers x
  let R : CommRingCat.{u} := Γ(X, U)
  let A : CommRingCat.{u} := X.presheaf.stalk x
  let : IsNoetherianRing R := IsLocallyNoetherian.component_noetherian ⟨U, hU⟩
  let : Algebra R A := (X.presheaf.germ U x hx).hom.toAlgebra
  let S : Submonoid R := (hU.primeIdealOf ⟨x, hx⟩).asIdeal.primeCompl
  have : IsLocalization S A := hU.isLocalization_stalk ⟨x, hx⟩
  let f := hU.fromSpec
  let g := Spec.map (X.presheaf.germ U x hx)
  have : Flat g := scalarLocalization_flat R A S
  have : (coherentPullback g).IsLocalization (coherentPullback g).kernel.isoModSerre :=
    coherentLocalization_isLocalization R A S
  have : (coherentPullback f).IsLocalization (coherentPullback f).kernel.isoModSerre :=
    CategoryTheory.Functor.isLocalization_kernel_of_natIso (coherentRestrictionIsoPullback f)
  have : (coherentPullback f ⋙ coherentPullback g).IsLocalization
      (coherentPullback f ⋙ coherentPullback g).kernel.isoModSerre :=
    CategoryTheory.Functor.isLocalization_comp_kernel _ _
  have h : g ≫ f = X.fromSpecStalk x := hU.fromSpecStalk_eq_fromSpecStalk hx
  let ec : coherentPullback (X.fromSpecStalk x) ≅
      coherentPullback f ⋙ coherentPullback g :=
    eqToIso (congrArg coherentPullback h.symm) ≪≫ coherentPullbackCompIso g f
  exact CategoryTheory.Functor.isLocalization_kernel_of_natIso ec.symm


end AlgebraicGeometry.Scheme.Modules.Coherent.Localization.Stalk
