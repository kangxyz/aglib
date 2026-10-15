/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Modules.LocallyFree.FiniteType
public import Aglib.AlgebraicGeometry.Modules.LocallyFree.LocalBases
public import Aglib.AlgebraicGeometry.Modules.QuasiCoherent.Affine.FiniteTypeComparison
public import Mathlib.RingTheory.Spectrum.Prime.FreeLocus

/-!
Source: `Quillen/AlgebraicGeometry/Scheme/Regular/AffineProjective.lean` at LOCAL Quillen
`189a8e779f0c68b2dfc6f8195daebb3e684a5905`. Selection: whole_general_prerequisite;
source ranges [[1, 197]]. Actual objects, maps and hypotheses are preserved.
-/

/-! # Finite projective modules and actual affine vector bundles -/
@[expose] public section

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace
open scoped ModuleCat.Algebra

open AlgebraicGeometry.Scheme.Modules

namespace AlgebraicGeometry.Scheme.Modules

/-- Carry a global basis on an open subscheme back to its over-site. -/
def generatingSectionsRestrictToOver {X : Scheme.{u}} {M : X.Modules} (U : X.Opens)
    (G : (M.restrict U.ι).GeneratingSections) : (M.over U).GeneratingSections :=
  let E := Scheme.Modules.overEquiv U
  let e : E.inverse.obj (M.restrict U.ι) ≅ M.over U :=
    (E.inverse.mapIso ((Scheme.Modules.overFunctorEquiv U).app M)).symm ≪≫
      (E.unitIso.app (M.over U)).symm
  (G.map E.inverse (U.sheafOfModulesEquivOverInverseUnit X.ringCatSheaf).symm).ofEpi e.hom

instance generatingSectionsRestrictToOver_isFiniteType {X : Scheme.{u}} {M : X.Modules}
    (U : X.Opens) (G : (M.restrict U.ι).GeneratingSections) [G.IsFiniteType] :
    (generatingSectionsRestrictToOver U G).IsFiniteType := by
  dsimp [generatingSectionsRestrictToOver]
  infer_instance

instance generatingSectionsRestrictToOver_isIso {X : Scheme.{u}} {M : X.Modules}
    (U : X.Opens) (G : (M.restrict U.ι).GeneratingSections) [IsIso G.π] :
    IsIso (generatingSectionsRestrictToOver U G).π := by
  dsimp [generatingSectionsRestrictToOver]
  infer_instance

/-- A basis on the affine localization chart becomes a basis on the actual
principal open subset of the original scheme. -/
def generatingSectionsPrincipalToOver (R : CommRingCat.{u}) (M : (Spec R).Modules) (r : R)
    (G : (M.restrict (QuasiCoherent.principalOpen R r)).GeneratingSections) :
    (M.over (PrimeSpectrum.basicOpen r)).GeneratingSections := by
  let a := (basicOpenIsoSpecAway r).hom
  have : PreservesColimitsOfSize.{u, u} (Scheme.Modules.restrictFunctor a) := inferInstance
  let e : Scheme.Modules.restrictFunctor (QuasiCoherent.principalOpen R r) ⋙
      Scheme.Modules.restrictFunctor a ≅
      Scheme.Modules.restrictFunctor (Scheme.Opens.ι (X := Spec R) (PrimeSpectrum.basicOpen r)) :=
    (Scheme.Modules.restrictFunctorComp a (QuasiCoherent.principalOpen R r)).symm ≪≫
      Scheme.Modules.restrictFunctorCongr (basicOpenIsoSpecAway_hom_SpecMap r)
  exact generatingSectionsRestrictToOver (X := Spec R) (PrimeSpectrum.basicOpen r)
    ((G.map (Scheme.Modules.restrictFunctor a) (Scheme.Modules.restrictUnitIso a).symm).ofEpi
      (e.app M).hom)

instance generatingSectionsPrincipalToOver_isFiniteType (R : CommRingCat.{u})
    (M : (Spec R).Modules) (r : R)
    (G : (M.restrict (QuasiCoherent.principalOpen R r)).GeneratingSections) [G.IsFiniteType] :
    (generatingSectionsPrincipalToOver R M r G).IsFiniteType := by
  dsimp [generatingSectionsPrincipalToOver]
  infer_instance

instance generatingSectionsPrincipalToOver_isIso (R : CommRingCat.{u})
    (M : (Spec R).Modules) (r : R)
    (G : (M.restrict (QuasiCoherent.principalOpen R r)).GeneratingSections) [IsIso G.π] :
    IsIso (generatingSectionsPrincipalToOver R M r G).π := by
  dsimp [generatingSectionsPrincipalToOver]
  infer_instance

/-- Finite free global sections give a finite global sheaf basis on an affine
scheme, through the actual tilde equivalence. -/
theorem exists_finiteGlobalBasis_of_free_sections (R : CommRingCat.{u}) (M : (Spec R).Modules)
    [M.IsQuasicoherent] [Module.Free R (moduleSpecΓFunctor.obj M)]
    [Module.Finite R (moduleSpecΓFunctor.obj M)] :
    ∃ G : M.GeneratingSections, IsIso G.π ∧ G.IsFiniteType := by
  have : IsIso M.fromTildeΓ := Scheme.Modules.isIso_fromTildeΓ_of_isQuasicoherent M
  let N := moduleSpecΓFunctor.obj M
  let b := Module.Free.chooseBasis R N
  let e : SheafOfModules.free (R := (Spec R).ringCatSheaf)
      (Module.Free.ChooseBasisIndex R N) ≅ M :=
    (tildeFinsupp (Module.Free.ChooseBasisIndex R N)).symm ≪≫
      (tilde.functor R).mapIso b.repr.symm.toModuleIso ≪≫ asIso M.fromTildeΓ
  let G := (SheafOfModules.free.generatingSections
    (R := (Spec R).ringCatSheaf) (Module.Free.ChooseBasisIndex R N)).ofEpi e.hom
  refine ⟨G, inferInstance, ?_⟩
  constructor
  change Finite (Module.Free.ChooseBasisIndex R N)
  infer_instance

/-- An actual finite projective module gives an actual finite locally free
sheaf. Freeness at each prime is spread to a principal open; the finite local
basis is then transported to the sheaf's Zariski over-site. -/
theorem finiteLocallyFree_tilde_of_finite_projective (R : CommRingCat.{u})
    (M : ModuleCat.{u} R) [Module.Finite R M] [Module.Projective R M] :
    IsFiniteLocallyFree (Spec R) (tilde M) := by
  have : Module.FinitePresentation R M := Module.finitePresentation_of_projective R M
  apply finiteLocallyFree_iff_pointwise.mpr
  intro x
  have : Module.Free (Localization.AtPrime x.asIdeal)
      (LocalizedModule x.asIdeal.primeCompl M) := Module.free_of_flat_of_isLocalRing
  obtain ⟨r, hr, hfree, _⟩ :=
    Module.FinitePresentation.exists_free_localizedModule_powers x.asIdeal.primeCompl
      (LocalizedModule.mkLinearMap x.asIdeal.primeCompl M) (Localization.AtPrime x.asIdeal)
  let N := QuasiCoherent.restrictionGlobalSections R r M
  let e : LocalizedModule.Away r M ≃ₗ[Localization.Away r] N :=
    (IsLocalizedModule.linearEquiv (Submonoid.powers r)
      (LocalizedModule.mkLinearMap (Submonoid.powers r) M)
      (QuasiCoherent.toRestrictionGlobalSections R r M)).extendScalarsOfIsLocalization
        (Submonoid.powers r) (Localization.Away r)
  have : Module.Free (Localization.Away r) (LocalizedModule.Away r M) := hfree
  have : Module.Free (Localization.Away r) N := Module.Free.of_equiv e
  have : Module.Finite (Localization.Away r) N :=
    Module.Finite.of_isLocalizedModule (Submonoid.powers r)
      (QuasiCoherent.toRestrictionGlobalSections R r M)
  obtain ⟨G, hG, hfG⟩ := exists_finiteGlobalBasis_of_free_sections
    (CommRingCat.of (Localization.Away r))
    ((tilde M).restrict (QuasiCoherent.principalOpen R r))
  exact ⟨PrimeSpectrum.basicOpen r, hr,
    generatingSectionsPrincipalToOver R (tilde M) r G, inferInstance, inferInstance⟩

/-- A global sheaf basis over an affine scheme gives a free module of
actual global sections. -/
theorem free_globalSections_of_basis (R : CommRingCat.{u}) (M : (Spec R).Modules)
    (G : M.GeneratingSections) [IsIso G.π] :
    Module.Free R (moduleSpecΓFunctor.obj M) := by
  let e : ModuleCat.of R (G.I →₀ R) ≅ moduleSpecΓFunctor.obj M :=
    tilde.toTildeΓNatIso.app _ ≪≫
      moduleSpecΓFunctor.mapIso (tildeFinsupp G.I ≪≫ asIso G.π)
  exact Module.Free.of_equiv e.toLinearEquiv

/-- A basis on any open restricts to a basis of global sections on a
contained principal affine open. -/
theorem free_restrictPrincipal_of_overBasis (R : CommRingCat.{u})
    (M : (Spec R).Modules) (r : R) (U : (Spec R).Opens)
    (h : PrimeSpectrum.basicOpen r ≤ U) (G : (M.over U).GeneratingSections)
    [IsIso G.π] : Module.Free (Localization.Away r)
      (moduleSpecΓFunctor.obj (M.restrict (QuasiCoherent.principalOpen R r))) := by
  let t := (Spec R).homOfLE (U := PrimeSpectrum.basicOpen r) (V := U) h
  let j := (basicOpenIsoSpecAway r).inv ≫ t
  let e : Scheme.Modules.restrictFunctor U.ι ⋙ Scheme.Modules.restrictFunctor j ≅
      Scheme.Modules.restrictFunctor (QuasiCoherent.principalOpen R r) :=
    (Scheme.Modules.restrictFunctorComp j U.ι).symm ≪≫
      Scheme.Modules.restrictFunctorCongr (by simp [j, t, basicOpenIsoSpecAway])
  have : PreservesColimitsOfSize.{u, u} (Scheme.Modules.restrictFunctor j) := inferInstance
  have : IsIso (generatingSectionsOverToRestrict U G).π := by
    dsimp [generatingSectionsOverToRestrict]
    infer_instance
  let G' := ((generatingSectionsOverToRestrict U G).map
    (Scheme.Modules.restrictFunctor j) (Scheme.Modules.restrictUnitIso j).symm).ofEpi
      (e.app M).hom
  exact free_globalSections_of_basis _ _ G'

/-- A finite module whose associated sheaf has genuine finite local bases
is projective. This direction only needs finite presentation of the module. -/
theorem projective_of_finiteLocallyFree_tilde (R : CommRingCat.{u})
    (M : ModuleCat.{u} R) [Module.FinitePresentation R M]
    [hM : IsFiniteLocallyFree (Spec R) (tilde M)] : Module.Projective R M := by
  apply (Module.freeLocus_eq_univ_iff (R := R) (M := M)).mp
  apply Set.eq_univ_of_forall
  intro x
  obtain ⟨q, hq, hf⟩ := hM.exists_localBasis
  obtain ⟨V, f, ⟨i, ⟨g⟩⟩, hxV⟩ := q.coversTop ⊤ x (by simp)
  have hxi : x ∈ q.X i := (leOfHom g) hxV
  obtain ⟨a, ⟨_, ⟨r, rfl⟩, rfl⟩, hxr, hrU : PrimeSpectrum.basicOpen _ ≤ _⟩ :=
    PrimeSpectrum.isBasis_basic_opens.exists_subset_of_mem_open hxi (q.X i).2
  have hfree := free_restrictPrincipal_of_overBasis R (tilde M) r (q.X i) hrU (q.generators i)
  let e : LocalizedModule.Away r M ≃ₗ[Localization.Away r]
      QuasiCoherent.restrictionGlobalSections R r M :=
    (IsLocalizedModule.linearEquiv (Submonoid.powers r)
      (LocalizedModule.mkLinearMap (Submonoid.powers r) M)
      (QuasiCoherent.toRestrictionGlobalSections R r M)).extendScalarsOfIsLocalization
        (Submonoid.powers r) (Localization.Away r)
  have : Module.Free (Localization.Away r) (LocalizedModule.Away r M) :=
    Module.Free.of_equiv e.symm
  exact (Module.basicOpen_subset_freeLocus_iff (R := R) (M := M)).mpr
    (show Module.Projective (Localization.Away r) (LocalizedModule.Away r M) from inferInstance) hxr

/-- On an affine noetherian scheme the tilde module is a vector bundle
exactly when the original finite module is projective. -/
theorem finiteLocallyFree_tilde_iff_projective (R : CommRingCat.{u}) [IsNoetherianRing R]
    (M : ModuleCat.{u} R) [Module.Finite R M] :
    IsFiniteLocallyFree (Spec R) (tilde M) ↔ Module.Projective R M := by
  have : Module.FinitePresentation R M := Module.finitePresentation_of_finite R M
  constructor
  · intro h
    have := h
    exact projective_of_finiteLocallyFree_tilde R M
  · intro h
    have := h
    exact finiteLocallyFree_tilde_of_finite_projective R M

end AlgebraicGeometry.Scheme.Modules
