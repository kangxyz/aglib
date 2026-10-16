/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.Algebra.Module.LocalizedModule.FiniteSubmodule
public import Aglib.Algebra.Category.ModuleCat.Localization.Submodule
public import Aglib.AlgebraicGeometry.Modules.QuasiCoherent.Affine.Isomorphisms
public import Aglib.AlgebraicGeometry.Modules.QuasiCoherent.FiniteType.Basic
public import Aglib.AlgebraicGeometry.Modules.Locality.Isomorphisms
public import Aglib.AlgebraicGeometry.Modules.QuasiCoherent.Affine.FiniteTypeRestriction
public import Aglib.AlgebraicGeometry.Modules.QuasiCoherent.Affine.FiniteTypeComparison

/-!
# Finite-type approximation on an affine scheme

Finite generation on a finite family of principal opens, or on a compact open of a spectrum, is
realized by a finitely generated submodule. For a quasicoherent ambient sheaf this gives a
finite-type subsheaf whose actual restriction inclusion is an isomorphism. The ring is
arbitrary.
-/

/-!
Source: frozen dirty Quillen `6db56ddd3fdb898ef5de29d5fe51a0c61f9ba116`.
`Quillen/AlgebraicGeometry/Scheme/Coherent/Localization/AffineApproximation.lean`.
SHA-256: `2029b40cd181d56164f97a019526a3e93de58da78ca2ad65b0f9b33ad9b3ef18`.
Selected original statements and proofs; canonical lower APIs replace the recorded source wrappers.
-/

@[expose] public section

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u v
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace
open ModuleCat
open AlgebraicGeometry.Scheme.Modules
attribute [local instance] Abelian.hasFiniteBiproducts
namespace AlgebraicGeometry.Scheme.Modules.QuasiCoherent

/-- One finitely generated submodule captures all finite restrictions on a
finite family of principal affine opens, with actual sheaf isomorphisms. -/
theorem exists_fg_submodule_principal_restriction_isIso
    (R : CommRingCat.{u}) (M : ModuleCat.{u} R) {ι : Type v} [Finite ι]
    (r : ι → R) [∀ i, Module.Finite (Localization.Away (r i))
      (restrictionGlobalSections R (r i) M)] :
    ∃ L : Submodule R M, L.FG ∧ ∀ i,
      IsIso ((Scheme.Modules.restrictFunctor (principalOpen R (r i))).map
        (tilde.map (ModuleCat.ofHom L.subtype))) := by
  have hfin (i : ι) : Module.Finite (Localization.Away (r i))
      (M.localizedModule (.powers (r i))) :=
    Module.Finite.of_surjective (localizationRestrictionIso R (r i) M).inv.hom
      (ConcreteCategory.bijective_of_isIso _).surjective
  obtain ⟨L, hL, htop⟩ := IsLocalizedModule.exists_fg_submodule_localized_eq_top_finite
    (fun i => Submonoid.powers (r i)) (fun i => Localization.Away (r i))
    (fun i => M.localizedModule (.powers (r i)))
    (fun i => M.localizedModuleMkLinearMap (.powers (r i)))
  refine ⟨L, hL, fun i => ?_⟩
  have hlociso : IsIso (ModuleCat.localizedModuleMap (.powers (r i)) (ModuleCat.ofHom L.subtype)) :=
    isIso_localized_subtype_of_eq_top R _ M L (htop i)
  have hΓ : IsIso ((restrictionGlobalSectionsFunctor R (r i)).map (ModuleCat.ofHom L.subtype)) :=
    (NatIso.isIso_map_iff (localizationRestrictionNatIso R (r i)) _).mp hlociso
  have : IsIso (moduleSpecΓFunctor.map
      ((Scheme.Modules.restrictFunctor (principalOpen R (r i))).map
        (tilde.map (ModuleCat.ofHom L.subtype)))) := hΓ
  exact affine_isIso_of_globalSections _ _

/-- Finite-type quasicoherence on a compact open of an affine scheme is captured
by a finitely generated submodule of the global module: the actual restricted
inclusion of its associated sheaf is an isomorphism. -/
theorem exists_fg_submodule_open_restriction_isIso
    (R : CommRingCat.{u}) (M : ModuleCat.{u} R) (V : (Spec R).Opens)
    (hV : IsCompact (V : Set (Spec R)))
    (hM : affineLocallyFiniteType V.toScheme ((tilde M).restrict V.ι)) :
    ∃ L : Submodule R M, L.FG ∧
      IsIso ((Scheme.Modules.restrictFunctor V.ι).map
        (tilde.map (ModuleCat.ofHom L.subtype))) := by
  classical
  obtain ⟨ι, _, r, hr⟩ :=
    PrimeSpectrum.isBasis_basic_opens.exists_iSup_eq_of_isCompact V hV
  have hle (i : ι) : PrimeSpectrum.basicOpen (r i) ≤ V := by
    rw [hr]
    exact le_iSup_of_le _ le_rfl
  have hfin (i : ι) : Module.Finite (Localization.Away (r i))
      (restrictionGlobalSections R (r i) M) := by
    let t := (Spec R).homOfLE (U := PrimeSpectrum.basicOpen (r i)) (V := V) (hle i)
    let q := (basicOpenIsoSpecAway (r i)).inv ≫ t
    let e : Scheme.Modules.restrictFunctor V.ι ⋙ Scheme.Modules.restrictFunctor q ≅
        Scheme.Modules.restrictFunctor (principalOpen R (r i)) :=
      (Scheme.Modules.restrictFunctorComp q V.ι).symm ≪≫
        Scheme.Modules.restrictFunctorCongr (by simp [q, t, basicOpenIsoSpecAway])
    exact ((affineFiniteSheaf (CommRingCat.of (Localization.Away (r i)))).prop_of_iso
      (e.app (tilde M)) (hM _ q)).2
  obtain ⟨L, hL, hLi⟩ := exists_fg_submodule_principal_restriction_isIso R M r
  refine ⟨L, hL, ?_⟩
  apply moduleSheaf_isIso_restrict_of_openCover V.ι
    (fun i => Spec (CommRingCat.of (Localization.Away (r i))))
    (fun i => principalOpen R (r i)) ?_ _ hLi
  intro x
  have hx : (x.1 : Spec R) ∈ ⨆ i, PrimeSpectrum.basicOpen (r i) := by
    rw [← hr]
    exact x.2
  obtain ⟨i, hi⟩ := TopologicalSpace.Opens.mem_iSup.mp hx
  have hi' : V.ι x ∈ (principalOpen R (r i)).opensRange := by
    rw [Scheme.Hom.opensRange_localizationAway]
    exact hi
  exact ⟨i, hi'⟩

/-- Over an arbitrary commutative ring, a quasicoherent affine sheaf of finite type on a
compact open contains an affine-local finite-type subsheaf agreeing on that open.
The construction uses a finitely generated global submodule and needs no noetherian hypothesis. -/
theorem exists_finiteType_subsheaf_restrict_isIso
    (R : CommRingCat.{u}) (M : (Spec R).Modules)
    [M.IsQuasicoherent] (V : (Spec R).Opens) (hV : IsCompact (V : Set (Spec R)))
    (hM : affineLocallyFiniteType V.toScheme (M.restrict V.ι)) :
    ∃ (N : FiniteTypeSheaves (Spec R)) (i : N.obj ⟶ M), Mono i ∧
      IsIso ((Scheme.Modules.restrictFunctor V.ι).map i) := by
  let P := moduleSpecΓFunctor.obj M
  let : Module R P := P.isModule
  have : IsIso M.fromTildeΓ := Scheme.Modules.isIso_fromTildeΓ_of_isQuasicoherent M
  let e : tilde P ≅ M := asIso M.fromTildeΓ
  have hP : affineLocallyFiniteType V.toScheme ((tilde P).restrict V.ι) :=
    (affineLocallyFiniteType V.toScheme).prop_of_iso
      ((Scheme.Modules.restrictFunctor V.ι).mapIso e.symm) hM
  obtain ⟨L, hL, hi⟩ := exists_fg_submodule_open_restriction_isIso R P V hV hP
  have : Module.Finite R L := Module.Finite.of_fg hL
  let N : FiniteTypeSheaves (Spec R) :=
    ⟨tilde (ModuleCat.of.{u} R L), (affineLocallyFiniteType_spec_iff R _).mpr
      ⟨inferInstance, by
        have : Module.Finite R (ModuleCat.of.{u} R L) := inferInstanceAs (Module.Finite R L)
        let eL : ModuleCat.of.{u} R L ≅ moduleSpecΓFunctor.obj (tilde (ModuleCat.of.{u} R L)) :=
          tilde.toTildeΓNatIso.app (ModuleCat.of.{u} R L)
        exact Module.Finite.equiv eL.toLinearEquiv⟩⟩
  let a : ModuleCat.of.{u} R L ⟶ P := ModuleCat.ofHom (Y := P) L.subtype
  have : Mono a := (ModuleCat.mono_iff_injective a).mpr (by
    intro x y h
    exact Subtype.ext h)
  have : Mono (tilde.map a) := (tilde.functor R).map_mono a
  let i : N.obj ⟶ M := tilde.map a ≫ e.hom
  refine ⟨N, i, ?_, ?_⟩
  · dsimp only [i]
    infer_instance
  · dsimp only [i]
    rw [Functor.map_comp]
    have : IsIso ((Scheme.Modules.restrictFunctor V.ι).map (tilde.map a)) := hi
    infer_instance

end AlgebraicGeometry.Scheme.Modules.QuasiCoherent
