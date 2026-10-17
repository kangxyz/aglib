/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Modules.Flat.Relative.AffineSections
public import Aglib.AlgebraicGeometry.Modules.QuasiCoherent.FiniteType.Basic
public import Aglib.RingTheory.GenericFreeness.Localization
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType

/-!
# Generic flatness over an affine integral Noetherian base

For a ring map `φ : A ⟶ B` and a quasicoherent `N` on `Spec B`, flatness of the localized
global sections `Γ(N)[1/a]` over `A[1/a]` gives flatness of the actual stalks of `N` over the
base local rings at every point lying over the basic open `D(a)`.
-/

@[expose] public section

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

namespace AlgebraicGeometry.Scheme.Modules

-- The `Module` instances on the carriers of `ModuleCat.restrictScalars` objects are identified
-- with those of the original modules only by unfolding below instance transparency.
set_option backward.isDefEq.respectTransparency false in
/-- If the global sections of a quasicoherent `N` on `Spec B` become flat over `A[1/a]` after
inverting `a`, then the actual stalk of `N` at every point `y` with `φ a ∉ y` is flat over the
base local ring at `Spec.map φ y`, through the original stalk map. -/
theorem flat_stalk_specMap_of_flat_localizedModule_away {A B : CommRingCat.{u}} (φ : A ⟶ B)
    (N : (Spec B).Modules) [N.IsQuasicoherent] (a : A)
    [Module.Flat (Localization.Away a)
      (LocalizedModule.Away a ((ModuleCat.restrictScalars φ.hom).obj (moduleSpecΓFunctor.obj N)))]
    (y : Spec B) (hy : φ.hom a ∉ y.asIdeal) :
    Module.Flat ((Spec A).presheaf.stalk (Spec.map φ y))
      ((ModuleCat.restrictScalars ((Spec.map φ).stalkMap y).hom).obj
        ((moduleStalk (Spec B) y).obj N)) := by
  let := φ.hom.toAlgebra
  let E := moduleSpecΓFunctor.obj N
  let : IsScalarTower A B ((ModuleCat.restrictScalars φ.hom).obj E) :=
    IsScalarTower.of_algebraMap_smul fun _ _ => rfl
  let Fy : ModuleCat A :=
    (ModuleCat.restrictScalars φ.hom).obj (ModuleCat.of B ((tilde E).presheaf.stalk y))
  let : IsScalarTower A B Fy := IsScalarTower.of_algebraMap_smul fun _ _ => rfl
  have : IsLocalizedModule y.asIdeal.primeCompl (tilde.toStalk E y).hom := inferInstance
  have h1 : Module.Flat A Fy :=
    Module.flat_of_isLocalizedModule_of_flat_localizedModule_away (B := B)
      (M := (ModuleCat.restrictScalars φ.hom).obj E) a y.asIdeal.primeCompl hy (M' := Fy)
      (tilde.toStalk E y).hom
  let e := (ModuleCat.restrictScalars φ.hom).mapIso
    ((ModuleCat.restrictScalars (StructureSheaf.toStalk B y).hom).mapIso
      ((moduleStalk (Spec B) y).mapIso (asIso N.fromTildeΓ)))
  have h2 := (Module.Flat.equiv_iff e.toLinearEquiv).mp h1
  have h3 : Module.Flat A ((ModuleCat.restrictScalars
      ((StructureSheaf.toStalk B y).hom.comp φ.hom)).obj ((moduleStalk (Spec B) y).obj N)) :=
    (Module.Flat.equiv_iff ((ModuleCat.restrictScalarsComp φ.hom
      (StructureSheaf.toStalk B y).hom).app ((moduleStalk (Spec B) y).obj N)).toLinearEquiv).mpr h2
  have he : ((Spec.map φ).stalkMap y).hom.comp
      (StructureSheaf.toStalk A ((Spec.map φ) y)).hom =
      (StructureSheaf.toStalk B y).hom.comp φ.hom :=
    congrArg CommRingCat.Hom.hom (AlgebraicGeometry.stalkMap_toStalk φ y)
  rw [← he] at h3
  let X' := (ModuleCat.restrictScalars ((Spec.map φ).stalkMap y).hom).obj
    ((moduleStalk (Spec B) y).obj N)
  have h4 : Module.Flat A ((ModuleCat.restrictScalars
      (StructureSheaf.toStalk A ((Spec.map φ) y)).hom).obj X') :=
    (Module.Flat.equiv_iff ((ModuleCat.restrictScalarsComp
      (StructureSheaf.toStalk A ((Spec.map φ) y)).hom
      ((Spec.map φ).stalkMap y).hom).app ((moduleStalk (Spec B) y).obj N)).toLinearEquiv).mp h3
  let : Algebra A ((Spec.structureSheaf A).presheaf.stalk ((Spec.map φ) y)) :=
    StructureSheaf.stalkAlgebra A ((Spec.map φ) y)
  let : IsLocalization.AtPrime ((Spec.structureSheaf A).presheaf.stalk ((Spec.map φ) y))
      ((Spec.map φ) y).asIdeal := StructureSheaf.IsLocalization.to_stalk A ((Spec.map φ) y)
  let : IsScalarTower A ((Spec.structureSheaf A).presheaf.stalk ((Spec.map φ) y))
      ((ModuleCat.restrictScalars (StructureSheaf.toStalk A ((Spec.map φ) y)).hom).obj X') :=
    IsScalarTower.of_algebraMap_smul fun _ _ => rfl
  exact (Module.flat_iff_of_isLocalization
    ((Spec.structureSheaf A).presheaf.stalk ((Spec.map φ) y)) ((Spec.map φ) y).asIdeal.primeCompl
    ((ModuleCat.restrictScalars (StructureSheaf.toStalk A ((Spec.map φ) y)).hom).obj X')).mpr h4

/-- Flatness of an actual restricted stalk over the base local ring gives flatness of the
original stalk at the image point: the pointwise converse of `relativeFlat_restrict`. -/
theorem flat_stalk_of_flat_stalk_restrict {U X Y : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j]
    (f : X ⟶ Y) (M : X.Modules) (x : U)
    (h : Module.Flat (Y.presheaf.stalk ((j ≫ f) x))
      ((ModuleCat.restrictScalars ((j ≫ f).stalkMap x).hom).obj
        ((moduleStalk U x).obj (M.restrict j)))) :
    Module.Flat (Y.presheaf.stalk (f (j x)))
      ((ModuleCat.restrictScalars (f.stalkMap (j x)).hom).obj ((moduleStalk X (j x)).obj M)) := by
  let T := (moduleStalk U x).obj (M.restrict j)
  have he : ((j ≫ f).stalkMap x).hom =
      (j.stalkMap x).hom.comp (f.stalkMap (j x)).hom :=
    congrArg CommRingCat.Hom.hom (Scheme.Hom.stalkMap_comp j f x)
  let e := (ModuleCat.restrictScalarsComp' (f.stalkMap (j x)).hom (j.stalkMap x).hom
      ((j ≫ f).stalkMap x).hom he).app T ≪≫
    (ModuleCat.restrictScalars (f.stalkMap (j x)).hom).mapIso
      ((restrictModuleStalkIso j x).app M)
  exact (Module.Flat.equiv_iff e.toLinearEquiv).mp h

/-- **Generic flatness** over an affine integral Noetherian base (Nitsure,
arXiv:math/0504590v1, Thm 4.2, p. 19, for `S = Spec A`; Stacks Project, Tag 051R, Lemma
10.118.1, for the ring statement). Let `A` be a Noetherian domain, `f : X ⟶ Spec A` locally
of finite type with `X` quasi-compact, and `F` an affine-locally finite-type quasicoherent
`X`-module. Then there is `a ≠ 0` in `A` such that, at every `x : X` with `f x` in the basic
open `D(a)`, the actual stalk of `F` is flat over the base local ring through `f.stalkMap x`
(the pointwise condition of `relativeFlat`). -/
theorem exists_ne_zero_flat_stalk_of_locallyOfFiniteType {X : Scheme.{u}} {A : CommRingCat.{u}}
    [IsDomain A] [IsNoetherianRing A] (f : X ⟶ Spec A) [LocallyOfFiniteType f] [CompactSpace X]
    (F : X.Modules) (hF : QuasiCoherent.affineLocallyFiniteType X F) :
    ∃ a : A, a ≠ 0 ∧ ∀ x : X, a ∉ (f x).asIdeal →
      Module.Flat ((Spec A).presheaf.stalk (f x))
        ((ModuleCat.restrictScalars (f.stalkMap x).hom).obj ((moduleStalk X x).obj F)) := by
  classical
  -- the ring map attached to an affine open and the generic freeness of its sections
  have key : ∀ W : X.Opens, ∃ a : A, a ≠ 0 ∧ ∀ hW : IsAffineOpen W,
      Module.Free (Localization.Away a) (LocalizedModule.Away a
        ((ModuleCat.restrictScalars ((Scheme.ΓSpecIso A).inv ≫ f.appLE ⊤ W (by simp)).hom).obj
          (moduleSpecΓFunctor.obj (F.restrict hW.fromSpec)))) := by
    intro W
    by_cases hW : IsAffineOpen W
    · let φ : A ⟶ Γ(X, W) := (Scheme.ΓSpecIso A).inv ≫ f.appLE ⊤ W (by simp)
      let := φ.hom.toAlgebra
      have hφ : φ.hom.FiniteType := by
        refine RingHom.FiniteType.comp ?_ (RingHom.FiniteType.of_surjective _
          (Scheme.ΓSpecIso A).commRingCatIsoToRingEquiv.symm.surjective)
        exact HasRingHomProperty.appLE @LocallyOfFiniteType f inferInstance
          ⟨⊤, isAffineOpen_top _⟩ ⟨W, hW⟩ (by simp)
      have : Algebra.FiniteType A Γ(X, W) := hφ
      let E := moduleSpecΓFunctor.obj (F.restrict hW.fromSpec)
      have : Module.Finite Γ(X, W) E := (hF Γ(X, W) hW.fromSpec).2
      let : IsScalarTower A Γ(X, W) ((ModuleCat.restrictScalars φ.hom).obj E) :=
        IsScalarTower.of_algebraMap_smul fun _ _ => rfl
      have : Module.Finite Γ(X, W) ((ModuleCat.restrictScalars φ.hom).obj E) :=
        inferInstanceAs (Module.Finite Γ(X, W) E)
      obtain ⟨a, ha, hfree⟩ := Module.Finite.exists_ne_zero_free_localizedModule_away
        (A := A) (B := Γ(X, W)) ((ModuleCat.restrictScalars φ.hom).obj E)
      exact ⟨a, ha, fun _ => hfree⟩
    · exact ⟨1, one_ne_zero, fun h => absurd h hW⟩
  choose aW haW hfreeW using key
  -- finitely many affine opens cover `X`
  obtain ⟨Us, hUsB, hUsfin, hUs⟩ :=
    X.isBasis_affineOpens.exists_finite_of_isCompact (U := ⊤) isCompact_univ
  refine ⟨∏ W ∈ hUsfin.toFinset, aW W,
    Finset.prod_ne_zero_iff.mpr fun W _ => haW W, fun x hx => ?_⟩
  obtain ⟨W, hWUs, hxW⟩ := (TopologicalSpace.Opens.mem_sSup).mp
    (hUs ▸ (TopologicalSpace.Opens.mem_top x : x ∈ (⊤ : X.Opens)))
  have hW : IsAffineOpen W := hUsB hWUs
  obtain ⟨y, rfl⟩ : x ∈ Set.range hW.fromSpec := hW.range_fromSpec.symm ▸ hxW
  let φ : A ⟶ Γ(X, W) := (Scheme.ΓSpecIso A).inv ≫ f.appLE ⊤ W (by simp)
  have hdvd : aW W ∣ ∏ W ∈ hUsfin.toFinset, aW W :=
    Finset.dvd_prod_of_mem aW (hUsfin.mem_toFinset.mpr hWUs)
  have := hfreeW W hW
  have : Module.Free (Localization.Away (∏ W ∈ hUsfin.toFinset, aW W))
      (LocalizedModule.Away (∏ W ∈ hUsfin.toFinset, aW W)
        ((ModuleCat.restrictScalars φ.hom).obj
          (moduleSpecΓFunctor.obj (F.restrict hW.fromSpec)))) :=
    Module.free_localizedModule_away_of_dvd hdvd
  have hSpec : Spec.map φ = hW.fromSpec ≫ f := SpecMap_affineOpen_baseRingHom f hW
  have hy : φ.hom (∏ W ∈ hUsfin.toFinset, aW W) ∉ y.asIdeal := by
    have : (Spec.map φ) y = f (hW.fromSpec y) := by rw [hSpec]; rfl
    intro h
    apply hx
    rw [← this]
    exact h
  have : (F.restrict hW.fromSpec).IsQuasicoherent := (hF Γ(X, W) hW.fromSpec).1
  have H := flat_stalk_specMap_of_flat_localizedModule_away φ (F.restrict hW.fromSpec)
    (∏ W ∈ hUsfin.toFinset, aW W) y hy
  rw [hSpec] at H
  exact flat_stalk_of_flat_stalk_restrict hW.fromSpec f F y H

-- The `Module` instances on the carriers of `ModuleCat.restrictScalars` objects are identified
-- with those of the original modules only by unfolding below instance transparency.
set_option backward.isDefEq.respectTransparency false in
/-- Generic flatness over an affine integral Noetherian base, in open-set form: there is a
nonempty open `U ⊆ Spec A`, a basic open `D(a)`, over which the actual stalks of `F` are
flat over the base local rings. -/
theorem exists_nonempty_open_flat_stalk_of_locallyOfFiniteType {X : Scheme.{u}}
    {A : CommRingCat.{u}} [IsDomain A] [IsNoetherianRing A] (f : X ⟶ Spec A)
    [LocallyOfFiniteType f] [CompactSpace X] (F : X.Modules)
    (hF : QuasiCoherent.affineLocallyFiniteType X F) :
    ∃ U : (Spec A).Opens, (U : Set (Spec A)).Nonempty ∧ ∀ x : X, f x ∈ U →
      Module.Flat ((Spec A).presheaf.stalk (f x))
        ((ModuleCat.restrictScalars (f.stalkMap x).hom).obj ((moduleStalk X x).obj F)) := by
  obtain ⟨a, ha, h⟩ := exists_ne_zero_flat_stalk_of_locallyOfFiniteType f F hF
  refine ⟨PrimeSpectrum.basicOpen a, ⟨⟨⊥, Ideal.isPrime_bot⟩, ?_⟩, fun x hx => h x hx⟩
  rw [SetLike.mem_coe, PrimeSpectrum.mem_basicOpen]
  simpa using ha

end AlgebraicGeometry.Scheme.Modules
