/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Picard.Comparison.Injectivity
public import Aglib.AlgebraicGeometry.Modules.ProjectionFormula.PushforwardTensorPullback
public import Aglib.AlgebraicGeometry.Modules.Invertible.FibrewiseIsomorphism
public import Aglib.AlgebraicGeometry.Modules.Invertible.FieldMaps
public import Aglib.AlgebraicGeometry.Modules.Invertible.Nonzero
public import Aglib.AlgebraicGeometry.Modules.Invertible.Affine
public import Aglib.AlgebraicGeometry.Cohomology.BaseChange.Relative
public import Aglib.CategoryTheory.Adjunction.Unit
public import Mathlib.AlgebraicGeometry.Geometrically.Integral

/-!
# Pullback along a geometrically integral family is fully faithful on line bundles

Let `p : X ⟶ S` be proper and flat with geometrically integral fibres over a locally Noetherian
`S`, `g : T ⟶ S` arbitrary and `q = pullback.snd p g : X ×_S T ⟶ T`. For a line bundle `N` on `T`:

* `isLocallyRankOne_pushforward_pullback_snd_of_isProper_of_flat_of_geometricallyIntegral`:
  `q_* q^* N` is a line bundle, since `q_*(𝒪 ⊗ q^* N) ≅ q_* 𝒪 ⊗ N` (the degree-zero projection
  formula) and `q_* 𝒪 ≅ 𝒪_T`
  (universal `𝒪`-connectedness,
  `isIso_unit_app_unit_pullback_snd_of_isProper_of_flat_of_geometricallyIntegral`);
* `isIso_unit_app_pullback_snd_of_isLocallyRankOne_of_isProper_of_flat_of_geometricallyIntegral`:
  the unit `N ⟶ q_* q^* N` is an isomorphism.
  It is a map of line bundles that is nonzero at every field point of `T`, because the identity
  of the line bundle `q^* N` is nonzero on every (integral, nonempty) fibre
  (`adjoint_pullback_ne_zero`), and such a map is an isomorphism
  (`lineBundleMap_isIso_of_geometricPullback_isIso`);
* `bijective_pullback_snd_map_of_isLocallyRankOne_of_isProper_of_flat_of_geometricallyIntegral`:
  hence `q^*` is bijective on maps into a line bundle.

This is Kleiman, *The Picard scheme*, arXiv:math/0504020v1, Lemma 2.7 (p. 18; `f^* N ≅ f^* N'`
implies `N ≅ N'`) in the form used in the proof of Thm 3.13 (p. 25: `N` is determined up to
isomorphism, and a second choice of `σ` changes it by a unit). Main's
`bijective_familyPullback_map_of_isProper_of_flat_of_geometricallyIntegral` is the case of a
trivial target.
-/

@[expose] public section

noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

open CategoryTheory Limits AlgebraicGeometry

namespace AlgebraicGeometry.Scheme.Modules.Invertible

variable {X S T : Scheme.{u}} (p : X ⟶ S) [IsLocallyNoetherian S] [IsProper p] [Flat p]
  [GeometricallyIntegral p] (g : T ⟶ S)

/-- The direct image of the pullback of a line bundle along the base-changed family is a line
bundle: `q_* q^* N ≅ q_* 𝒪 ⊗ N ≅ N`. -/
theorem isLocallyRankOne_pushforward_pullback_snd_of_isProper_of_flat_of_geometricallyIntegral
    (N : T.Modules) (hN : IsLocallyRankOne T N) :
    IsLocallyRankOne T ((pushforward (Limits.pullback.snd p g)).obj
      ((Scheme.Modules.pullback (Limits.pullback.snd p g)).obj N)) := by
  let q := Limits.pullback.snd p g
  have : IsFiniteLocallyFree T N := isFiniteLocallyFree_of_isLocallyRankOne hN
  have := isIso_unit_app_unit_pullback_snd_of_isProper_of_flat_of_geometricallyIntegral p g
  let eO : (pushforward q).obj (SheafOfModules.unit (Limits.pullback p g).ringCatSheaf) ≅
      SheafOfModules.unit T.ringCatSheaf :=
    (asIso ((pullbackPushforwardAdjunction q).unit.app (SheafOfModules.unit T.ringCatSheaf)) ≪≫
      (pushforward q).mapIso (pullbackUnitIso q)).symm
  let e : (pushforward q).obj ((Scheme.Modules.pullback q).obj N) ≅ N :=
    (pushforward q).mapIso
        (tensorSheafLeftUnit (Limits.pullback p g) ((Scheme.Modules.pullback q).obj N)).symm ≪≫
      pushforwardTensorPullbackIso q (SheafOfModules.unit (Limits.pullback p g).ringCatSheaf) N ≪≫
      tensorSheafIso T eO (Iso.refl N) ≪≫ tensorSheafLeftUnit T N
  exact isLocallyRankOne_of_iso T e.symm hN

/-- **The unit of the pullback adjunction is an isomorphism on line bundles** (Kleiman,
Lemma 2.7). -/
theorem isIso_unit_app_pullback_snd_of_isLocallyRankOne_of_isProper_of_flat_of_geometricallyIntegral
    (N : T.Modules) (hN : IsLocallyRankOne T N) :
    IsIso ((pullbackPushforwardAdjunction (Limits.pullback.snd p g)).unit.app N) := by
  let q := Limits.pullback.snd p g
  have hM :=
    isLocallyRankOne_pushforward_pullback_snd_of_isProper_of_flat_of_geometricallyIntegral p g N hN
  have hne (K : Type u) [Field K] (t : Spec (.of K) ⟶ T) :
      (Scheme.Modules.pullback t).map ((pullbackPushforwardAdjunction q).unit.app N) ≠ 0 := by
    have : IsIntegral (Limits.pullback q t) :=
      GeometricallyIntegral.geometrically_isIntegral t _ _ (IsPullback.of_hasPullback q t)
    have h := Cohomology.adjoint_pullback_ne_zero q t (𝟙 ((Scheme.Modules.pullback q).obj N))
      (by
        rw [CategoryTheory.Functor.map_id]
        exact lineBundle_id_ne_zero (Limits.pullback q t)
          (pullbackLineBundle (Limits.pullback.fst q t) (pullbackLineBundle q ⟨N, hN⟩)))
    rwa [Adjunction.homEquiv_id] at h
  exact lineBundleMap_isIso_of_geometricPullback_isIso ⟨N, hN⟩ ⟨_, hM⟩ _
    (fun K _ _ t ↦ fieldLineBundleMap_isIso_of_ne_zero K (pullbackLineBundle t ⟨N, hN⟩)
      (pullbackLineBundle t ⟨_, hM⟩) _ (hne K t))

/-- **Pullback along the base-changed family is bijective on maps into a line bundle**:
for a line bundle `N'` on `T` and any `N`, `φ ↦ q^* φ` is a bijection
`(N ⟶ N') → (q^* N ⟶ q^* N')`. -/
theorem bijective_pullback_snd_map_of_isLocallyRankOne_of_isProper_of_flat_of_geometricallyIntegral
    (N N' : T.Modules) (hN' : IsLocallyRankOne T N') :
    Function.Bijective
      (fun φ : N ⟶ N' ↦ (Scheme.Modules.pullback (Limits.pullback.snd p g)).map φ) := by
  have :=
    isIso_unit_app_pullback_snd_of_isLocallyRankOne_of_isProper_of_flat_of_geometricallyIntegral
      p g N' hN'
  exact (pullbackPushforwardAdjunction (Limits.pullback.snd p g)).bijective_map_of_isIso_unit_app
    N N'

end AlgebraicGeometry.Scheme.Modules.Invertible
