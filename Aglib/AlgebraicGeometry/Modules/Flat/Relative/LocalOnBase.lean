/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Modules.Flat.Relative.BaseChange
public import Aglib.AlgebraicGeometry.Modules.Flat.Generic.Spec

/-!
# Relative flatness of a base change is local on the new base

Let `p : X ⟶ S` be a morphism of schemes, `M` an `𝒪_X`-module and `g : T ⟶ S`, and let
`X_T` be a pullback of `p` along `g` (any square `IsPullback a b p g`), with `M_T = a^* M`.

* `relativeFlat_of_isPullback_comp`: if `M_T` is flat over `T`, then for any `j : U ⟶ T` and any
  pullback square of `p` along `j ≫ g`, the pullback of `M` to it is flat over `U` (pasting of
  pullback squares and base change of relative flatness, `relativeFlat_pullback_of_isPullback`).
* `relativeFlat_of_isPullback_of_forall_exists`: conversely, `M_T` is flat over `T` as soon as
  every point of `T` lies in the image of an open immersion `j : U ⟶ T` over which the pullback
  of `M` (to some pullback square of `p` along `j ≫ g`) is flat. Relative flatness is a stalkwise
  condition, and the induced map from the square over `U` to `X_T` is an open immersion.

Together they say that flatness of the base change of a fixed family is local on the new base,
in the form used by the proof of Nitsure, *Construction of Hilbert and Quot schemes*,
arXiv:math/0504590v1, Thm 4.3 (ii), p. 22.
-/

@[expose] public section

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Scheme.Modules

/-- **Restriction of a flat base change along a further base change.** For a pullback square
`IsPullback a b p g`, a morphism `j : U ⟶ T` and a pullback square `IsPullback a' b' p (j ≫ g)`,
if `a^* M` is flat over `T` then `a'^* M` is flat over `U`. -/
theorem relativeFlat_of_isPullback_comp {X S T XT U XU : Scheme.{u}} {p : X ⟶ S} {g : T ⟶ S}
    {a : XT ⟶ X} {b : XT ⟶ T} (hsq : IsPullback a b p g) {j : U ⟶ T} {a' : XU ⟶ X}
    {b' : XU ⟶ U} (hsq' : IsPullback a' b' p (j ≫ g)) (M : X.Modules) [M.IsQuasicoherent]
    (hM : relativeFlat b ((Scheme.Modules.pullback a).obj M)) :
    relativeFlat b' ((Scheme.Modules.pullback a').obj M) := by
  obtain ⟨k, hka, hk⟩ : ∃ k : XU ⟶ XT, k ≫ a = a' ∧ IsPullback k b' b j :=
    ⟨_, hsq.lift_fst _ _ _, IsPullback.of_right' hsq' hsq⟩
  exact relativeFlat_of_iso b'
    (((Scheme.Modules.pullbackCongr hka).app M).symm ≪≫
      ((Scheme.Modules.pullbackComp k a).app M).symm)
    (relativeFlat_pullback_of_isPullback hk _ hM)

/-- **Relative flatness of a base change is local on the new base.** For a pullback square
`IsPullback a b p g`, if every point of `T` lies in the image of an open immersion `j : U ⟶ T`
admitting a pullback square `IsPullback a' b' p (j ≫ g)` with `a'^* M` flat over `U`, then
`a^* M` is flat over `T`. -/
theorem relativeFlat_of_isPullback_of_forall_exists {X S T XT : Scheme.{u}} {p : X ⟶ S}
    {g : T ⟶ S} {a : XT ⟶ X} {b : XT ⟶ T} (hsq : IsPullback a b p g) (M : X.Modules)
    (H : ∀ t : T, ∃ (U : Scheme.{u}) (j : U ⟶ T) (_ : IsOpenImmersion j) (_ : t ∈ Set.range j)
      (XU : Scheme.{u}) (a' : XU ⟶ X) (b' : XU ⟶ U),
      IsPullback a' b' p (j ≫ g) ∧ relativeFlat b' ((Scheme.Modules.pullback a').obj M)) :
    relativeFlat b ((Scheme.Modules.pullback a).obj M) := by
  intro x
  obtain ⟨U, j, hj, ⟨u, hu⟩, XU, a', b', hsq', hflat⟩ := H (b x)
  obtain ⟨k, hka, hkb, hk⟩ :
      ∃ k : XU ⟶ XT, k ≫ a = a' ∧ k ≫ b = b' ≫ j ∧ IsPullback k b' b j :=
    ⟨_, hsq.lift_fst _ _ _, hsq.lift_snd _ _ _, IsPullback.of_right' hsq' hsq⟩
  have : IsOpenImmersion k := MorphismProperty.of_isPullback (P := @IsOpenImmersion) hk.flip hj
  obtain ⟨z, rfl⟩ : ∃ z : XU, k z = x := by
    obtain ⟨w, hw₁, -⟩ := Scheme.Pullback.exists_preimage_pullback x u hu.symm
    refine ⟨hk.isoPullback.inv w, ?_⟩
    rw [← Scheme.Hom.comp_apply, hk.isoPullback_inv_fst, hw₁]
  have h₁ := relativeFlat_comp_of_isOpenImmersion b' j hflat
  rw [← hkb] at h₁
  have h₂ : relativeFlat (k ≫ b) (((Scheme.Modules.pullback a).obj M).restrict k) :=
    relativeFlat_of_iso _ ((Scheme.Modules.restrictFunctorIsoPullback k).app _ ≪≫
      (Scheme.Modules.pullbackComp k a).app M ≪≫ (Scheme.Modules.pullbackCongr hka).app M) h₁
  exact flat_stalk_of_flat_stalk_restrict k b _ z (h₂ z)

end AlgebraicGeometry.Scheme.Modules
