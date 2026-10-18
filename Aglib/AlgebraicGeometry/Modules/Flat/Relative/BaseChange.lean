/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.Algebra.Category.ModuleCat.ChangeOfRings.BaseChange
public import Aglib.AlgebraicGeometry.Modules.BaseChange.Affine.PullbackSections
public import Aglib.AlgebraicGeometry.Modules.Flat.Relative.OfSections
public import Aglib.AlgebraicGeometry.Modules.QuasiCoherent.Affine.Pullback
public import Aglib.AlgebraicGeometry.Modules.QuasiCoherent.Pullback
public import Mathlib.AlgebraicGeometry.Morphisms.Affine

/-!
# Base change of relative flatness

For a pullback square of schemes
```
X' --g--> X
|q        |p
v         v
S' --f--> S
```
and a quasicoherent `𝒪_X`-module `M` that is flat over `S` (`Scheme.Modules.relativeFlat p M`),
the pullback `g^* M` is flat over `S'` (`relativeFlat_pullback_of_isPullback`). This is the
global ("in particular") statement of Stacks Project, Tag 01U8 (Lemma 29.26.7), in module form;
the pointwise form is not formalized. `relativeFlat_pullback_snd` is the
canonical-pullback form, which for `S = Spec A`, `S' = Spec A'`, `f = Spec.map σ` is the affine
base change along `σ : A ⟶ A'`.

The proof is local and uses only `appTop` maps of affine open subschemes. Around a point of `X'`
choose affine opens `W ⊆ S`, `W' ⊆ f⁻¹ W` and `U ⊆ p⁻¹ W`, and put `V = g⁻¹ U ∩ q⁻¹ W'`. The
restricted square of `resLE` maps is cartesian (`Scheme.Hom.isPullback_resLE`), so `V` is affine
and `Γ(V) = Γ(U) ⊗_{Γ(W)} Γ(W')` (`isPushout_appTop_of_isPullback`). The sections of `g^* M` on
`V` are `Γ(V) ⊗_{Γ(U)} Γ(M, U) ≅ Γ(W') ⊗_{Γ(W)} Γ(M, U)`, flat over `Γ(W')`
(`ModuleCat.flat_extendScalars_of_isPushout`). Relative flatness of affine schemes over affine
targets is flatness of the affine sections (`flat_affineΓFunctor_of_relativeFlat`,
`relativeFlat_of_flat_affineΓFunctor`), and it is unchanged by open immersions of the target
(`relativeFlat_comp_of_isOpenImmersion`, `relativeFlat_of_comp_isOpenImmersion`).
-/

@[expose] public section

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Scheme.Modules

/-- Relative flatness persists after composing the structure morphism with an open immersion,
whose base stalk maps are isomorphisms. The converse is
`relativeFlat_of_comp_isOpenImmersion`. -/
theorem relativeFlat_comp_of_isOpenImmersion {W V Y : Scheme.{u}}
    (b : W ⟶ V) (j : V ⟶ Y) [IsOpenImmersion j] {N : W.Modules}
    (hN : relativeFlat b N) : relativeFlat (b ≫ j) N := by
  intro x
  let T := (moduleStalk W x).obj N
  have hc : ((b ≫ j).stalkMap x).hom =
      (b.stalkMap x).hom.comp (j.stalkMap (b x)).hom :=
    congrArg CommRingCat.Hom.hom (Scheme.Hom.stalkMap_comp b j x)
  let E := (ModuleCat.restrictScalarsComp' (j.stalkMap (b x)).hom (b.stalkMap x).hom
    ((b ≫ j).stalkMap x).hom hc).app T
  let : Module.Flat (V.presheaf.stalk (b x))
      ((ModuleCat.restrictScalars (b.stalkMap x).hom).obj T) := hN x
  have hj : (j.stalkMap (b x)).hom.Flat :=
    RingHom.Flat.of_bijective (ConcreteCategory.bijective_of_isIso (j.stalkMap (b x)))
  exact (Module.Flat.equiv_iff E.toLinearEquiv).mpr
    (flat_restrictScalars (j.stalkMap (b x)).hom hj _)

/-- The affine spectrum square of a morphism of affine schemes, in the order used for relative
flatness: `Spec Γ(X) ≅ X ⟶ Y ≅ Spec Γ(Y)` is `Spec` of the global-section map. -/
private theorem specMap_appTop_eq_isoSpec {X Y : Scheme.{u}} [IsAffine X] [IsAffine Y] (f : X ⟶ Y) :
    Spec.map f.appTop = (X.isoSpec.inv ≫ f) ≫ Y.isoSpec.hom := by
  rw [Category.assoc, ← Scheme.isoSpec_hom_naturality, Iso.inv_hom_id_assoc]

/-- For a morphism of affine schemes `π : U ⟶ Y` and a quasicoherent `𝒪_U`-module `N` that is
relatively flat over `Y`, the affine sections of `N` are flat over `Γ(Y, ⊤)` through
`π.appTop`. -/
theorem flat_affineΓFunctor_of_relativeFlat {U Y : Scheme.{u}} [IsAffine U] [IsAffine Y]
    (π : U ⟶ Y) (N : U.Modules) [N.IsQuasicoherent] (hN : relativeFlat π N) :
    Module.Flat Γ(Y, ⊤)
      ((ModuleCat.restrictScalars π.appTop.hom).obj ((affineΓFunctor U).obj N)) := by
  let : ((pushforward U.isoSpec.hom).obj N).IsQuasicoherent :=
    isQuasicoherent_pushforward_of_isIso U.isoSpec.hom N
  have h₁ : relativeFlat ((U.isoSpec.inv ≫ π) ≫ Y.isoSpec.hom) (N.restrict U.isoSpec.inv) :=
    relativeFlat_comp_of_isOpenImmersion _ Y.isoSpec.hom
      (relativeFlat_restrict U.isoSpec.inv π hN)
  rw [← specMap_appTop_eq_isoSpec] at h₁
  exact flat_moduleSpecΓFunctor_of_relativeFlat π.appTop ((pushforward U.isoSpec.hom).obj N)
    (relativeFlat_of_iso _ ((pushforwardIsoRestrict U.isoSpec).app N) h₁)

/-- For a morphism of affine schemes `π : V ⟶ Y` and a quasicoherent `𝒪_V`-module `N` whose
affine sections are flat over `Γ(Y, ⊤)` through `π.appTop`, `N` is relatively flat over `Y`. -/
theorem relativeFlat_of_flat_affineΓFunctor {V Y : Scheme.{u}} [IsAffine V] [IsAffine Y]
    (π : V ⟶ Y) (N : V.Modules) [N.IsQuasicoherent]
    (hN : Module.Flat Γ(Y, ⊤)
      ((ModuleCat.restrictScalars π.appTop.hom).obj ((affineΓFunctor V).obj N))) :
    relativeFlat π N := by
  let : ((pushforward V.isoSpec.hom).obj N).IsQuasicoherent :=
    isQuasicoherent_pushforward_of_isIso V.isoSpec.hom N
  have h₁ : relativeFlat (Spec.map π.appTop) (N.restrict V.isoSpec.inv) :=
    relativeFlat_of_iso _ ((pushforwardIsoRestrict V.isoSpec).app N).symm
      (relativeFlat_specMap_of_flat π.appTop ((pushforward V.isoSpec.hom).obj N) hN)
  rw [specMap_appTop_eq_isoSpec] at h₁
  have h₂ := relativeFlat_of_comp_isOpenImmersion _ Y.isoSpec.hom h₁
  intro x
  obtain ⟨y, rfl⟩ : ∃ y, V.isoSpec.inv y = x := ⟨V.isoSpec.hom x, Scheme.hom_inv_apply _ x⟩
  exact flat_stalk_of_flat_stalk_restrict V.isoSpec.inv π N y (h₂ y)

/-- **Relative flatness between affine schemes is flatness of the affine sections**: for a
morphism of affine schemes `π : U ⟶ Y` and a quasicoherent `𝒪_U`-module `N`, `N` is relatively
flat over `Y` if and only if its affine sections are flat over `Γ(Y, ⊤)` through `π.appTop`. -/
theorem relativeFlat_iff_flat_affineΓFunctor {U Y : Scheme.{u}} [IsAffine U] [IsAffine Y]
    (π : U ⟶ Y) (N : U.Modules) [N.IsQuasicoherent] :
    relativeFlat π N ↔ Module.Flat Γ(Y, ⊤)
      ((ModuleCat.restrictScalars π.appTop.hom).obj ((affineΓFunctor U).obj N)) :=
  ⟨flat_affineΓFunctor_of_relativeFlat π N, relativeFlat_of_flat_affineΓFunctor π N⟩

/-- **Base change of relative flatness** (Stacks Project, Tag 01U8, Lemma 29.26.7, the global
("in particular") statement, for a quasicoherent module). For a pullback square
`g ≫ p = q ≫ f` of schemes and a quasicoherent `𝒪_X`-module `M` flat over `S`
(`relativeFlat p M`), the pullback `g^* M` is flat over `S'`. -/
theorem relativeFlat_pullback_of_isPullback {X X' S S' : Scheme.{u}} {g : X' ⟶ X}
    {q : X' ⟶ S'} {p : X ⟶ S} {f : S' ⟶ S} (h : IsPullback g q p f) (M : X.Modules)
    [M.IsQuasicoherent] (hM : relativeFlat p M) :
    relativeFlat q ((Scheme.Modules.pullback g).obj M) := by
  intro x'
  obtain ⟨W, hW, hxW⟩ : ∃ W : S.Opens, IsAffineOpen W ∧ f (q x') ∈ W := by
    obtain ⟨_, ⟨W, hW, rfl⟩, hxW, -⟩ :=
      S.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ (f (q x'))) isOpen_univ
    exact ⟨W, hW, hxW⟩
  obtain ⟨W', hW', hxW', hW'W⟩ :
      ∃ W' : S'.Opens, IsAffineOpen W' ∧ q x' ∈ W' ∧ W' ≤ f ⁻¹ᵁ W := by
    obtain ⟨_, ⟨W', hW', rfl⟩, hxW', hW'W⟩ :=
      S'.isBasis_affineOpens.exists_subset_of_mem_open
        (show q x' ∈ ((f ⁻¹ᵁ W : S'.Opens) : Set S') from hxW) (f ⁻¹ᵁ W).isOpen
    exact ⟨W', hW', hxW', hW'W⟩
  have hgx : g x' ∈ p ⁻¹ᵁ W := by
    change p (g x') ∈ W
    rw [← Scheme.Hom.comp_apply, h.w, Scheme.Hom.comp_apply]
    exact hxW
  obtain ⟨U, hU, hxU, hUW⟩ : ∃ U : X.Opens, IsAffineOpen U ∧ g x' ∈ U ∧ U ≤ p ⁻¹ᵁ W := by
    obtain ⟨_, ⟨U, hU, rfl⟩, hxU, hUW⟩ :=
      X.isBasis_affineOpens.exists_subset_of_mem_open hgx (p ⁻¹ᵁ W).isOpen
    exact ⟨U, hU, hxU, hUW⟩
  obtain ⟨V, hV⟩ : ∃ V : X'.Opens, V = g ⁻¹ᵁ U ⊓ q ⁻¹ᵁ W' := ⟨_, rfl⟩
  have hxV : x' ∈ V := by
    rw [hV]
    exact ⟨hxU, hxW'⟩
  have hVU : V ≤ g ⁻¹ᵁ U := hV.trans_le inf_le_left
  have hVW' : V ≤ q ⁻¹ᵁ W' := hV.trans_le inf_le_right
  have : IsAffine U.toScheme := hU
  have : IsAffine W.toScheme := hW
  have : IsAffine W'.toScheme := hW'
  have hpb : IsPullback (g.resLE U V hVU) (q.resLE W' V hVW') (p.resLE W U hUW)
      (f.resLE W W' hW'W) := Scheme.Hom.isPullback_resLE h hW'W hUW hV
  have : IsAffine V.toScheme := IsAffine.of_isPullback hpb
  have hpo := isPushout_appTop_of_isPullback hpb
  -- the source module on `U` is relatively flat over `W`
  let MU := M.restrict U.ι
  let : MU.IsQuasicoherent := isQuasicoherent_restrictFunctor U.ι M
  have hMU : relativeFlat (p.resLE W U hUW) MU := by
    have h₀ := relativeFlat_restrict U.ι p hM
    rw [← Scheme.Hom.resLE_comp_ι p hUW] at h₀
    exact relativeFlat_of_comp_isOpenImmersion _ W.ι h₀
  have hE := flat_affineΓFunctor_of_relativeFlat (p.resLE W U hUW) MU hMU
  have hF := ModuleCat.flat_extendScalars_of_isPushout (p.resLE W U hUW).appTop
    (f.resLE W W' hW'W).appTop (g.resLE U V hVU).appTop (q.resLE W' V hVW').appTop hpo.flip
    ((affineΓFunctor U).obj MU) hE
  -- the sections of the pulled-back module on `V`
  let N := ((Scheme.Modules.pullback g).obj M).restrict V.ι
  let : N.IsQuasicoherent := isQuasicoherent_restrictFunctor V.ι _
  let e₁ := affinePullbackSectionsIso (g.resLE U V hVU) MU
  let e₂ := (pullbackOpenSquare V.ι (g.resLE U V hVU) g U.ι
    (Scheme.Hom.resLE_comp_ι g hVU).symm).app M
  let e := (ModuleCat.restrictScalars (q.resLE W' V hVW').appTop.hom).mapIso
    (e₁ ≪≫ (affineΓFunctor V.toScheme).mapIso e₂.symm)
  have hG : Module.Flat Γ(W', ⊤) ((ModuleCat.restrictScalars (q.resLE W' V hVW').appTop.hom).obj
      ((affineΓFunctor V.toScheme).obj N)) :=
    (Module.Flat.equiv_iff e.toLinearEquiv).mp hF
  have hN := relativeFlat_comp_of_isOpenImmersion _ W'.ι
    (relativeFlat_of_flat_affineΓFunctor (q.resLE W' V hVW') N hG)
  rw [Scheme.Hom.resLE_comp_ι] at hN
  exact flat_stalk_of_flat_stalk_restrict V.ι q _ ⟨x', hxV⟩ (hN ⟨x', hxV⟩)

/-- **Base change of relative flatness along the canonical pullback** (Stacks Project, Tag 01U8,
the global statement):
for `p : X ⟶ S`, `f : S' ⟶ S` and a quasicoherent `𝒪_X`-module `M` flat over `S`, the pullback
of `M` to `X ×_S S'` is flat over `S'`. For `S = Spec A`, `S' = Spec A'` and `f = Spec.map σ` this
is the affine base change of the family `M` along `σ : A ⟶ A'`. -/
theorem relativeFlat_pullback_snd {X S S' : Scheme.{u}} (p : X ⟶ S) (f : S' ⟶ S)
    (M : X.Modules) [M.IsQuasicoherent] (hM : relativeFlat p M) :
    relativeFlat (pullback.snd p f) ((Scheme.Modules.pullback (pullback.fst p f)).obj M) :=
  relativeFlat_pullback_of_isPullback (IsPullback.of_hasPullback p f) M hM

end AlgebraicGeometry.Scheme.Modules
