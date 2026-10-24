/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Picard.LinearSystem.Evaluation
public import Aglib.AlgebraicGeometry.EffectiveCartierDivisor.Relative.ZeroScheme
public import Aglib.AlgebraicGeometry.Modules.LocallyFree.LineSubbundle
public import Aglib.AlgebraicGeometry.Grassmannian.LocallyFree.KernelRank
public import Aglib.AlgebraicGeometry.Modules.Invertible.Nonzero
public import Aglib.AlgebraicGeometry.Modules.Invertible.ZeroLocus.Uniqueness

/-!
# The divisor of a line subbundle of `E_T`

Let `p : X ⟶ S`, `L` a line bundle on `X` and `E = p_* L`. For `T` over `S`, with
`g_T : X_T ⟶ X` and `q_T : X_T ⟶ T`, a map `u : N ⟶ E_T` defines the section
`subbundleSection p L T u = q_T^* u ≫ ev_T : q_T^* N ⟶ g_T^* L`, and its pairing with `L^∨`,
`subbundlePairing p L T u : q_T^* N ⊗ g_T^* L^∨ ⟶ 𝒪_{X_T}`. The **divisor of `u`**,
`subbundleDivisor p L T u`, is the zero scheme of this section: the image ideal of the pairing.

* `subbundleSection_ne_zero`: if the base-change map of `L` along `T ⟶ S` is an isomorphism,
  the section of a nonzero `u` is nonzero. For `T = Spec K` this is "a section of `E ⊗ K` that is
  nonzero is nonzero on `X_K`". The fibre form is `pullback_fst_map_subbundleSection_ne_zero`:
  if `u` is nonzero at `v : V ⟶ T`, the section is nonzero on `X_T ×_T V`.
* `isLinearSystemDivisor_subbundleDivisor`: for `p` flat, locally of finite presentation and
  geometrically integral, every base-change map of `L` an isomorphism, `N` a line bundle and `u`
  nonzero on every field fibre (a line subbundle with locally free quotient, by
  `LineSubbundle`), the divisor of `u` is a relative effective Cartier divisor of `X_T ⟶ T`
  whose ideal is `q_T^* N ⊗ g_T^* L^∨` (`subbundleDivisorIdealIso`); that is,
  `O(D) ≅ L_T ⊗ q_T^* N^∨`.
* `quotientDivisor p L T P`: for a point `P : E_T ↠ Q` of `Gr(E, k)` over `T`, with `E` of
  constant rank `k + 1`, the divisor of the kernel `ker P ↪ E_T`, a line subbundle
  (`isLinearSystemDivisor_quotientDivisor`); it depends only on the isomorphism class of `P`
  (`quotientDivisor_eq_of_isoUnder`).

Supporting lemmas: `pullback_map_pullbackPairingOf_eq_zero_iff` (a perfect pairing vanishes after
pullback exactly when its map does) and `pullback_fst_map_idealInclusion_ne_zero` (the ideal of a
relative effective Cartier divisor is nonzero on every integral fibre).

Sources: Kleiman, *The Picard scheme*, arXiv:math/0504020v1, Def. 3.12, p. 25, and the proof of
Thm 3.13, pp. 25–26 (the section `σ` of `L_T ⊗ f^* N` defined by a quotient `u : Q_T ↠ N`,
`Q = E^∨`, nonzero on the fibres, and its divisor, by Lemma 3.4, p. 22); Ex. 3.14, p. 26. The line
subbundle `N^{-1} ⟶ E_T` used here is dual to Kleiman's `u`, so `O(D) ≅ L_T ⊗ f^* N` in his
notation.
-/

@[expose] public section

noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

open CategoryTheory Limits

namespace AlgebraicGeometry.Scheme.Modules

variable {X P : Scheme.{u}} (p : X ⟶ P) {N L : P.Modules}

/-- The pairing of the zero map is zero. -/
theorem pullbackPairingOf_zero
    (ε : (show P.Modules from tensorSheaf P N L) ⟶
      (show P.Modules from SheafOfModules.unit P.ringCatSheaf)) (M : X.Modules) :
    pullbackPairingOf p ε (0 : M ⟶ (pullback p).obj N) = 0 := by
  simp only [pullbackPairingOf]
  rw [Invertible.tensorSheafMap_zero_left, zero_comp]

/-- **A perfect pairing vanishes exactly where its map does**: for an isomorphism
`ε : N ⊗ L ⟶ 𝒪_P` with `L` a line bundle, the pullback along any `b` of
`pullbackPairingOf p ε j` is zero exactly when the pullback of `j` is. -/
theorem pullback_map_pullbackPairingOf_eq_zero_iff
    (ε : (show P.Modules from tensorSheaf P N L) ⟶
      (show P.Modules from SheafOfModules.unit P.ringCatSheaf)) [IsIso ε]
    (hL : Invertible.IsLocallyRankOne P L) {M : X.Modules} (j : M ⟶ (pullback p).obj N)
    {X' : Scheme.{u}} (b : X' ⟶ X) :
    (pullback b).map (pullbackPairingOf p ε j) = 0 ↔ (pullback b).map j = 0 := by
  constructor
  · intro h
    have key := pullbackPairingOf_pullback p b (b ≫ p) rfl ε j (𝟙 _)
      ((pullback b).map j ≫ (pullbackComp b p).hom.app N) (by simp [pullbackCongr])
    rw [h, zero_comp, comp_zero, comp_zero] at key
    have h0 := (bijective_pullbackPairingOf (b ≫ p) ε hL _).1
      (key.symm.trans (pullbackPairingOf_zero (b ≫ p) ε _).symm)
    exact (cancel_mono ((pullbackComp b p).hom.app N)).mp (h0.trans zero_comp.symm)
  · intro h
    have h1 := pullbackTensorMapIso_inv_naturality b j (𝟙 ((pullback p).obj L))
    rw [h, Invertible.tensorSheafMap_zero_left, zero_comp] at h1
    have h2 : (pullback b).map (tensorSheafMap X j (𝟙 ((pullback p).obj L))) = 0 :=
      (cancel_epi (pullbackTensorMapIso b _ _).inv).mp (h1.trans comp_zero.symm)
    simp only [pullbackPairingOf]
    rw [CategoryTheory.Functor.map_comp, h2, zero_comp]

end AlgebraicGeometry.Scheme.Modules

namespace AlgebraicGeometry.Scheme.LinearSystem

open Scheme.Modules Scheme.Modules.Invertible Scheme.RelativePicard

/-- **The ideal of a relative effective Cartier divisor is nonzero on integral fibres**: for a
relative effective Cartier divisor `i : D ⟶ Y` of `q : Y ⟶ T` and any `v : V ⟶ T` with
`Y ×_T V` integral, the pullback of the ideal inclusion `I_D ⟶ 𝒪_Y` to `Y ×_T V` is nonzero.
Its ideal pulls back to the ideal of the fibre divisor (flatness), which is a line bundle. -/
theorem pullback_fst_map_idealInclusion_ne_zero {D Y T V : Scheme.{u}} {i : D ⟶ Y}
    {q : Y ⟶ T} (hD : Scheme.Hom.IsRelativeEffectiveCartier i q) (v : V ⟶ T)
    [IsIntegral (Limits.pullback q v)] :
    (Scheme.Modules.pullback (Limits.pullback.fst q v)).map (Scheme.Hom.idealInclusion i) ≠ 0 := by
  intro h0
  have H := IsPullback.of_hasPullback q v
  have H' := IsPullback.of_hasPullback i (Limits.pullback.fst q v)
  have hD' := hD.of_isPullback H H'
  have := hD.isClosedImmersion
  have := hD.flat
  have := Scheme.Hom.flatQuotient_idealPullbackMap_isIso q v (Limits.pullback.snd q v)
    (Limits.pullback.fst q v) i _ _ H'.w H H'
  have hinc := Scheme.Hom.idealPullbackMap_inclusion i _ (Limits.pullback.fst q v) _ H'.w
  rw [h0, zero_comp] at hinc
  exact lineBundleMap_ne_zero_of_mono (Limits.pullback q v) ⟨_, hD'.isLocallyRankOne⟩ _
    ((cancel_epi _).mp (hinc.trans comp_zero.symm))

variable {X S : Scheme.{u}} (p : X ⟶ S) (L : LineBundle X)

/-- **The section defined by a map into `E_T`**: for `u : N ⟶ E_T`, the composite
`q_T^* N ⟶ q_T^* E_T ⟶ g_T^* L` of `q_T^* u` and the evaluation map. For `N = 𝒪_T` it is the
section of `L_T` defined by a section of `E_T`. -/
def subbundleSection (T : Over S) {N : T.left.Modules}
    (u : N ⟶ overPullback ((pushforward p).obj L.val) T) :
    (Scheme.Modules.pullback (Limits.pullback.snd p T.hom)).obj N ⟶
      (Scheme.Modules.pullback (Limits.pullback.fst p T.hom)).obj L.val :=
  (Scheme.Modules.pullback (Limits.pullback.snd p T.hom)).map u ≫ evaluationMap p L T

/-- The adjoint of the section of `u` is `u` followed by the base-change map. -/
theorem homEquiv_subbundleSection (T : Over S) {N : T.left.Modules}
    (u : N ⟶ overPullback ((pushforward p).obj L.val) T) :
    (pullbackPushforwardAdjunction (Limits.pullback.snd p T.hom)).homEquiv _ _
      (subbundleSection p L T u) = u ≫ familyBaseChangeMap p L T := by
  rw [subbundleSection, Adjunction.homEquiv_naturality_left, homEquiv_evaluationMap]

/-- **A nonzero section of `E_T` is nonzero on `X_T`**: if the base-change map of `L` along
`T ⟶ S` is an isomorphism, the section defined by a nonzero `u : N ⟶ E_T` is nonzero. For
`T = Spec K`: a section of `E ⊗ K` that is nonzero is nonzero on `X_K`. -/
theorem subbundleSection_ne_zero (T : Over S)
    (hbc : IsIso (moduleBaseChangeMap p T.hom L.val)) {N : T.left.Modules}
    (u : N ⟶ overPullback ((pushforward p).obj L.val) T) (hu : u ≠ 0) :
    subbundleSection p L T u ≠ 0 := by
  intro h
  apply hu
  have h1 := homEquiv_subbundleSection p L T u
  have h2 : (pullbackPushforwardAdjunction (Limits.pullback.snd p T.hom)).homEquiv N
      ((Scheme.Modules.pullback (Limits.pullback.fst p T.hom)).obj L.val) 0 = 0 := by
    rw [Adjunction.homEquiv_unit, CategoryTheory.Functor.map_zero, comp_zero]
  rw [h, h2] at h1
  have : IsIso (familyBaseChangeMap p L T) := by
    rw [familyBaseChangeMap_eq]
    exact hbc
  exact (cancel_mono (familyBaseChangeMap p L T)).mp (h1.symm.trans zero_comp.symm)

/-- **Fibre nonvanishing of the section**: if every base-change map of `L` is an isomorphism and
`u : N ⟶ E_T` is nonzero after pullback along `v : V ⟶ T`, the section of `u` is nonzero on
`X_T ×_T V`. -/
theorem pullback_fst_map_subbundleSection_ne_zero
    (hbc : ∀ (T : Scheme.{u}) (g : T ⟶ S), IsIso (moduleBaseChangeMap p g L.val))
    (T : Over S) {N : T.left.Modules} (u : N ⟶ overPullback ((pushforward p).obj L.val) T)
    {V : Scheme.{u}} (v : V ⟶ T.left) (hu : (Scheme.Modules.pullback v).map u ≠ 0) :
    (Scheme.Modules.pullback (Limits.pullback.fst (Limits.pullback.snd p T.hom) v)).map
      (subbundleSection p L T u) ≠ 0 := by
  refine pullback_fst_map_ne_zero_of_pullback_map_homEquiv_ne_zero p L hbc T _ v ?_
  rw [homEquiv_subbundleSection, CategoryTheory.Functor.map_comp]
  have : IsIso (familyBaseChangeMap p L T) := by
    rw [familyBaseChangeMap_eq]
    exact hbc _ _
  intro h
  exact hu ((cancel_mono _).mp (h.trans zero_comp.symm))

/-- **The pairing of `u`**: `q_T^* N ⊗ g_T^* L^∨ ⟶ 𝒪_{X_T}`, the section of `u` paired with
`L^∨` through the evaluation pairing of `L`. -/
def subbundlePairing (T : Over S) {N : T.left.Modules}
    (u : N ⟶ overPullback ((pushforward p).obj L.val) T) :
    (show (Limits.pullback p T.hom).Modules from tensorSheaf (Limits.pullback p T.hom)
      ((Scheme.Modules.pullback (Limits.pullback.snd p T.hom)).obj N)
      ((Scheme.Modules.pullback (Limits.pullback.fst p T.hom)).obj (dualLineBundle X L).val)) ⟶
    (show (Limits.pullback p T.hom).Modules from
      SheafOfModules.unit (Limits.pullback p T.hom).ringCatSheaf) :=
  pullbackPairingOf (Limits.pullback.fst p T.hom) (evaluationPairing L) (subbundleSection p L T u)

/-- **The divisor of a map `u : N ⟶ E_T`** (Kleiman, proof of Thm 3.13, p. 25): the zero scheme
of the section of `u`, as the image ideal of its pairing with `L^∨`. -/
def subbundleDivisor (T : Over S) {N : T.left.Modules}
    (u : N ⟶ overPullback ((pushforward p).obj L.val) T) :
    (Limits.pullback p T.hom).IdealSheafData :=
  Hom.imageIdealData (subbundlePairing p L T u)

/-- The pairing of `u` vanishes after a pullback exactly when the section of `u` does. -/
theorem pullback_map_subbundlePairing_eq_zero_iff (T : Over S) {N : T.left.Modules}
    (u : N ⟶ overPullback ((pushforward p).obj L.val) T) {V : Scheme.{u}}
    (b : V ⟶ Limits.pullback p T.hom) :
    (Scheme.Modules.pullback b).map (subbundlePairing p L T u) = 0 ↔
      (Scheme.Modules.pullback b).map (subbundleSection p L T u) = 0 :=
  pullback_map_pullbackPairingOf_eq_zero_iff _ (evaluationPairing L)
    (dualLineBundle X L).property _ b

/-- Precomposing `u` with an isomorphism does not change its divisor. -/
theorem subbundleDivisor_iso_comp (T : Over S) {N N' : T.left.Modules} (e : N' ≅ N)
    (u : N ⟶ overPullback ((pushforward p).obj L.val) T) :
    subbundleDivisor p L T (e.hom ≫ u) = subbundleDivisor p L T u := by
  have h : subbundlePairing p L T (e.hom ≫ u) =
      (tensorSheafIso (Limits.pullback p T.hom)
        ((Scheme.Modules.pullback (Limits.pullback.snd p T.hom)).mapIso e)
        (Iso.refl ((Scheme.Modules.pullback (Limits.pullback.fst p T.hom)).obj
          (dualLineBundle X L).val))).hom ≫ subbundlePairing p L T u := by
    simp only [subbundlePairing, subbundleSection, CategoryTheory.Functor.map_comp,
      Category.assoc]
    rw [pullbackPairingOf_comp]
    rfl
  rw [subbundleDivisor, subbundleDivisor, h, Hom.imageIdealData_precomp_iso]

/-- The line bundle `q_T^* N ⊗ g_T^* L^∨` on `X_T`, the source of the pairing of `u`. -/
def subbundlePairingSource (T : Over S) (N : LineBundle T.left) :
    LineBundle (Limits.pullback p T.hom) :=
  tensorLineBundle _ (pullbackLineBundle (Limits.pullback.snd p T.hom) N)
    (pullbackLineBundle (Limits.pullback.fst p T.hom) (dualLineBundle X L))

/-- The image ideal of the pairing of `u` localizes (its source is quasi-coherent). -/
theorem imageIdealLocalizes_subbundlePairing (T : Over S) (N : LineBundle T.left)
    (u : N.val ⟶ overPullback ((pushforward p).obj L.val) T) :
    Hom.ImageIdealLocalizes (subbundlePairing p L T u) := by
  have := lineBundle_isLocallyFree _ (subbundlePairingSource p L T N)
  have : (subbundlePairingSource p L T N).val.IsQuasicoherent := inferInstance
  exact Hom.imageIdealLocalizes_of_isQuasicoherent (M := (subbundlePairingSource p L T N).val)
    (subbundlePairing p L T u)

variable [Flat p] [LocallyOfFinitePresentation p] [GeometricallyIntegral p]

/-- **The divisor of a line subbundle is a relative effective Cartier divisor**, and the pairing
of `u` is a monomorphism: for `u : N ⟶ E_T` from a line bundle, nonzero on every field fibre,
when every base-change map of `L` is an isomorphism (Kleiman, proof of Thm 3.13, p. 26, with
Lemma 3.4, p. 22). -/
theorem mono_subbundlePairing_and_isRelativeEffectiveCartier
    (hbc : ∀ (T : Scheme.{u}) (g : T ⟶ S), IsIso (moduleBaseChangeMap p g L.val))
    (T : Over S) (N : LineBundle T.left)
    (u : N.val ⟶ overPullback ((pushforward p).obj L.val) T)
    (hu : ∀ (K : Type u) [Field K] (t : Spec (.of K) ⟶ T.left),
      (Scheme.Modules.pullback t).map u ≠ 0) :
    Mono (subbundlePairing p L T u) ∧ Scheme.Hom.IsRelativeEffectiveCartier
      (subbundleDivisor p L T u).subschemeι (Limits.pullback.snd p T.hom) := by
  have hφ : ∀ (K : Type u) [Field K] [IsAlgClosed K] (t : Spec (.of K) ⟶ T.left),
      (Scheme.Modules.pullback (Limits.pullback.fst (Limits.pullback.snd p T.hom) t)).map
        (subbundlePairing p L T u) ≠ 0 := fun K _ _ t h ↦
    pullback_fst_map_subbundleSection_ne_zero p L hbc T u t (hu K t)
      ((pullback_map_subbundlePairing_eq_zero_iff p L T u _).mp h)
  exact ⟨(mono_and_flat_zeroInclusion_comp_of_geometricallyIntegral
      (Limits.pullback.snd p T.hom) (subbundlePairingSource p L T N)
      (subbundlePairing p L T u) hφ).1,
    isRelativeEffectiveCartier_zeroInclusion_of_geometricallyIntegral
      (Limits.pullback.snd p T.hom) (subbundlePairingSource p L T N)
      (subbundlePairing p L T u) hφ⟩

/-- **The ideal of the divisor of a line subbundle** `u : N ⟶ E_T`: the factor of the pairing
of `u` through its image, `q_T^* N ⊗ g_T^* L^∨ ≅ I_D`. -/
def subbundleDivisorIdealIso
    (hbc : ∀ (T : Scheme.{u}) (g : T ⟶ S), IsIso (moduleBaseChangeMap p g L.val))
    (T : Over S) (N : LineBundle T.left)
    (u : N.val ⟶ overPullback ((pushforward p).obj L.val) T)
    (hu : ∀ (K : Type u) [Field K] (t : Spec (.of K) ⟶ T.left),
      (Scheme.Modules.pullback t).map u ≠ 0) :
    (show (Limits.pullback p T.hom).Modules from tensorSheaf (Limits.pullback p T.hom)
      ((Scheme.Modules.pullback (Limits.pullback.snd p T.hom)).obj N.val)
      ((Scheme.Modules.pullback (Limits.pullback.fst p T.hom)).obj (dualLineBundle X L).val)) ≅
    Scheme.Hom.idealModule (subbundleDivisor p L T u).subschemeι :=
  haveI := (mono_subbundlePairing_and_isRelativeEffectiveCartier p L hbc T N u hu).1
  haveI := Hom.zeroIdealFactor_isIso (subbundlePairing p L T u)
    (imageIdealLocalizes_subbundlePairing p L T N u)
  asIso (Hom.zeroIdealFactor (subbundlePairing p L T u)
    (imageIdealLocalizes_subbundlePairing p L T N u))

/-- The ideal isomorphism followed by the ideal inclusion is the pairing of `u`. -/
@[reassoc]
theorem subbundleDivisorIdealIso_hom_idealInclusion
    (hbc : ∀ (T : Scheme.{u}) (g : T ⟶ S), IsIso (moduleBaseChangeMap p g L.val))
    (T : Over S) (N : LineBundle T.left)
    (u : N.val ⟶ overPullback ((pushforward p).obj L.val) T)
    (hu : ∀ (K : Type u) [Field K] (t : Spec (.of K) ⟶ T.left),
      (Scheme.Modules.pullback t).map u ≠ 0) :
    (subbundleDivisorIdealIso p L hbc T N u hu).hom ≫
        Scheme.Hom.idealInclusion (subbundleDivisor p L T u).subschemeι =
      subbundlePairing p L T u :=
  Hom.zeroIdealFactor_inclusion (subbundlePairing p L T u)
    (imageIdealLocalizes_subbundlePairing p L T N u)

/-- **The divisor of a line subbundle lies in the linear system** (Kleiman, Def. 3.12, p. 25,
and the proof of Thm 3.13, p. 26): for `u : N ⟶ E_T` from a line bundle, nonzero on every field
fibre, when every base-change map of `L` is an isomorphism, `subbundleDivisor p L T u` is a
relative effective Cartier divisor with ideal `q_T^* N ⊗ g_T^* L^∨`. -/
theorem isLinearSystemDivisor_subbundleDivisor
    (hbc : ∀ (T : Scheme.{u}) (g : T ⟶ S), IsIso (moduleBaseChangeMap p g L.val))
    (T : Over S) (N : LineBundle T.left)
    (u : N.val ⟶ overPullback ((pushforward p).obj L.val) T)
    (hu : ∀ (K : Type u) [Field K] (t : Spec (.of K) ⟶ T.left),
      (Scheme.Modules.pullback t).map u ≠ 0) :
    IsLinearSystemDivisor p L T (subbundleDivisor p L T u) :=
  ⟨(mono_subbundlePairing_and_isRelativeEffectiveCartier p L hbc T N u hu).2, N,
    ⟨(subbundleDivisorIdealIso p L hbc T N u hu).symm⟩⟩

end AlgebraicGeometry.Scheme.LinearSystem

namespace AlgebraicGeometry.Scheme.LinearSystem

open Scheme.Modules Scheme.Modules.Invertible Scheme.RelativePicard Grassmannian

variable {X S : Scheme.{u}} (p : X ⟶ S) (L : LineBundle X) {k : ℕ}

/-- **The divisor of a point of `Gr(E, k)`**: for a rank-`k` locally free quotient `P : E_T ↠ Q`,
the divisor of the kernel inclusion `ker P ↪ E_T`. -/
def quotientDivisor (T : Over S)
    (P : LocallyFreeQuotientOf (overPullback ((pushforward p).obj L.val) T) k) :
    (Limits.pullback p T.hom).IdealSheafData :=
  subbundleDivisor p L T (kernel.ι P.π)

/-- Isomorphic quotients have the same divisor. -/
theorem quotientDivisor_eq_of_isoUnder (T : Over S)
    {P P' : LocallyFreeQuotientOf (overPullback ((pushforward p).obj L.val) T) k}
    (e : LocallyFreeQuotientOf.IsoUnder P P') :
    quotientDivisor p L T P = quotientDivisor p L T P' := by
  let eK : kernel P.π ≅ kernel P'.π := kernel.mapIso P.π P'.π (Iso.refl _) e.iso
    (by rw [e.comm, Iso.refl_hom, Category.id_comp])
  have h : kernel.ι P.π = eK.hom ≫ kernel.ι P'.π := by
    simp [eK]
  rw [quotientDivisor, quotientDivisor, h, subbundleDivisor_iso_comp]

/-- The kernel of a point of `Gr(E, k)`, for `E` of constant rank `k + 1`, as a line bundle on
`T`. -/
def quotientKernelLineBundle (hE : SheafHasRank ((pushforward p).obj L.val) (k + 1))
    (T : Over S) (P : LocallyFreeQuotientOf (overPullback ((pushforward p).obj L.val) T) k) :
    LineBundle T.left :=
  ⟨kernel P.π, P.isLocallyRankOne_kernel (sheafHasRank_pullback T.hom hE)⟩

/-- The kernel inclusion of a point of `Gr(E, k)` is nonzero on every field fibre
(`LineSubbundle`, converse direction). -/
theorem pullback_map_kernel_ι_ne_zero (hE : SheafHasRank ((pushforward p).obj L.val) (k + 1))
    (T : Over S) (P : LocallyFreeQuotientOf (overPullback ((pushforward p).obj L.val) T) k)
    (K : Type u) [Field K] (t : Spec (.of K) ⟶ T.left) :
    (Scheme.Modules.pullback t).map (kernel.ι P.π) ≠ 0 := by
  have : IsFiniteLocallyFree T.left (ShortComplex.kernelSequence P.π).X₃ :=
    P.hasRank.isFiniteLocallyFree
  exact pullback_map_f_ne_zero_of_shortExact (shortExact_kernelSequence P.π)
    (P.isLocallyRankOne_kernel (sheafHasRank_pullback T.hom hE)) K t

variable [Flat p] [LocallyOfFinitePresentation p] [GeometricallyIntegral p]

/-- **The divisor of a point of `Gr(E, k)` lies in the linear system** (Kleiman, proof of
Thm 3.13, pp. 25–26): for `E = p_* L` of constant rank `k + 1` with every base-change map of `L`
an isomorphism, the divisor of a rank-`k` locally free quotient `P` of `E_T` is a relative
effective Cartier divisor of `X_T ⟶ T` whose ideal is `q_T^* (ker P) ⊗ g_T^* L^∨`. -/
theorem isLinearSystemDivisor_quotientDivisor
    (hbc : ∀ (T : Scheme.{u}) (g : T ⟶ S), IsIso (moduleBaseChangeMap p g L.val))
    (hE : SheafHasRank ((pushforward p).obj L.val) (k + 1)) (T : Over S)
    (P : LocallyFreeQuotientOf (overPullback ((pushforward p).obj L.val) T) k) :
    IsLinearSystemDivisor p L T (quotientDivisor p L T P) :=
  isLinearSystemDivisor_subbundleDivisor p L hbc T (quotientKernelLineBundle p L hE T P)
    (kernel.ι P.π) (pullback_map_kernel_ι_ne_zero p L hE T P)

end AlgebraicGeometry.Scheme.LinearSystem
