/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Picard.LinearSystem.Divisor
public import Aglib.AlgebraicGeometry.Picard.Comparison.PullbackFullyFaithful
public import Aglib.AlgebraicGeometry.Modules.LocallyFree.EqualRank

/-!
# Linear-system divisors are the divisors of points of `Gr(E, k)`

Let `p : X ⟶ S` be proper, flat and geometrically integral over a locally Noetherian `S`, `L` a
line bundle on `X` with every base-change map of `L` an isomorphism, and `E = p_* L` of constant
rank `k + 1`. For every `T` over `S`, the divisor map `P ↦ quotientDivisor p L T P` is a
bijection from isomorphism classes of rank-`k` locally free quotients of `E_T` (the `T`-points
of `Gr(E, k)`) to the divisors of the linear system `LinSys_{L/X/S}(T)` (Kleiman, *The Picard
scheme*, arXiv:math/0504020v1, Thm 3.13, pp. 25–26, and Ex. 3.14, p. 26):

* `exists_subbundle_of_isLinearSystemDivisor`: every divisor `D` of the linear system is the
  divisor of a line subbundle `u : N ⟶ E_T`, nonzero on every field fibre. Write
  `I_D ≅ q_T^* N ⊗ g_T^* L^∨`; the inclusion `I_D ⟶ 𝒪` is the pairing of a unique section
  `q_T^* N ⟶ g_T^* L` (`pullbackPairingOfEquiv`), the section of `u`, where `u` is its adjoint
  followed by the inverse base-change map. The ideal of `D` is nonzero on every fibre
  (`pullback_fst_map_idealInclusion_ne_zero`), so `u` is nonzero on every field fibre.
* `exists_comp_eq_of_subbundleDivisor_eq`: line subbundles with the same divisor differ by a map
  of line bundles, `u = a ≫ u'`. The two ideal isomorphisms give `q_T^* N ⊗ B ⟶ q_T^* N' ⊗ B`;
  tensoring with the line bundle `B = g_T^* L^∨` is full and `q_T^*` is full on line bundles
  (`bijective_pullback_snd_map_of_isLocallyRankOne_of_isProper_of_flat_of_geometricallyIntegral`,
  Kleiman Lemma 2.7, p. 18, applied as in the proof of Thm 3.13, p. 25), and the pairing and the
  base-change map are injective.
* `quotientDivisorMap`, `bijective_quotientDivisorMap`, `quotientDivisorEquiv`: the bijection,
  with inverse `D ↦ E_T ↠ coker u` (`LocallyFreeQuotientOf.ofLineSubbundle`).
* `isEmpty_of_isLinearSystemDivisor_of_sheafHasRank_zero`: where `h^0 = 0` (`E = 0`) there is no
  divisor over a nonempty `T`; the statements above assume rank `k + 1 ≥ 1`.

The naturality in `T` and the representability statement are in
`Picard/LinearSystem/Representability`.
-/

@[expose] public section

noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

open CategoryTheory Limits Opposite

namespace AlgebraicGeometry.Scheme.LinearSystem

open Scheme.Modules Scheme.Modules.Invertible Scheme.RelativePicard Grassmannian

/-- If `u` vanishes after pullback along `v`, then `q^* u` vanishes after pullback along the
projection `Y ×_T V ⟶ Y`. -/
theorem pullback_fst_map_pullback_map_eq_zero {Y T V : Scheme.{u}} (q : Y ⟶ T) (v : V ⟶ T)
    {A B : T.Modules} (u : A ⟶ B) (hu : (Scheme.Modules.pullback v).map u = 0) :
    (Scheme.Modules.pullback (Limits.pullback.fst q v)).map
      ((Scheme.Modules.pullback q).map u) = 0 := by
  have h := (pullbackSquareIso (Limits.pullback.fst q v) (Limits.pullback.snd q v) q v
    Limits.pullback.condition).hom.naturality u
  simp only [Functor.comp_map, hu, CategoryTheory.Functor.map_zero, zero_comp] at h
  exact (cancel_epi _).mp (h.symm.trans comp_zero.symm)

/-- Equal closed subschemes have isomorphic ideals, compatibly with the ideal inclusions. -/
theorem exists_iso_comp_idealInclusion_of_eq {Y : Scheme.{u}} {D₁ D₂ : Y.IdealSheafData}
    (h : D₁ = D₂) :
    ∃ e : Scheme.Hom.idealModule D₁.subschemeι ≅ Scheme.Hom.idealModule D₂.subschemeι,
      e.hom ≫ Scheme.Hom.idealInclusion D₂.subschemeι =
        Scheme.Hom.idealInclusion D₁.subschemeι := by
  subst h
  exact ⟨Iso.refl _, Category.id_comp _⟩

variable {X S : Scheme.{u}} (p : X ⟶ S) (L : LineBundle X)

section Subbundle

variable [GeometricallyIntegral p]

/-- **Every divisor of the linear system is the divisor of a line subbundle** of `E_T` (Kleiman,
proof of Thm 3.13, pp. 25–26): if every base-change map of `L` is an isomorphism, a divisor `D`
of the linear system is `subbundleDivisor p L T u` for a map `u : N ⟶ E_T` from a line bundle,
nonzero on every field fibre. -/
theorem exists_subbundle_of_isLinearSystemDivisor
    (hbc : ∀ (T : Scheme.{u}) (g : T ⟶ S), IsIso (moduleBaseChangeMap p g L.val))
    (T : Over S) {D : (Limits.pullback p T.hom).IdealSheafData}
    (hD : IsLinearSystemDivisor p L T D) :
    ∃ (N : LineBundle T.left) (u : N.val ⟶ overPullback ((pushforward p).obj L.val) T),
      (∀ (K : Type u) [Field K] (t : Spec (.of K) ⟶ T.left),
        (Scheme.Modules.pullback t).map u ≠ 0) ∧ subbundleDivisor p L T u = D := by
  obtain ⟨hR, N, ⟨α⟩⟩ := hD
  obtain ⟨s, hs⟩ := (bijective_pullbackPairingOf (Limits.pullback.fst p T.hom)
    (evaluationPairing L) (dualLineBundle X L).property _).2
      (α.inv ≫ Scheme.Hom.idealInclusion D.subschemeι)
  have : IsIso (familyBaseChangeMap p L T) := by
    rw [familyBaseChangeMap_eq]
    exact hbc _ _
  obtain ⟨u, hus⟩ : ∃ u : N.val ⟶ overPullback ((pushforward p).obj L.val) T,
      subbundleSection p L T u = s :=
    ⟨(pullbackPushforwardAdjunction (Limits.pullback.snd p T.hom)).homEquiv _ _ s ≫
        inv (familyBaseChangeMap p L T), by
      apply ((pullbackPushforwardAdjunction (Limits.pullback.snd p T.hom)).homEquiv _ _).injective
      rw [homEquiv_subbundleSection, Category.assoc, IsIso.inv_hom_id, Category.comp_id]⟩
  have hpair : subbundlePairing p L T u = α.inv ≫ Scheme.Hom.idealInclusion D.subschemeι := by
    rw [subbundlePairing, hus]
    exact hs
  refine ⟨N, u, fun K _ t h ↦ ?_, ?_⟩
  · have := isIntegral_pullback_of_geometricallyIntegral (Limits.pullback.snd p T.hom) t
    apply pullback_fst_map_idealInclusion_ne_zero hR t
    have h1 : (Scheme.Modules.pullback (Limits.pullback.fst (Limits.pullback.snd p T.hom) t)).map
        (subbundleSection p L T u) = 0 := by
      rw [subbundleSection, CategoryTheory.Functor.map_comp,
        pullback_fst_map_pullback_map_eq_zero _ t u h, zero_comp]
    have h2 := (pullback_map_subbundlePairing_eq_zero_iff p L T u _).mpr h1
    rw [hpair, CategoryTheory.Functor.map_comp] at h2
    exact (cancel_epi _).mp (h2.trans comp_zero.symm)
  · have h := Hom.imageIdealData_precomp_iso α.symm (Scheme.Hom.idealInclusion D.subschemeι)
    rw [Iso.symm_hom] at h
    rw [subbundleDivisor, hpair, h, Hom.imageIdealData_idealInclusion,
      Scheme.IdealSheafData.ker_subschemeι]

/-- **The `h^0 = 0` piece**: if `E = p_* L` is zero (constant rank `0`) and every base-change map
of `L` is an isomorphism, the linear system has no divisor over a nonempty `T`. -/
theorem isEmpty_of_isLinearSystemDivisor_of_sheafHasRank_zero
    (hbc : ∀ (T : Scheme.{u}) (g : T ⟶ S), IsIso (moduleBaseChangeMap p g L.val))
    (hE : SheafHasRank ((pushforward p).obj L.val) 0) (T : Over S)
    {D : (Limits.pullback p T.hom).IdealSheafData} (hD : IsLinearSystemDivisor p L T D) :
    IsEmpty T.left := by
  obtain ⟨N, u, hu, -⟩ := exists_subbundle_of_isLinearSystemDivisor p L hbc T hD
  refine ⟨fun x ↦ hu (T.left.residueField x) (T.left.fromSpecResidueField x) ?_⟩
  rw [(isZero_of_sheafHasRank_zero (sheafHasRank_pullback T.hom hE)).eq_of_tgt u 0,
    CategoryTheory.Functor.map_zero]

end Subbundle

section Uniqueness

variable [IsLocallyNoetherian S] [IsProper p] [Flat p] [GeometricallyIntegral p]

/-- **Line subbundles with the same divisor differ by a map of line bundles** (Kleiman, proof of
Thm 3.13, p. 25: "`(N, u)` is determined up to isomorphism"): if
`subbundleDivisor p L T u = subbundleDivisor p L T u'`, then `u = a ≫ u'` for some `a`. -/
theorem exists_comp_eq_of_subbundleDivisor_eq
    (hbc : ∀ (T : Scheme.{u}) (g : T ⟶ S), IsIso (moduleBaseChangeMap p g L.val))
    (T : Over S) (N N' : LineBundle T.left)
    (u : N.val ⟶ overPullback ((pushforward p).obj L.val) T)
    (u' : N'.val ⟶ overPullback ((pushforward p).obj L.val) T)
    (hu : ∀ (K : Type u) [Field K] (t : Spec (.of K) ⟶ T.left),
      (Scheme.Modules.pullback t).map u ≠ 0)
    (hu' : ∀ (K : Type u) [Field K] (t : Spec (.of K) ⟶ T.left),
      (Scheme.Modules.pullback t).map u' ≠ 0)
    (h : subbundleDivisor p L T u = subbundleDivisor p L T u') :
    ∃ a : N.val ⟶ N'.val, a ≫ u' = u := by
  obtain ⟨e, he⟩ := exists_iso_comp_idealInclusion_of_eq h
  obtain ⟨γ, hγ⟩ : ∃ γ, γ ≫ subbundlePairing p L T u' = subbundlePairing p L T u :=
    ⟨(subbundleDivisorIdealIso p L hbc T N u hu).hom ≫ e.hom ≫
        (subbundleDivisorIdealIso p L hbc T N' u' hu').inv, by
      rw [← subbundleDivisorIdealIso_hom_idealInclusion p L hbc T N' u' hu']
      simp only [Category.assoc, Iso.inv_hom_id_assoc]
      rw [he, subbundleDivisorIdealIso_hom_idealInclusion]⟩
  obtain ⟨δ, hδ⟩ := (tensorRightFullyFaithful (pullbackLineBundle (Limits.pullback.fst p T.hom)
    (dualLineBundle X L))).map_surjective (X := (Scheme.Modules.pullback
      (Limits.pullback.snd p T.hom)).obj N.val)
    (Y := (Scheme.Modules.pullback (Limits.pullback.snd p T.hom)).obj N'.val) γ
  obtain ⟨a, ha⟩ :=
    (bijective_pullback_snd_map_of_isLocallyRankOne_of_isProper_of_flat_of_geometricallyIntegral
      p T.hom N.val N'.val N'.property).2 δ
  have ha' : (Scheme.Modules.pullback (Limits.pullback.snd p T.hom)).map a = δ := ha
  refine ⟨a, ?_⟩
  have h1 : subbundlePairing p L T (a ≫ u') =
      tensorSheafMap _ ((Scheme.Modules.pullback (Limits.pullback.snd p T.hom)).map a)
        (𝟙 _) ≫ subbundlePairing p L T u' := by
    simp only [subbundlePairing, subbundleSection, CategoryTheory.Functor.map_comp,
      Category.assoc]
    rw [pullbackPairingOf_comp]
  have hs : subbundlePairing p L T (a ≫ u') = subbundlePairing p L T u := by
    rw [h1, ha']
    exact (congrArg (· ≫ subbundlePairing p L T u') hδ).trans hγ
  have hs' : subbundleSection p L T (a ≫ u') = subbundleSection p L T u :=
    (bijective_pullbackPairingOf (Limits.pullback.fst p T.hom) (evaluationPairing L)
      (dualLineBundle X L).property _).1 hs
  have : IsIso (familyBaseChangeMap p L T) := by
    rw [familyBaseChangeMap_eq]
    exact hbc _ _
  have h2 := congrArg ((pullbackPushforwardAdjunction (Limits.pullback.snd p T.hom)).homEquiv _ _)
    hs'
  rw [homEquiv_subbundleSection, homEquiv_subbundleSection] at h2
  exact (cancel_mono (familyBaseChangeMap p L T)).mp h2

end Uniqueness

/-- Two locally free quotients of `F`, each of whose kernels is killed by the other quotient map,
are isomorphic under `F`. -/
theorem nonempty_isoUnder_of_kernel_ι_comp_eq_zero {Y : Scheme.{u}} {F : Y.Modules} {k : ℕ}
    {P P' : LocallyFreeQuotientOf F k} (h₁ : kernel.ι P.π ≫ P'.π = 0)
    (h₂ : kernel.ι P'.π ≫ P.π = 0) : Nonempty (LocallyFreeQuotientOf.IsoUnder P P') := by
  obtain ⟨a, ha⟩ := CokernelCofork.IsColimit.desc' (shortExact_kernelSequence P.π).gIsCokernel
    P'.π h₁
  obtain ⟨b, hb⟩ := CokernelCofork.IsColimit.desc' (shortExact_kernelSequence P'.π).gIsCokernel
    P.π h₂
  have ha' : P.π ≫ a = P'.π := ha
  have hb' : P'.π ≫ b = P.π := hb
  refine ⟨⟨⟨a, b, ?_, ?_⟩, ha'⟩⟩
  · exact (cancel_epi P.π).mp (by rw [reassoc_of% ha', hb', Category.comp_id])
  · exact (cancel_epi P'.π).mp (by rw [reassoc_of% hb', ha', Category.comp_id])

variable {k : ℕ}

/-- The divisor of the quotient by a line subbundle `u` is the divisor of `u`. -/
theorem quotientDivisor_ofLineSubbundle (hE : SheafHasRank ((pushforward p).obj L.val) (k + 1))
    (T : Over S) (N : LineBundle T.left)
    (u : N.val ⟶ overPullback ((pushforward p).obj L.val) T)
    (hu : ∀ (K : Type u) [Field K] (t : Spec (.of K) ⟶ T.left),
      (Scheme.Modules.pullback t).map u ≠ 0) :
    quotientDivisor p L T (LocallyFreeQuotientOf.ofLineSubbundle (sheafHasRank_pullback T.hom hE)
      N.property u hu) = subbundleDivisor p L T u := by
  obtain ⟨e, he⟩ := LocallyFreeQuotientOf.exists_iso_hom_kernel_ι_ofLineSubbundle
    (sheafHasRank_pullback T.hom hE) N.property u hu
  have hι : kernel.ι (LocallyFreeQuotientOf.ofLineSubbundle (sheafHasRank_pullback T.hom hE)
      N.property u hu).π = e.inv ≫ u :=
    (Iso.eq_inv_comp e).mpr he
  rw [quotientDivisor, hι]
  exact subbundleDivisor_iso_comp p L T e.symm u

section Bijection

variable [IsLocallyNoetherian S] [IsProper p] [Flat p] [GeometricallyIntegral p]

/-- **Points of `Gr(E, k)` with the same divisor are isomorphic.** -/
theorem nonempty_isoUnder_of_quotientDivisor_eq
    (hbc : ∀ (T : Scheme.{u}) (g : T ⟶ S), IsIso (moduleBaseChangeMap p g L.val))
    (hE : SheafHasRank ((pushforward p).obj L.val) (k + 1)) (T : Over S)
    {P P' : LocallyFreeQuotientOf (overPullback ((pushforward p).obj L.val) T) k}
    (h : quotientDivisor p L T P = quotientDivisor p L T P') :
    Nonempty (LocallyFreeQuotientOf.IsoUnder P P') := by
  obtain ⟨a, ha⟩ := exists_comp_eq_of_subbundleDivisor_eq p L hbc T
    (quotientKernelLineBundle p L hE T P) (quotientKernelLineBundle p L hE T P')
    (kernel.ι P.π) (kernel.ι P'.π) (pullback_map_kernel_ι_ne_zero p L hE T P)
    (pullback_map_kernel_ι_ne_zero p L hE T P') h
  obtain ⟨b, hb⟩ := exists_comp_eq_of_subbundleDivisor_eq p L hbc T
    (quotientKernelLineBundle p L hE T P') (quotientKernelLineBundle p L hE T P)
    (kernel.ι P'.π) (kernel.ι P.π) (pullback_map_kernel_ι_ne_zero p L hE T P')
    (pullback_map_kernel_ι_ne_zero p L hE T P) h.symm
  exact nonempty_isoUnder_of_kernel_ι_comp_eq_zero
    (by rw [← ha, Category.assoc, kernel.condition, comp_zero])
    (by rw [← hb, Category.assoc, kernel.condition, comp_zero])

/-- **The divisor map** `Gr(E, k)(T) ⟶ LinSys_{L/X/S}(T)` on isomorphism classes of rank-`k`
locally free quotients of `E_T`. -/
def quotientDivisorMap
    (hbc : ∀ (T : Scheme.{u}) (g : T ⟶ S), IsIso (moduleBaseChangeMap p g L.val))
    (hE : SheafHasRank ((pushforward p).obj L.val) (k + 1)) (T : Over S) :
    (quotBundleFunctor ((pushforward p).obj L.val) k).obj (op T) →
      (linearSystemFunctor p L).obj (op T) :=
  Quotient.lift
    (fun P ↦ ⟨quotientDivisor p L T P, isLinearSystemDivisor_quotientDivisor p L hbc hE T P⟩)
    (fun _ _ ⟨e⟩ ↦ Subtype.ext (quotientDivisor_eq_of_isoUnder p L T e))

theorem quotientDivisorMap_mk
    (hbc : ∀ (T : Scheme.{u}) (g : T ⟶ S), IsIso (moduleBaseChangeMap p g L.val))
    (hE : SheafHasRank ((pushforward p).obj L.val) (k + 1)) (T : Over S)
    (P : LocallyFreeQuotientOf (overPullback ((pushforward p).obj L.val) T) k) :
    (quotientDivisorMap p L hbc hE T (Quotient.mk _ P)).1 = quotientDivisor p L T P :=
  rfl

/-- **The divisor map is bijective** (Kleiman, Thm 3.13, pp. 25–26). -/
theorem bijective_quotientDivisorMap
    (hbc : ∀ (T : Scheme.{u}) (g : T ⟶ S), IsIso (moduleBaseChangeMap p g L.val))
    (hE : SheafHasRank ((pushforward p).obj L.val) (k + 1)) (T : Over S) :
    Function.Bijective (quotientDivisorMap p L hbc hE T) := by
  constructor
  · intro x y hxy
    induction x using Quotient.inductionOn with | h P => ?_
    induction y using Quotient.inductionOn with | h P' => ?_
    exact Quotient.sound
      (nonempty_isoUnder_of_quotientDivisor_eq p L hbc hE T (congrArg Subtype.val hxy))
  · rintro ⟨D, hD⟩
    obtain ⟨N, u, hu, hDu⟩ := exists_subbundle_of_isLinearSystemDivisor p L hbc T hD
    exact ⟨Quotient.mk _ (LocallyFreeQuotientOf.ofLineSubbundle (sheafHasRank_pullback T.hom hE)
      N.property u hu), Subtype.ext ((quotientDivisor_ofLineSubbundle p L hE T N u hu).trans hDu)⟩

/-- **`Gr(E, k)(T) ≃ LinSys_{L/X/S}(T)`**: the divisor map as an equivalence. -/
def quotientDivisorEquiv
    (hbc : ∀ (T : Scheme.{u}) (g : T ⟶ S), IsIso (moduleBaseChangeMap p g L.val))
    (hE : SheafHasRank ((pushforward p).obj L.val) (k + 1)) (T : Over S) :
    (quotBundleFunctor ((pushforward p).obj L.val) k).obj (op T) ≃
      (linearSystemFunctor p L).obj (op T) :=
  Equiv.ofBijective _ (bijective_quotientDivisorMap p L hbc hE T)

theorem quotientDivisorEquiv_apply
    (hbc : ∀ (T : Scheme.{u}) (g : T ⟶ S), IsIso (moduleBaseChangeMap p g L.val))
    (hE : SheafHasRank ((pushforward p).obj L.val) (k + 1)) (T : Over S)
    (x : (quotBundleFunctor ((pushforward p).obj L.val) k).obj (op T)) :
    quotientDivisorEquiv p L hbc hE T x = quotientDivisorMap p L hbc hE T x :=
  rfl

end Bijection

end AlgebraicGeometry.Scheme.LinearSystem
