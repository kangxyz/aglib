/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.HilbertScheme.IdealTwist.Evaluation
public import Aglib.AlgebraicGeometry.HilbertScheme.LocallyNoetherianPoint
public import Aglib.AlgebraicGeometry.HilbertScheme.UniversalSubschemeGrassmannian

/-!
# A Hilbert family is the universal subscheme pulled back along its Grassmannian point

Let `T` be a locally Noetherian scheme over `Spec A`, `Z` a point of `Hilb^Φ(T)`,
`ι ≃ Fin (n + 1)`, `r ≥ hilbertRegularityBound n Φ` a natural number, and
`q_Z : 𝒪_T^{monomials} ⟶ π_* 𝒪_Z(r)` the evaluation map (`directImageQuotientMap`), with kernel
`K = ker q_Z ⊆ 𝒪_T^{monomials}`. This file proves the "⇒" half of Nitsure's proof of
Theorem 5.2 (*Construction of Hilbert and Quot schemes*, arXiv:math/0504590v1, §5, pp. 26–27),
for `E = 𝒪`: the closed subscheme `Z(K)` cut out by the image of `π^* K ⊗ 𝒪(-r) ⟶ 𝒪`
(`evaluationIdeal`) is `Z` (`IsHilbertFamily.evaluationIdeal_kernel_directImageQuotientMap`), so
`Z` is the pullback of the universal subscheme along its Grassmannian point
(`IsHilbertFamily.universalHilbertSubscheme_comap_grassmannianMap`).

* `monomialEvaluation ι g r ιK : π^* K ⟶ 𝒪(r)` is the evaluation of the monomials on `π^* K` for
  `ιK : K ⟶ 𝒪_T^{monomials}`; it is the map whose twist by `-r` defines `Z(K)`
  (`freeTransfer_comp_homogeneousEvaluation_monomialFamily`). Its restriction to a closed
  subscheme `W` vanishes exactly when `ιK ≫ q_W = 0`, by adjunction
  (`monomialEvaluation_comp_twistedRestriction_eq_zero_iff`).
* `directImageMonomialMap ι g r : 𝒪_T^{monomials} ⟶ π_*(𝒪(r) ⊗ 𝒪)` is an epimorphism for every
  `T` (`epi_directImageMonomialMap`): over each affine open `Spec B ⊆ T` it is
  `𝒪^{monomials} ⟶ (toSpec)_* 𝒪(r)`, onto because the monomials are a basis of `B[x]_r`
  (`epi_pushforwardFreeMap_monomialMap`). The evaluation map factors through it,
  `q_Z = μ ≫ π_*(𝒪(r) ⊗ 𝒪 ⟶ 𝒪(r) ⊗ 𝒪_Z)` (`directImageQuotientMap_eq_comp`), through the
  presentation identity `IdealSheafData.twistedRestriction_eq_shortComplex_map_g`.

For `ιK = ker q_Z`, `monomialEvaluation` lifts to `ψ : π^* K ⟶ I_Z(r)` (`familyIdealTwistLift`),
and the adjoint `K ⟶ π_* I_Z(r)` of `ψ` is an epimorphism: `π_* I_Z(r)` is the kernel of
`π_*(𝒪(r) ⊗ 𝒪) ⟶ π_* 𝒪_Z(r)` and `μ` is onto
(`epi_of_isKernel_pushforward_familyTwistedShortComplex`). Relative global generation
(`IsHilbertFamily.evaluationIdeal_eq_of_epi_homEquiv`) then gives `Z(K) = Z`: the image of
`π_T^* π_{T*} G(r) → E_T(r)`, twisted by `-r`, is the ideal of `Z` (p. 26).
-/

@[expose] public section

noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory Opposite
open AlgebraicGeometry.Scheme.Modules
open scoped Polynomial

universe u

namespace AlgebraicGeometry

namespace ProjectiveSpace

section Evaluation

variable (ι : Type u) {A : Type u} [CommRing A] {T : Scheme.{u}}
  (g : T ⟶ Spec (CommRingCat.of A))

/-- **The monomial evaluation on `π^* K`**: for `ιK : K ⟶ 𝒪_T^{monomials}`, the composite
`π^* K ⟶ π^* 𝒪_T^{monomials} ≅ 𝒪^{monomials} ⟶ 𝒪(r)` on `P^n_A ×_{Spec A} T`, the last map the
pulled-back monomial sections (`familyMonomialMap`). -/
def monomialEvaluation (r : ℕ) {K : T.Modules}
    (ιK : K ⟶ SheafOfModules.free (R := T.ringCatSheaf) (Monomials ι r)) :
    (Scheme.Modules.pullback (pullback.snd (toSpec A ι) g)).obj K ⟶ familyTwistingSheaf ι g r :=
  (Scheme.Modules.pullback (pullback.snd (toSpec A ι) g)).map ιK ≫
    (pullbackFreeIso (pullback.snd (toSpec A ι) g) (Monomials ι r)).hom ≫ familyMonomialMap ι g r

theorem monomialEvaluation_def (r : ℕ) {K : T.Modules}
    (ιK : K ⟶ SheafOfModules.free (R := T.ringCatSheaf) (Monomials ι r)) :
    monomialEvaluation ι g r ιK =
      (Scheme.Modules.pullback (pullback.snd (toSpec A ι) g)).map ιK ≫
        (pullbackFreeIso (pullback.snd (toSpec A ι) g) (Monomials ι r)).hom ≫
          familyMonomialMap ι g r :=
  rfl

/-- The evaluation map of `Z(K)`, untwisted, is the monomial evaluation: the transfer
`π^* K ⟶ p^* 𝒪^{monomials}` followed by the pullback of `homogeneousEvaluation` of the monomial
family is `monomialEvaluation`. -/
theorem freeTransfer_comp_homogeneousEvaluation_monomialFamily (r : ℕ) {K : T.Modules}
    (ιK : K ⟶ SheafOfModules.free (R := T.ringCatSheaf) (Monomials ι r)) :
    Scheme.Modules.freeTransfer (pullback.snd (toSpec A ι) g) (pullback.fst (toSpec A ι) g) ιK ≫
        (Scheme.Modules.pullback (pullback.fst (toSpec A ι) g)).map
          (homogeneousEvaluation ι r (monomialFamily (A := A) ι r)) =
      monomialEvaluation ι g r ιK := by
  rw [homogeneousEvaluation_monomialFamily, monomialEvaluation_def, familyMonomialMap,
    pullbackFreeMap_def, Scheme.Modules.freeTransfer]
  simp only [Category.assoc]

/-- **The restriction of the monomial evaluation vanishes exactly on the kernel**: for a closed
subscheme `W ⊆ P^n_A ×_{Spec A} T`, `monomialEvaluation` followed by the restriction
`𝒪(r) ⟶ 𝒪_W(r)` vanishes if and only if `ιK` followed by the evaluation map
`𝒪_T^{monomials} ⟶ π_* 𝒪_W(r)` does (adjunction). -/
theorem monomialEvaluation_comp_twistedRestriction_eq_zero_iff (r : ℕ) {K : T.Modules}
    (ιK : K ⟶ SheafOfModules.free (R := T.ringCatSheaf) (Monomials ι r))
    (W : (pullback (toSpec A ι) g).IdealSheafData) :
    monomialEvaluation ι g r ιK ≫ W.twistedRestriction (familyTwistingSheaf ι g r) = 0 ↔
      ιK ≫ directImageQuotientMap ι g W r = 0 := by
  rw [directImageQuotientMap, comp_pushforwardFreeMap_eq_zero_iff, familyQuotientMonomialMap,
    monomialEvaluation_def]
  simp only [Category.assoc]

/-- **The monomial sections of `π_*(𝒪(r) ⊗ 𝒪)`**: the adjoint of
`𝒪^{monomials} ⟶ 𝒪(r) ≅ 𝒪(r) ⊗ 𝒪` on `P^n_A ×_{Spec A} T`, with values in the direct image of
the middle term of the twisted sequence of every closed subscheme. -/
def directImageMonomialMap (r : ℕ) :
    SheafOfModules.free (R := T.ringCatSheaf) (Monomials ι r) ⟶
      (Scheme.Modules.pushforward (pullback.snd (toSpec A ι) g)).obj
        ((moduleTensorLeftFunctor _ (familyTwistingSheaf ι g r)).obj
          (SheafOfModules.unit (pullback (toSpec A ι) g).ringCatSheaf)) :=
  pushforwardFreeMap (pullback.snd (toSpec A ι) g)
    (familyMonomialMap ι g r ≫ (ρ_ (familyTwistingSheaf ι g r)).inv)

theorem directImageMonomialMap_def (r : ℕ) :
    directImageMonomialMap ι g r =
      pushforwardFreeMap (pullback.snd (toSpec A ι) g)
        (familyMonomialMap ι g r ≫ (ρ_ (familyTwistingSheaf ι g r)).inv) :=
  rfl

/-- **The evaluation map factors through the monomial sections of `π_*(𝒪(r) ⊗ 𝒪)`**: for a closed
subscheme `Z`, `q_Z = μ ≫ π_*(𝒪(r) ⊗ 𝒪 ⟶ 𝒪(r) ⊗ 𝒪_Z)`. -/
theorem directImageQuotientMap_eq_comp (Z : (pullback (toSpec A ι) g).IdealSheafData) (r : ℕ) :
    directImageQuotientMap ι g Z r =
      directImageMonomialMap ι g r ≫
        (Scheme.Modules.pushforward (pullback.snd (toSpec A ι) g)).map
          (familyTwistedShortComplex ι g Z r).g := by
  rw [directImageMonomialMap_def, ← pushforwardFreeMap_comp_right, Category.assoc,
    ← Z.twistedRestriction_eq_shortComplex_map_g, directImageQuotientMap,
    familyQuotientMonomialMap]

end Evaluation

section Generation

variable (ι : Type u) {A : Type u} [CommRing A] (n : ℕ) (e : ι ≃ Fin (n + 1)) {T : Scheme.{u}}
  (g : T ⟶ Spec (CommRingCat.of A))

/-- `pullbackFreeMap` of the monomial sections of `𝒪(r)` on `P^n_A ×_{Spec A} T` along `p` with
`p ≫ fst = q`, followed by an identification `d` of `q^* 𝒪(r)`. Stated at variable `p`, `q` and
`d`. -/
theorem pullbackFreeMap_familyMonomialMap_of_comp_fst {Y : Scheme.{u}}
    (p : Y ⟶ pullback (toSpec A ι) g) (q : Y ⟶ ProjectiveSpace A ι)
    (hq : p ≫ pullback.fst (toSpec A ι) g = q) (r : ℕ) {L' : Y.Modules}
    (d : (Scheme.Modules.pullback q).obj (twistingSheaf A ι (r : ℤ)) ≅ L') :
    pullbackFreeMap p (familyMonomialMap ι g r) ≫
        ((Scheme.Modules.pullbackComp p (pullback.fst (toSpec A ι) g)).app _ ≪≫
          (Scheme.Modules.pullbackCongr hq).app (twistingSheaf A ι (r : ℤ)) ≪≫ d).hom =
      pullbackFreeMap q (monomialMap ι A r) ≫ d.hom := by
  rw [Iso.trans_hom, Iso.trans_hom, Iso.app_hom, Iso.app_hom, familyMonomialMap,
    ← Category.assoc, pullbackFreeMap_comp, ← Category.assoc, pullbackFreeMap_congr]

include e in
/-- **The monomials generate `𝒪(r)` over an affine open**: for an open immersion
`x : Spec B ⟶ T`, the pullback along `x` of `𝒪_T^{monomials} ⟶ π_* 𝒪(r)` is an epimorphism. Over
`Spec B` it is `𝒪^{monomials} ⟶ (toSpec)_* 𝒪(r)` (`pushforwardFreeMap_baseChange` on the
open-immersion square `isPullback_pointMap`), onto since the monomials form a basis of `B[x]_r`
(`epi_pushforwardFreeMap_monomialMap`). -/
theorem epi_pullbackFreeMap_pushforwardFreeMap_familyMonomialMap {B : Type u} [CommRing B]
    (x : Spec (CommRingCat.of B) ⟶ T) [IsOpenImmersion x] (r : ℕ) :
    Epi (pullbackFreeMap x
      (pushforwardFreeMap (pullback.snd (toSpec A ι) g) (familyMonomialMap ι g r))) := by
  have hsq := isPullback_pointMap ι g x
  have hiso : IsIso ((cartesianBaseChangeMap (pointMap ι g x) (toSpec B ι)
      (pullback.snd (toSpec A ι) g) x hsq).app (familyTwistingSheaf ι g r)) :=
    isIso_cartesianBaseChangeMap_of_isOpenImmersion _ _ _ _ _ _
  have hψ : pullbackFreeMap (pointMap ι g x) (familyMonomialMap ι g r) ≫
      ((Scheme.Modules.pullbackComp (pointMap ι g x) (pullback.fst (toSpec A ι) g)).app _ ≪≫
        (Scheme.Modules.pullbackCongr (pointMap_fst ι g x)).app (twistingSheaf A ι (r : ℤ)) ≪≫
          twistingPullbackIso (pointRingHom g x) ι r).hom = monomialMap ι B r :=
    (pullbackFreeMap_familyMonomialMap_of_comp_fst ι g (pointMap ι g x)
      (map (pointRingHom g x) ι) (pointMap_fst ι g x) r
      (twistingPullbackIso (pointRingHom g x) ι r)).trans
      (pullbackFreeMap_monomialMap ι (pointRingHom g x) r)
  have hnat := pushforwardFreeMap_baseChange (pointMap ι g x) (toSpec B ι)
    (pullback.snd (toSpec A ι) g) x hsq (familyMonomialMap ι g r) (monomialMap ι B r) _ hψ
  have h1 := epi_pushforwardFreeMap_monomialMap ι n e (B := B) r
  rw [← hnat] at h1
  exact (epi_comp_iff_of_isIso _ _).mp h1

include e in
/-- **The monomials generate `π_* 𝒪(r)`**: on every scheme `T` over `Spec A` and for every `r`,
the adjoint `𝒪_T^{monomials} ⟶ π_* 𝒪(r)` of the pulled-back monomial sections is an
epimorphism; it is checked on the affine open cover of `T` (`epi_of_pullback_openCover`). -/
theorem epi_pushforwardFreeMap_familyMonomialMap (r : ℕ) :
    Epi (pushforwardFreeMap (pullback.snd (toSpec A ι) g) (familyMonomialMap ι g r)) := by
  let U := T.affineOpenCover
  refine Scheme.Modules.epi_of_pullback_openCover (fun i => Spec (U.X i)) U.f
    (fun x => by obtain ⟨y, hy⟩ := U.covers x; exact ⟨U.idx x, y, hy⟩) _ fun i => ?_
  have h := epi_pullbackFreeMap_pushforwardFreeMap_familyMonomialMap ι n e g (B := U.X i) (U.f i) r
  rw [pullbackFreeMap_def] at h
  exact epi_of_epi ((pullbackFreeIso (U.f i) (Monomials ι r)).inv) _

include e in
/-- **The monomials generate `π_*(𝒪(r) ⊗ 𝒪)`** (Nitsure, arXiv:math/0504590v1, §5, p. 26:
`W ⊗ Sym^r V = π_* E(r)`, here only the surjection): on every scheme `T` over `Spec A`, the
monomial sections `𝒪_T^{monomials} ⟶ π_*(𝒪(r) ⊗ 𝒪)` form an epimorphism. -/
theorem epi_directImageMonomialMap (r : ℕ) : Epi (directImageMonomialMap ι g r) := by
  have := epi_pushforwardFreeMap_familyMonomialMap ι n e g r
  rw [directImageMonomialMap_def, pushforwardFreeMap_comp_right]
  infer_instance

end Generation

section Kernel

variable (ι : Type u) {A : Type u} [CommRing A] (n : ℕ) (e : ι ≃ Fin (n + 1)) {Φ : ℚ[X]}
  {T : Scheme.{u}} {g : T ⟶ Spec (CommRingCat.of A)}

/-- **A kernel over an epimorphism onto `π_*(𝒪(r) ⊗ 𝒪)` maps onto `π_* I_Z(r)`**, for a map
`q : F ⟶ π_* 𝒪_Z(r)` presented as `μ` followed by `π_*(𝒪(r) ⊗ 𝒪 ⟶ 𝒪(r) ⊗ 𝒪_Z)` with `μ` an
epimorphism: every `k : ker q ⟶ π_* I_Z(r)` compatible with `μ` is an epimorphism. -/
theorem epi_of_kernel_comp_pushforward_familyTwistedShortComplex
    (Z : (pullback (toSpec A ι) g).IdealSheafData) (r : ℤ) {F : T.Modules}
    {q : F ⟶ (Scheme.Modules.pushforward (pullback.snd (toSpec A ι) g)).obj
      (familyTwistedShortComplex ι g Z r).X₃}
    (μ : F ⟶ (Scheme.Modules.pushforward (pullback.snd (toSpec A ι) g)).obj
      (familyTwistedShortComplex ι g Z r).X₂) [Epi μ]
    (hμ : μ ≫ (Scheme.Modules.pushforward (pullback.snd (toSpec A ι) g)).map
      (familyTwistedShortComplex ι g Z r).g = q)
    (k : Limits.kernel q ⟶ (Scheme.Modules.pushforward (pullback.snd (toSpec A ι) g)).obj
      (familyIdealTwist ι g Z r))
    (hk : k ≫ (Scheme.Modules.pushforward (pullback.snd (toSpec A ι) g)).map
      (familyTwistedShortComplex ι g Z r).f = Limits.kernel.ι q ≫ μ) :
    Epi k := by
  subst hμ
  exact epi_of_isKernel_pushforward_familyTwistedShortComplex ι Z r μ
    (wK := Limits.kernel.condition _) (Limits.kernelIsKernel _) k hk

variable {Z : (pullback (toSpec A ι) g).IdealSheafData}

include e in
/-- The kernel of the evaluation map `𝒪_T^{monomials} ⟶ π_* 𝒪_Z(r)` is quasi-coherent: it is the
kernel of a rank-`⌊Φ(r)⌋₊` locally free quotient (`LocallyFreeQuotient.ofFreeKernelIso`). -/
theorem IsHilbertFamily.isQuasicoherent_kernel_directImageQuotientMap [IsLocallyNoetherian T]
    (hZ : IsHilbertFamily ι Φ g Z) (r : ℕ) (hr : hilbertRegularityBound n Φ ≤ r) :
    (Limits.kernel (directImageQuotientMap ι g Z r)).IsQuasicoherent :=
  haveI := hZ.epi_directImageQuotientMap ι n e r hr
  (SheafOfModules.isQuasicoherent T.ringCatSheaf).prop_of_iso
    (Grassmannian.LocallyFreeQuotient.ofFreeKernelIso (monomialsEquiv ι n e r) _
      (hZ.sheafHasRank_directImageSheaf ι n e r hr)) inferInstance

/-- **The lift of the monomial evaluation of a kernel**: for `ιK : K ⟶ 𝒪_T^{monomials}` with
`ιK ≫ q_Z = 0`, the monomial evaluation `π^* K ⟶ 𝒪(r)` lifts to `π^* K ⟶ I_Z(r)` (through the
right unitor `𝒪(r) ≅ 𝒪(r) ⊗ 𝒪`, `familyIdealTwistLift`). -/
def monomialEvaluationLift (r : ℕ) {K : T.Modules}
    (ιK : K ⟶ SheafOfModules.free (R := T.ringCatSheaf) (Monomials ι r))
    (hK : ιK ≫ directImageQuotientMap ι g Z r = 0) :
    (Scheme.Modules.pullback (pullback.snd (toSpec A ι) g)).obj K ⟶ familyIdealTwist ι g Z r :=
  familyIdealTwistLift ι Z r (monomialEvaluation ι g r ιK)
    (by
      rw [← Z.twistedRestriction_eq_shortComplex_map_g]
      exact (monomialEvaluation_comp_twistedRestriction_eq_zero_iff ι g r ιK Z).mpr hK)

/-- The lift followed by the inclusion `I_Z(r) ⟶ 𝒪(r)` is the monomial evaluation. -/
theorem monomialEvaluationLift_inclusion (r : ℕ) {K : T.Modules}
    (ιK : K ⟶ SheafOfModules.free (R := T.ringCatSheaf) (Monomials ι r))
    (hK : ιK ≫ directImageQuotientMap ι g Z r = 0) :
    monomialEvaluationLift ι r ιK hK ≫ familyIdealTwistInclusion ι Z r =
      monomialEvaluation ι g r ιK :=
  familyIdealTwistLift_inclusion ι Z r _ _

/-- The lift followed by the first map of the twisted sequence is the monomial evaluation
followed by the inverse right unitor. -/
theorem monomialEvaluationLift_comp_f (r : ℕ) {K : T.Modules}
    (ιK : K ⟶ SheafOfModules.free (R := T.ringCatSheaf) (Monomials ι r))
    (hK : ιK ≫ directImageQuotientMap ι g Z r = 0) :
    monomialEvaluationLift ι r ιK hK ≫ (familyTwistedShortComplex ι g Z r).f =
      monomialEvaluation ι g r ιK ≫ (ρ_ (familyTwistingSheaf ι g r)).inv := by
  rw [← cancel_mono (ρ_ (familyTwistingSheaf ι g r)).hom, Category.assoc, Category.assoc,
    Iso.inv_hom_id, Category.comp_id,
    ← Z.whiskerLeft_idealInclusion_eq_shortComplex_map_f]
  exact monomialEvaluationLift_inclusion ι r ιK hK

/-- **The adjoint of the lift is compatible with the monomial sections**: under
`π_*(I_Z(r) ⟶ 𝒪(r) ⊗ 𝒪)`, the adjoint `K ⟶ π_* I_Z(r)` of the lift is `ιK` followed by
`directImageMonomialMap`. -/
theorem homEquiv_monomialEvaluationLift_comp (r : ℕ) {K : T.Modules}
    (ιK : K ⟶ SheafOfModules.free (R := T.ringCatSheaf) (Monomials ι r))
    (hK : ιK ≫ directImageQuotientMap ι g Z r = 0) :
    (pullbackPushforwardAdjunction (pullback.snd (toSpec A ι) g)).homEquiv _ _
        (monomialEvaluationLift ι r ιK hK) ≫
      (Scheme.Modules.pushforward (pullback.snd (toSpec A ι) g)).map
        (familyTwistedShortComplex ι g Z r).f =
      ιK ≫ directImageMonomialMap ι g r := by
  rw [← Adjunction.homEquiv_naturality_right, monomialEvaluationLift_comp_f,
    directImageMonomialMap_def, pushforwardFreeMap_def, ← Adjunction.homEquiv_naturality_left,
    monomialEvaluation_def]
  simp only [Category.assoc]
  rfl

variable [IsLocallyNoetherian T]

include e in
/-- **The closed subscheme of the kernel of the evaluation map is `Z`** (Nitsure,
arXiv:math/0504590v1, §5, p. 26, the "⇒" inclusion of the proof of Theorem 5.2): for a point `Z`
of `Hilb^Φ(T)`, `T` locally Noetherian, and a natural `r ≥ hilbertRegularityBound n Φ`,
`Z(ker q_Z) = Z` for the evaluation map `q_Z : 𝒪_T^{monomials} ⟶ π_* 𝒪_Z(r)`. -/
theorem IsHilbertFamily.evaluationIdeal_kernel_directImageQuotientMap
    (hZ : IsHilbertFamily ι Φ g Z) (r : ℕ) (hr : hilbertRegularityBound n Φ ≤ r) :
    evaluationIdeal ι g r (monomialFamily (A := A) ι r)
      (Limits.kernel.ι (directImageQuotientMap ι g Z r)) = Z := by
  have := hZ.isQuasicoherent_kernel_directImageQuotientMap ι n e r hr
  have := epi_directImageMonomialMap ι n e g r
  refine hZ.evaluationIdeal_eq_of_epi_homEquiv ι n e r hr (monomialFamily (A := A) ι r)
    (Limits.kernel.ι (directImageQuotientMap ι g Z r))
    (monomialEvaluationLift ι r (Limits.kernel.ι (directImageQuotientMap ι g Z r))
      (Limits.kernel.condition _)) ?_ ?_
  · exact epi_of_kernel_comp_pushforward_familyTwistedShortComplex ι Z r
      (directImageMonomialMap ι g r) (directImageQuotientMap_eq_comp ι g Z r).symm _
      (homEquiv_monomialEvaluationLift_comp ι r _ _)
  · rw [monomialEvaluationLift_inclusion, freeTransfer_comp_homogeneousEvaluation_monomialFamily]

include e in
/-- **"⇒": a Hilbert family is the pullback of the universal subscheme along its Grassmannian
point** (Nitsure, arXiv:math/0504590v1, §5, pp. 26–27, proof of Theorem 5.2 for `E = 𝒪`): for a
point `Z` of `Hilb^Φ(T)`, `T` locally Noetherian, and a natural `r ≥ hilbertRegularityBound n Φ`,
the pullback of `universalHilbertSubscheme` along `P^n_φ` for `φ = hZ.grassmannianMap` is `Z`. -/
theorem IsHilbertFamily.universalHilbertSubscheme_comap_grassmannianMap
    (hZ : IsHilbertFamily ι Φ g Z) (r : ℕ) (hr : hilbertRegularityBound n Φ ≤ r) :
    (universalHilbertSubscheme ι r ⌊Φ.eval (r : ℚ)⌋₊ n e).comap
        (baseChangeMap ι
          (Grassmannian.schemeOver (CommRingCat.of A) ⌊Φ.eval (r : ℚ)⌋₊ ((n + r).choose r)).hom g
          (hZ.grassmannianMap ι n e r hr).left (Over.w (hZ.grassmannianMap ι n e r hr))) = Z := by
  have := hZ.epi_directImageQuotientMap ι n e r hr
  exact (universalHilbertSubscheme_comap_classifyingMap ι r ⌊Φ.eval (r : ℚ)⌋₊ n e
    (T := Over.mk g) (directImageQuotientMap ι g Z r)
    (hZ.sheafHasRank_directImageSheaf ι n e r hr)).trans
      (hZ.evaluationIdeal_kernel_directImageQuotientMap ι n e r hr)

end Kernel

end ProjectiveSpace

end AlgebraicGeometry
