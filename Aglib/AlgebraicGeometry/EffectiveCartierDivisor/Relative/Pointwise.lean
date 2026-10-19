/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EffectiveCartierDivisor.Relative.Spectral
public import Aglib.AlgebraicGeometry.Modules.Invertible.Locus
public import Aglib.RingTheory.Flat.PrincipalQuotient.AtPrime
public import Aglib.RingTheory.Regular.Localization
public import Aglib.AlgebraicGeometry.Spec.ResidueField

/-!
# The fibrewise criterion at a single fibre over a Noetherian ring

Kleiman's Lemma 3.4 (*The Picard scheme*, arXiv:math/0504020v1, pp. 22-23) is pointwise: if
`X` and `D` are flat over the base at `x` and the fibre `D_s` is an effective divisor of `X_s`
at `x`, then `D` is an effective divisor of `X` near `x`. This file proves the affine form used
in Kleiman's openness argument (proof of Thm 3.7, p. 24), with the fibre hypothesis imposed on
a set `Z` of base points through `Scheme.Hom.FiberPullbackRankOne`.

For ring maps `ψ : R ⟶ A` and `φ : A ⟶ B` with `Spec A ⟶ Spec R` flat and locally of finite
presentation, `Spec B ⟶ Spec A` a closed immersion, `Spec B ⟶ Spec R` flat and locally of
finite presentation, and `A` Noetherian, the actual ideal of `Spec B` is locally rank one at
every point of `Spec A` lying over `Z`
(`spectralIdeal_isLocallyRankOneAt_of_fiberPullbackRankOne`).

Nakayama's lemma gives a principal generator `a` of the ideal on a principal open set. The
equation `1 ⊗ a` is regular on the fibre over the image point, and the proved local criterion
`Algebra.FlatApproximation.regular_and_flat_at_prime_of_residue_regular`, transported through
localization of the base, makes `a` regular at the stalk. The Noetherian hypothesis is used only
to spread regularity from the stalk to a principal open neighbourhood: the annihilator of `a` is
a finite module (`IsNoetherianRing.exists_away_isSMulRegular_of_atPrime`).
-/

@[expose] public section

noncomputable section
set_option autoImplicit false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

open CategoryTheory Limits AlgebraicGeometry Opposite TopologicalSpace
open AlgebraicGeometry.Scheme
open AlgebraicGeometry.Scheme.Modules
open AlgebraicGeometry.Scheme.Modules.Invertible
open TensorProduct


namespace AlgebraicGeometry.Scheme.Hom

section Regular

attribute [local instance] Algebra.TensorProduct.rightAlgebra

/-- A principal generator of the actual spectral ideal is regular at every prime over a point
of `Z`, when the ideal pulls back to locally rank-one modules along the morphisms into the
fibres over `Z`. The base can be non-Noetherian. -/
theorem isSMulRegular_atPrime_of_fiberPullbackRankOne {R A B : CommRingCat.{u}} (ψ : R ⟶ A)
    (φ : A ⟶ B) [Flat (Spec.map ψ)] [LocallyOfFinitePresentation (Spec.map ψ)]
    [IsClosedImmersion (Spec.map φ)] [Flat (Spec.map φ ≫ Spec.map ψ)] {Z : Set (Spec R)}
    (hM : FiberPullbackRankOne (Spec.map ψ) (idealModule (Spec.map φ)) Z)
    (a : A) (hker : RingHom.ker φ.hom = Ideal.span {a}) (Q : Spec A)
    (hQ : Spec.map ψ Q ∈ Z) :
    IsSMulRegular (Localization.AtPrime Q.asIdeal)
      (algebraMap A (Localization.AtPrime Q.asIdeal) a) := by
  have hflat : ψ.hom.Flat := Flat.SpecMap_iff.mp inferInstance
  have hfp := (LocallyOfFinitePresentation.SpecMap_iff ψ).mp inferInstance
  have hflatB : (ψ ≫ φ).hom.Flat := by
    apply Flat.SpecMap_iff.mp
    rw [Spec.map_comp]
    infer_instance
  have hsurj := IsClosedImmersion.surjective_of_specMap φ
  algebraize [ψ.hom, φ.hom, (ψ ≫ φ).hom]
  have : IsScalarTower R A B := IsScalarTower.of_algebraMap_eq' rfl
  let : Module.Flat R A := hflat
  let : Algebra.FinitePresentation R A := hfp
  let : Module.Flat R B := hflatB
  apply Algebra.isSMulRegular_atPrime_of_fiber_regular (R := R) a Q.asIdeal
  apply isSMulRegular_one_tmul_of_idealPullback_rankOne R A B (Q.asIdeal.under R).ResidueField
    hsurj a hker
  have hsq := (tensorSpecProjection_isPullback R A (Q.asIdeal.under R).ResidueField).w
  refine hM.of_comp_eq _ (Q.asIdeal.under R).ResidueField
    (Spec.map (CommRingCat.ofHom (algebraMap R _))) ?_ _ hsq.symm
  convert hQ using 1
  exact (Spec.map_algebraMap_residueField_closedPoint (Q.asIdeal.under R)).trans
    (PrimeSpectrum.ext rfl)

end Regular

/-- **Pointwise affine criterion** (the whole-fiber form of Kleiman, Lemma 3.4, (ii) ⇒ (i): the
fibers over `Z` are effective Cartier everywhere and `Spec B` is flat over the whole base; `A`
Noetherian): the actual spectral ideal is locally rank one at every point lying over `Z`. -/
theorem spectralIdeal_isLocallyRankOneAt_of_fiberPullbackRankOne {R A B : CommRingCat.{u}}
    [IsNoetherianRing A] (ψ : R ⟶ A) (φ : A ⟶ B) [Flat (Spec.map ψ)]
    [LocallyOfFinitePresentation (Spec.map ψ)] [IsClosedImmersion (Spec.map φ)]
    [Flat (Spec.map φ ≫ Spec.map ψ)] [LocallyOfFinitePresentation (Spec.map φ ≫ Spec.map ψ)]
    {Z : Set (Spec R)} (hM : FiberPullbackRankOne (Spec.map ψ) (idealModule (Spec.map φ)) Z)
    (P : Spec A) (hP : Spec.map ψ P ∈ Z) :
    IsLocallyRankOneAt (idealModule (Spec.map φ)) P := by
  have hx := hM.fieldPoint P.asIdeal.ResidueField
    (Spec.map (CommRingCat.ofHom (algebraMap A P.asIdeal.ResidueField)))
    (by
      convert hP using 2
      exact (Spec.map_algebraMap_residueField_closedPoint P.asIdeal).trans
        (PrimeSpectrum.ext rfl))
  obtain ⟨s, hs, a, ha⟩ := exists_away_surjective_idealGenerator_of_fieldPoint φ
    (spectralIdeal_fg ψ φ) P.asIdeal hx
  have hspan := _root_.Ideal.idealMap_eq_span_of_localized_surjective (RingHom.ker φ.hom)
    (.powers s) a ha
  let S := Localization.Away s
  let loc := CommRingCat.ofHom (algebraMap A S)
  let φs := CommRingCat.ofHom
    (IsLocalization.Away.map (Localization.Away s) (Localization.Away (φ s)) φ.hom s)
  have : Flat (Spec.map (ψ ≫ loc)) := by
    rw [Spec.map_comp]
    infer_instance
  have : LocallyOfFinitePresentation (Spec.map (ψ ≫ loc)) := by
    rw [Spec.map_comp]
    infer_instance
  have := _root_.AlgebraicGeometry.Scheme.isClosedImmersion_specMap_localizationAway φ s
  have := _root_.AlgebraicGeometry.Scheme.flat_specMap_localizationAway_comp ψ φ s
  have hsq := _root_.AlgebraicGeometry.Scheme.isPullback_specMap_localizationAway φ s
  have hw : Spec.map (CommRingCat.ofHom (algebraMap B (Localization.Away (φ s)))) ≫
      Spec.map φ = Spec.map φs ≫ Spec.map loc := hsq.w.symm
  have hiso : IsIso (idealPullbackMap (Spec.map φ) (Spec.map φs) (Spec.map loc)
      (Spec.map (CommRingCat.ofHom (algebraMap B (Localization.Away (φ s))))) hw) :=
    idealPullbackMap_isIso_of_isOpenImmersion _ _ _ _ _ hsq.flip
  let eI := asIso (idealPullbackMap (Spec.map φ) (Spec.map φs) (Spec.map loc)
    (Spec.map (CommRingCat.ofHom (algebraMap B (Localization.Away (φ s))))) hw)
  have hM' := (hM.pullback (Spec.map loc) (Spec.map (ψ ≫ loc)) (𝟙 _)
    (by rw [Spec.map_comp, Category.comp_id])).of_iso eI
  have hdisj : Disjoint (Submonoid.powers s : Set A) P.asIdeal :=
    (Ideal.disjoint_powers_iff_notMem_of_isPrime s).mpr hs
  let Q : Ideal S := P.asIdeal.map (algebraMap A S)
  have hQprime : Q.IsPrime :=
    IsLocalization.isPrime_of_isPrime_disjoint (.powers s) S P.asIdeal inferInstance hdisj
  have hQunder : Q.comap (algebraMap A S) = P.asIdeal :=
    IsLocalization.under_map_of_isPrime_disjoint (.powers s) S inferInstance hdisj
  let Q' : Spec (CommRingCat.of S) := ⟨Q, hQprime⟩
  have hloc : Spec.map loc Q' = P := PrimeSpectrum.ext hQunder
  have hQ'Z : Spec.map (ψ ≫ loc) Q' ∈ (𝟙 (Spec R)) ⁻¹' Z := by
    change Spec.map ψ (Spec.map loc Q') ∈ Z
    rw [hloc]
    exact hP
  have hker' : RingHom.ker φs.hom = Ideal.span {algebraMap A S a.val} :=
    (CommRingCat.ker_localizationAway_map φ s).trans hspan
  have : IsNoetherianRing S := IsLocalization.isNoetherianRing (.powers s) S inferInstance
  have hregQ := isSMulRegular_atPrime_of_fiberPullbackRankOne (ψ ≫ loc) φs hM' _ hker' Q' hQ'Z
  obtain ⟨f, hf, hreg⟩ :=
    IsNoetherianRing.exists_away_isSMulRegular_of_atPrime (algebraMap A S a.val) Q hregQ
  have hspan' : (RingHom.ker φs.hom).map (algebraMap S (Localization.Away f)) =
      Ideal.span {algebraMap S (Localization.Away f) (algebraMap A S a.val)} := by
    rw [hker', Ideal.map_span, Set.image_singleton]
  let b := _root_.Ideal.regularPrincipalIdealBasis _ _ hreg hspan'
  let e := (IsLocalizedModule.iso (.powers f)
    (Algebra.idealMap (Localization.Away f) (RingHom.ker φs.hom))).extendScalarsOfIsLocalization
      (.powers f) (Localization.Away f)
  let W : (Spec (CommRingCat.of S)).Opens := PrimeSpectrum.basicOpen f
  have hAt : IsLocallyRankOneAt (idealModule (Spec.map φs)) Q' := by
    refine ⟨W, W.ι, inferInstance, ?_, ?_⟩
    · rw [Scheme.Opens.range_ι]
      exact hf
    · let e1 := tildeBasicOpenBasisIso (ModuleCat.of (CommRingCat.of S) (RingHom.ker φs.hom)) f
        (b.map e.symm)
      exact isLocallyRankOne_of_iso _ (e1 ≪≫ (Scheme.Modules.restrictFunctor W.ι).mapIso
        (affineIdealIso φs) ≪≫ (Scheme.Modules.restrictFunctorIsoPullback W.ι).app _)
        (trivialLineBundle _).property
  have hP' := (hAt.of_iso eI.symm).of_pullback (Spec.map loc)
  rwa [hloc] at hP'

end AlgebraicGeometry.Scheme.Hom
