/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Morphisms.Smooth.GenericIntegralOpen
public import Aglib.AlgebraicGeometry.Curves.Normalization.GenericCoverBaseChange
public import Aglib.AlgebraicGeometry.Descent.FinitePresentation.ClosedModelMaps
public import Aglib.AlgebraicGeometry.Curves.Normalization.GenericCoverModels
public import Aglib.RingTheory.Localization.FiniteFieldCapture
public import Aglib.AlgebraicGeometry.Descent.FinitePresentation.GenericArrow
public import Aglib.AlgebraicGeometry.Morphisms.Finite.GenericOpen
public import Aglib.AlgebraicGeometry.Morphisms.Surjective.GenericOpen
public import Aglib.AlgebraicGeometry.Limits.Monomorphisms
public import Aglib.RingTheory.Localization.FiniteIntegralCaptureBase
public import Aglib.AlgebraicGeometry.Morphisms.Dominant.Spec
public import Mathlib.AlgebraicGeometry.Morphisms.SchemeTheoreticallyDominant
public import Aglib.AlgebraicGeometry.Morphisms.Smooth.GenericFieldOpen
public import Aglib.AlgebraicGeometry.Limits.ImmersionBaseChange
public import Mathlib.AlgebraicGeometry.Morphisms.Finite
public import Mathlib.AlgebraicGeometry.PullbackCarrier
public import Aglib.AlgebraicGeometry.Morphisms.Finite.Coproduct
public import Aglib.AlgebraicGeometry.Geometrically.Integral.SmoothGenericIntegrality
public import Aglib.AlgebraicGeometry.Curves.Normalization.FiniteFieldModel
public import Aglib.AlgebraicGeometry.Curves.Normalization.FiniteFieldCover
public import Aglib.AlgebraicGeometry.Curves.SmoothGeometry

/-! # The actual generic finite cover of an original proper curve family

The original finite field cover is constructed internally. Its finite family,
sections, and projective embeddings descend through one common coefficient
stage and one finite capture inside the same field. Joint coverage is spread
using the closed union of the original proper branch images, never individual
branch surjectivity. The original finite-base pullback over an actual principal
open is then used for every branch at once.

The output is actual data, including the finite field stage, canonical affine
base realization, original Model/Model.Map comparisons, sections, and relative
projective embeddings. No externally supplied generic cover or spreading
certificate is a premise. This geometric result alone is not proper sheaf
constructibility or a smooth base-change theorem.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace
open AlgebraicGeometry.Scheme.FinitePresentationDescent
open Algebra.FiniteTypeSubalgebraLimit IsFractionRing
open AlgebraicGeometry.Scheme.OverField.Curve.Normalization.GenericCover

namespace AlgebraicGeometry.Scheme.OverField.Curve.Normalization

universe u

private theorem exists_captured_cover_models
    (R K L : Type u) [CommRing R] [IsDomain R] [IsNoetherianRing R]
    [Field K] [Algebra R K] [IsFractionRing R K]
    [Field L] [Algebra K L] [Algebra R L] [IsScalarTower R K L]
    [Module.Finite K L]
    {X : Scheme.{u}} (p : X ⟶ Spec (.of R)) [IsProper p]
    {I : Type u} [Finite I] (C : I → Scheme.{u})
    (q : ∀ i, C i ⟶ Spec (.of L)) [∀ i, IsProper (q i)]
    (ν : ∀ i, C i ⟶ pullback p (fieldMap R L))
    (hν : ∀ i, ν i ≫ pullback.snd p (fieldMap R L) = q i)
    (σ : ∀ i, Spec (.of L) ⟶ C i) (hσ : ∀ i, σ i ≫ q i = 𝟙 _)
    (P : Set I) (hpoint : ∀ i : P, IsIso (q i))
    (n : {i : I // i ∉ P} → ℕ)
    (e : ∀ i : {i : I // i ∉ P}, C i ⟶
      ProjectiveSpace L (ULift.{u} (Fin (n i + 1))))
    [∀ i, IsClosedImmersion (e i)]
    (he : ∀ i, e i ≫ ProjectiveSpace.toSpec L (ULift.{u} (Fin (n i + 1))) = q i) :
    ∃ r : R, r ≠ 0 ∧ ∃ hr : algebraMap R L r ≠ 0,
      ∃ B : Subalgebra R L, Module.Finite R B ∧
        Function.Injective (finiteSubalgebraAwayMap B r hr) ∧
        (letI : Algebra (Localization.Away (algebraMap R B r)) L :=
          (finiteSubalgebraAwayMap B r hr).toRingHom.toAlgebra
         IsFractionRing (Localization.Away (algebraMap R B r)) L) ∧
        (let Br := Localization.Away (algebraMap R B r)
         let χ := (finiteSubalgebraAwayMap B r hr).toRingHom
         let κ := Spec.map (CommRingCat.ofHom χ)
         ∃ N : Model κ (pullback.snd p (fieldMap R L)),
         ∃ M : ∀ i, Model κ (q i),
           IsProper N.f ∧ (∀ i, IsProper (M i).f) ∧
           (∃ ρ : N.X ⟶ X,
             IsPullback ρ N.f p (Spec.map (CommRingCat.ofHom (algebraMap R Br))) ∧
             N.p ≫ ρ = pullback.fst p (fieldMap R L)) ∧
           (∀ i, Nonempty (Model.Map (M i) N (Over.homMk (ν i) (hν i)))) ∧
           (∃ σB : ∀ i, Spec (.of Br) ⟶ (M i).X,
             (∀ i, σB i ≫ (M i).f = 𝟙 _) ∧
             ∀ i, κ ≫ σB i = σ i ≫ (M i).p) ∧
           (∀ i : P, IsIso (M i).f) ∧
           ∀ i : {i : I // i ∉ P},
             ∃ eB : (M i).X ⟶ ProjectiveSpace Br (ULift.{u} (Fin (n i + 1))),
               IsClosedImmersion eB ∧
               eB ≫ ProjectiveSpace.toSpec Br (ULift.{u} (Fin (n i + 1))) = (M i).f ∧
               (M i).p ≫ eB = e i ≫ ProjectiveSpace.map χ
                 (ULift.{u} (Fin (n i + 1)))) := by
  classical
  obtain ⟨a, N, M, hN, hM, ⟨ρ, hρ, hρcomp⟩, arrows,
      ⟨σa, hσa, hσcomp⟩, hpointa, embeddings⟩ :=
    exists_common_models R L p C q ν hν σ hσ P hpoint n e he
  obtain ⟨r, hr, hrL, B, hB, hinj, ⟨ψ, hψ⟩, hfrac⟩ :=
    IsFractionRing.exists_finiteSubalgebra_away_factor_fractionField R K
      (stage R L a) ⟨a, rfl⟩
  let Br := Localization.Away (algebraMap R B r)
  let χ := (finiteSubalgebraAwayMap B r hrL).toRingHom
  let φ := (stage R L a).val.toRingHom
  have hfactor : χ.comp ψ.toRingHom = φ := congrArg AlgHom.toRingHom hψ
  let κ := Spec.map (CommRingCat.ofHom χ)
  let δ := Spec.map (CommRingCat.ofHom ψ.toRingHom)
  let hf := ProjectiveSpace.spec_factor φ ψ.toRingHom χ hfactor
  let NB := N.factorBase κ δ hf
  let MB (i : I) := (M i).factorBase κ δ hf
  let : IsProper N.f := hN
  let (i : I) : IsProper (M i).f := hM i
  have hNB : IsProper NB.f := inferInstanceAs (IsProper (pullback.snd N.f δ))
  have hMB (i : I) : IsProper (MB i).f :=
    inferInstanceAs (IsProper (pullback.snd (M i).f δ))
  let ρB : NB.X ⟶ X := pullback.fst N.f δ ≫ ρ
  have hδ : δ ≫ stageStructure R L a =
      Spec.map (CommRingCat.ofHom (algebraMap R Br)) := by
    rw [← Spec.map_comp]
    change Spec.map (CommRingCat.ofHom
      (ψ.toRingHom.comp (algebraMap R (stage R L a)))) = _
    exact congrArg (fun η : R →+* Br => Spec.map (CommRingCat.ofHom η))
      ψ.comp_algebraMap
  have hρB : IsPullback ρB NB.f p
      (Spec.map (CommRingCat.ofHom (algebraMap R Br))) := by
    have H := (IsPullback.of_hasPullback N.f δ).paste_horiz hρ
    change IsPullback (pullback.fst N.f δ ≫ ρ) (pullback.snd N.f δ) p _
    rw [hδ] at H
    exact H
  have hρBcomp : NB.p ≫ ρB = pullback.fst p (fieldMap R L) := by
    dsimp only [ρB]
    rw [← Category.assoc]
    have hfst : NB.p ≫ pullback.fst N.f δ = N.p := by
      exact (IsPullback.of_hasPullback N.f δ).lift_fst _ _ _
    rw [hfst, hρcomp]
  let σB (i : I) : Spec (.of Br) ⟶ (MB i).X :=
    pullback.lift (δ ≫ σa i) (𝟙 _) (by simp only [Category.assoc, hσa,
      Category.comp_id, Category.id_comp])
  have hσB (i : I) : σB i ≫ (MB i).f = 𝟙 _ := pullback.lift_snd _ _ _
  have hσBcomp (i : I) : κ ≫ σB i = σ i ≫ (MB i).p := by
    have hfst : (MB i).p ≫ pullback.fst (M i).f δ = (M i).p :=
      (IsPullback.of_hasPullback (M i).f δ).lift_fst _ _ _
    have hsnd : (MB i).p ≫ pullback.snd (M i).f δ = q i ≫ κ :=
      (IsPullback.of_hasPullback (M i).f δ).lift_snd _ _ _
    have hσfst : σB i ≫ pullback.fst (M i).f δ = δ ≫ σa i :=
      pullback.lift_fst _ _ _
    have hσsnd : σB i ≫ pullback.snd (M i).f δ = 𝟙 _ :=
      pullback.lift_snd _ _ _
    apply pullback.hom_ext (f := (M i).f) (g := δ)
    · rw [Category.assoc, hσfst, Category.assoc, hfst,
        ← Category.assoc, hf, hσcomp]
    · rw [Category.assoc, hσsnd, Category.assoc, hsnd,
        ← Category.assoc, hσ, Category.id_comp, Category.comp_id]
  refine ⟨r, hr, hrL, B, hB, hinj, hfrac, NB, MB, hNB, hMB,
    ⟨ρB, hρB, hρBcomp⟩, ?_, ⟨σB, hσB, hσBcomp⟩, ?_, ?_⟩
  · intro i
    exact ⟨(Classical.choice (arrows i)).factorBase κ δ hf⟩
  · intro i
    let : IsIso (M i).f := hpointa i
    exact inferInstanceAs (IsIso (pullback.snd (M i).f δ))
  · intro i
    obtain ⟨ea, hea, hstruct, hgeneric⟩ := embeddings i
    let : IsClosedImmersion ea := hea
    exact factorBase_projective_embedding φ ψ.toRingHom χ hfactor
      (ULift.{u} (Fin (n i + 1))) (M i) ea hstruct (e i) (he i) hgeneric

private theorem exists_common_property_opens
    (A L : Type u) [CommRing A] [IsDomain A] [IsNoetherianRing A]
    [Field L] [Algebra A L] [IsFractionRing A L]
    {W : Scheme.{u}} {s : W ⟶ Spec (.of L)}
    (N : Model (Spec.algebraMap A L) s) [IsProper N.f]
    {I : Type u} [Finite I] {C : I → Scheme.{u}}
    {q : ∀ i, C i ⟶ Spec (.of L)}
    (M : ∀ i, Model (Spec.algebraMap A L) (q i)) [∀ i, IsProper (M i).f]
    {m : ∀ i, Over.mk (q i) ⟶ Over.mk s}
    (a : ∀ i, Model.Map (M i) N (m i))
    [∀ i, IsFinite (m i).left] [Surjective (Sigma.desc fun i => (m i).left)]
    (J : Set I) [∀ i : J, SmoothOfRelativeDimension 1 (q i)]
    [∀ i : J, GeometricallyIntegral (q i)] :
    ∃ V : (Spec (.of A)).Opens, genericPoint (Spec (.of A)) ∈ V ∧
      (∀ i, ∃ U : (Spec (.of A)).Opens, V ≤ U ∧
        IsFinite ((a i).hom.left ∣_ (N.f ⁻¹ᵁ U))) ∧
      (∀ i : J, ∃ U : (Spec (.of A)).Opens, V ≤ U ∧
        SmoothOfRelativeDimension 1 ((M i).f ∣_ U) ∧
        GeometricallyIntegral ((M i).f ∣_ U)) ∧
      (∀ x : N.X, N.f x ∈ V → ∃ i, ∃ c : (M i).X, (a i).hom.left c = x) := by
  classical
  let π := Spec.algebraMap A L
  let η := genericPoint (Spec (.of A))
  let : IsDominant π := Scheme.specMap_dominant_of_injective _
    (IsFractionRing.injective A L)
  have hproper (i : I) : IsProper (a i).hom.left := by
    let : IsProper ((a i).hom.left ≫ N.f) := by
      have hw : (a i).hom.left ≫ N.f = (M i).f := Over.w (a i).hom
      rw [hw]
      infer_instance
    exact IsProper.of_comp (a i).hom.left N.f
  let : ∀ i, IsProper (a i).hom.left := hproper
  have hfinite (i : I) : ∃ U : (Spec (.of A)).Opens,
      η ∈ U ∧ IsFinite ((a i).hom.left ∣_ (N.f ⁻¹ᵁ U)) := by
    let : IsFinite (pullback.snd (a i).hom.left (N.f.fiberι η)) :=
      Model.Map.finite_genericFibre π (M i) N (a i)
    exact Scheme.exists_open_isFinite_of_finite_fibreBaseChange N.f (a i).hom.left η
  choose U hηU hU using hfinite
  have hsmooth (i : J) : ∃ V : (Spec (.of A)).Opens,
      η ∈ V ∧ SmoothOfRelativeDimension 1 ((M i).f ∣_ V) ∧
      GeometricallyIntegral ((M i).f ∣_ V) := by
    let E := (M i).square.isoPullback
    have hE : E.hom ≫ pullback.snd (M i).f π = q i :=
      (M i).square.isoPullback_hom_snd
    let : SmoothOfRelativeDimension 1 (pullback.snd (M i).f π) := by
      apply (MorphismProperty.cancel_left_of_respectsIso
        (P := @SmoothOfRelativeDimension 1) E.hom _).mp
      rw [hE]
      infer_instance
    let : GeometricallyIntegral (pullback.snd (M i).f π) := by
      apply (MorphismProperty.cancel_left_of_respectsIso
        (P := @GeometricallyIntegral) E.hom _).mp
      rw [hE]
      infer_instance
    exact Scheme.exists_generic_open_smooth_geometricallyIntegral A L (M i).f 1
  choose V hηV hV using hsmooth
  let ν := Sigma.desc fun i => (a i).hom.left
  let : Surjective (pullback.snd ν (N.f.fiberι η)) :=
    Model.Map.surjective_genericFibre_sigma π N M a
  have hjoint (x : N.X) (hx : N.f x = η) :
      ∃ i, ∃ c : (M i).X, (a i).hom.left c = x := by
    let z : Spec ((Spec (.of A)).residueField η) := Nonempty.some inferInstance
    have hxz : N.f x = (Spec (.of A)).fromSpecResidueField η z := by
      simpa only [Scheme.fromSpecResidueField_apply] using hx
    obtain ⟨xη, hfst, _⟩ := Scheme.Pullback.exists_preimage_pullback
      (f := N.f) (g := (Spec (.of A)).fromSpecResidueField η) x z hxz
    obtain ⟨w, hw⟩ := (pullback.snd ν (N.f.fiberι η)).surjective xη
    obtain ⟨i, c, hc⟩ := Scheme.exists_sigmaι_eq (pullback.fst ν (N.f.fiberι η) w)
    have hν : ν (pullback.fst ν (N.f.fiberι η) w) = x := by
      calc
        _ = N.f.fiberι η (pullback.snd ν (N.f.fiberι η) w) :=
          congrArg (fun f : pullback ν (N.f.fiberι η) ⟶ N.X => f w)
            (pullback.condition (f := ν) (g := N.f.fiberι η))
        _ = x := by rw [hw]; exact hfst
    refine ⟨i, c, ?_⟩
    have hd := congrArg (fun f : (M i).X ⟶ N.X => f c)
      (Sigma.ι_comp_desc (fun j => (a j).hom.left) i)
    exact hd.symm.trans ((congrArg ν hc).trans hν)
  obtain ⟨W, hηW, hW⟩ :=
    Scheme.exists_generic_open_jointly_surjective_proper_family A N.f
      (fun i => (a i).hom.left) hjoint
  let O := W ⊓ (⨅ i, U i) ⊓ (⨅ i, V i)
  have hOW : O ≤ W := le_trans inf_le_left inf_le_left
  have hOU (i : I) : O ≤ U i :=
    le_trans (le_trans inf_le_left inf_le_right) (iInf_le _ i)
  have hOV (i : J) : O ≤ V i := le_trans inf_le_right (iInf_le _ i)
  refine ⟨O, ?_, (fun i => ⟨U i, hOU i, hU i⟩),
    (fun i => ⟨V i, hOV i, (hV i).1, (hV i).2⟩), ?_⟩
  · refine ⟨⟨hηW, ?_⟩, ?_⟩
    · change η ∈ ((⨅ i, U i : (Spec (.of A)).Opens) : Set (Spec (.of A)))
      rw [TopologicalSpace.Opens.coe_iInf]
      exact Set.mem_iInter.mpr hηU
    · change η ∈ ((⨅ i, V i : (Spec (.of A)).Opens) : Set (Spec (.of A)))
      rw [TopologicalSpace.Opens.coe_iInf]
      exact Set.mem_iInter.mpr hηV
  · intro x hx
    exact hW x (hOW hx)

private theorem captureAwayDomain
    {R L : Type u} [CommRing R] [Field L] [Algebra R L]
    (B : Subalgebra R L) (r : R) (hrL : algebraMap R L r ≠ 0) :
    IsDomain (Localization.Away (algebraMap R B r)) :=
  Localization.Away.isDomain (fun hz => hrL (by
    simpa only [Subalgebra.coe_algebraMap, Subalgebra.coe_zero] using
      congrArg (fun z : B => (z : L)) hz))

private theorem exists_captured_base_principal_open
    (R K L : Type u) [CommRing R] [IsDomain R]
    [Field K] [Algebra R K] [IsFractionRing R K]
    [Field L] [Algebra R L] [Algebra K L] [IsScalarTower R K L]
    (r : R) (hr : r ≠ 0) (hrL : algebraMap R L r ≠ 0)
    (B : Subalgebra R L) [Module.Finite R B]
    (hinj : Function.Injective (finiteSubalgebraAwayMap B r hrL))
    (V : (Spec (.of (Localization.Away (algebraMap R B r)))).Opens)
    (hV : letI := captureAwayDomain B r hrL
      genericPoint (Spec (.of (Localization.Away (algebraMap R B r)))) ∈ V) :
    ∃ d : Localization.Away r, d ≠ 0 ∧
      (letI : IsDomain (Localization.Away r) := Localization.Away.isDomain hr
       let U : (Spec (.of (Localization.Away r))).Opens := PrimeSpectrum.basicOpen d
       let b := Spec.map (CommRingCat.ofHom (finiteSubalgebraAwayBaseMap B r).toRingHom)
       let T := pullback b U.ι
       genericPoint (Spec (.of (Localization.Away r))) ∈ U ∧
       b ⁻¹ᵁ U ≤ V ∧ IsFinite (pullback.snd b U.ι) ∧
       Surjective (pullback.snd b U.ι) ∧ IsAffine T ∧ IsIntegral T ∧
       ∃ κT : Spec (.of L) ⟶ T,
         κT ≫ pullback.fst b U.ι =
           Spec.map (CommRingCat.ofHom (finiteSubalgebraAwayMap B r hrL).toRingHom) ∧
         IsDominant κT ∧ Function.Injective κT.appTop ∧
         (pullback.snd b U.ι).appTop.hom.Finite) := by
  classical
  have hR : Function.Injective (algebraMap R L) := by
    rw [IsScalarTower.algebraMap_eq R K L]
    exact (algebraMap K L).injective.comp (IsFractionRing.injective R K)
  let : IsDomain (Localization.Away r) := Localization.Away.isDomain hr
  let := captureAwayDomain B r hrL
  let Rr := Localization.Away r
  let Br := Localization.Away (algebraMap R B r)
  let b : Spec (.of Br) ⟶ Spec (.of Rr) :=
    Spec.map (CommRingCat.ofHom (finiteSubalgebraAwayBaseMap B r).toRingHom)
  let κ : Spec (.of L) ⟶ Spec (.of Br) :=
    Spec.map (CommRingCat.ofHom (finiteSubalgebraAwayMap B r hrL).toRingHom)
  let : IsFinite b := (IsFinite.SpecMap_iff _).mpr
    (finiteSubalgebraAwayBaseMap_finite B r)
  let : Surjective b := ⟨finiteSubalgebraAwayBaseMap_comap_surjective B r hR⟩
  let : IsDominant b := Scheme.specMap_dominant_of_injective _
    (finiteSubalgebraAwayBaseMap_injective B r hR)
  let : IsDominant κ := Scheme.specMap_dominant_of_injective _ hinj
  obtain ⟨W, hW, hWV⟩ :=
    Scheme.exists_generic_open_preimage_subset_of_isFinite_of_genericPoint_mem Rr b V hV
  obtain ⟨_, ⟨d, rfl⟩, hd, hsub⟩ :=
    TopologicalSpace.Opens.isBasis_iff_nbhd.mp PrimeSpectrum.isBasis_basic_opens hW
  let U : (Spec (.of Rr)).Opens := PrimeSpectrum.basicOpen d
  have hd0 : d ≠ 0 := by
    intro h
    subst d
    simp only [PrimeSpectrum.basicOpen_zero, TopologicalSpace.Opens.mem_bot] at hd
  have hUV : b ⁻¹ᵁ U ≤ V := le_trans (fun _ hx => hsub hx) hWV
  let : IsAffine U := IsAffineOpen.Spec_basicOpen d
  let T := pullback b U.ι
  let g := κ ≫ b
  have hg (y : Spec (.of L)) : g y = genericPoint (Spec (.of Rr)) := by
    rw [Subsingleton.elim y (genericPoint (Spec (.of L)))]
    exact Scheme.map_genericPoint_of_isDominant _ g
  have hrange : Set.range g ⊆ Set.range U.ι := by
    rintro _ ⟨y, rfl⟩
    exact ⟨⟨g y, (hg y).symm ▸ hd⟩, rfl⟩
  let j : Spec (.of L) ⟶ U := IsOpenImmersion.lift U.ι g hrange
  have hj : j ≫ U.ι = κ ≫ b := IsOpenImmersion.lift_fac _ _ hrange
  let κT : Spec (.of L) ⟶ T := pullback.lift κ j hj.symm
  have hκT : κT ≫ pullback.fst b U.ι = κ := pullback.lift_fst _ _ _
  let : Nonempty T := ⟨κT (genericPoint (Spec (.of L)))⟩
  let : IsIntegral T := isIntegral_of_isOpenImmersion (pullback.fst b U.ι)
  let : IsDominant (κT ≫ pullback.fst b U.ι) := hκT.symm ▸ inferInstance
  let : IsDominant κT := IsDominant.of_comp_of_isOpenImmersion κT (pullback.fst b U.ι)
  let : IsSchemeTheoreticallyDominant κT := IsSchemeTheoreticallyDominant.of_isDominant κT
  refine ⟨d, hd0, hd, hUV, inferInstance, inferInstance, inferInstance, inferInstance,
    κT, hκT, inferInstance, ?_, ?_⟩
  · exact κT.app_injective ⊤
  · exact (pullback.snd b U.ι).finite_appTop

private theorem spread_original_field_cover
    (R K L : Type u) [CommRing R] [IsDomain R] [IsNoetherianRing R]
    [Field K] [Algebra R K] [IsFractionRing R K]
    [Field L] [Algebra K L] [Algebra R L] [IsScalarTower R K L]
    [Module.Finite K L]
    {X : Scheme.{u}} (p : X ⟶ Spec (.of R)) [IsProper p]
    {I : Type u} [Finite I] (C : I → Scheme.{u})
    (q : ∀ i, C i ⟶ Spec (.of L)) [∀ i, IsProper (q i)]
    (ν : ∀ i, C i ⟶ pullback p (fieldMap R L))
    (hν : ∀ i, ν i ≫ pullback.snd p (fieldMap R L) = q i)
    (σ : ∀ i, Spec (.of L) ⟶ C i) (hσ : ∀ i, σ i ≫ q i = 𝟙 _)
    (P : Set I) (hpoint : ∀ i : P, IsIso (q i))
    (n : {i : I // i ∉ P} → ℕ)
    (e : ∀ i : {i : I // i ∉ P}, C i ⟶
      ProjectiveSpace L (ULift.{u} (Fin (n i + 1))))
    [∀ i, IsClosedImmersion (e i)]
    (he : ∀ i, e i ≫ ProjectiveSpace.toSpec L (ULift.{u} (Fin (n i + 1))) = q i)
    [∀ i, IsFinite (ν i)] [Surjective (Sigma.desc ν)]
    [∀ i : {i : I // i ∉ P}, SmoothOfRelativeDimension 1 (q i)]
    [∀ i : {i : I // i ∉ P}, GeometricallyIntegral (q i)] :
    ∃ r : R, r ≠ 0 ∧ ∃ hrL : algebraMap R L r ≠ 0,
    ∃ B : Subalgebra R L, Module.Finite R B ∧
    Function.Injective (finiteSubalgebraAwayMap B r hrL) ∧
    (letI : Algebra (Localization.Away (algebraMap R B r)) L :=
      (finiteSubalgebraAwayMap B r hrL).toRingHom.toAlgebra
     IsFractionRing (Localization.Away (algebraMap R B r)) L) ∧
    ∃ d : Localization.Away r, d ≠ 0 ∧
      (let Br := Localization.Away (algebraMap R B r)
       let U : (Spec (.of (Localization.Away r))).Opens := PrimeSpectrum.basicOpen d
       let β := Spec.map (CommRingCat.ofHom (finiteSubalgebraAwayBaseMap B r).toRingHom)
       let T := pullback β U.ι
       ∃ hAff : IsAffine T, letI : IsAffine T := hAff
       IsIntegral T ∧ IsFinite (pullback.snd β U.ι) ∧ Surjective (pullback.snd β U.ι) ∧
       ∃ κT : Spec (.of L) ⟶ T,
         κT ≫ pullback.fst β U.ι =
           Spec.map (CommRingCat.ofHom (finiteSubalgebraAwayMap B r hrL).toRingHom) ∧
         IsDominant κT ∧ Function.Injective κT.appTop ∧
         (pullback.snd β U.ι).appTop.hom.Finite ∧
       let κS := κT ≫ T.isoSpec.hom
       let δS := T.isoSpec.inv ≫ pullback.fst β U.ι
       ∃ N : Model κS (pullback.snd p (fieldMap R L)),
       ∃ M : ∀ i, Model κS (q i),
         IsProper N.f ∧ (∀ i, IsProper (M i).f) ∧
         (∃ ρ : N.X ⟶ X,
           IsPullback ρ N.f p (δS ≫ Spec.map (CommRingCat.ofHom (algebraMap R Br))) ∧
           N.p ≫ ρ = pullback.fst p (fieldMap R L)) ∧
         ∃ a : ∀ i, Model.Map (M i) N (Over.homMk (ν i) (hν i)),
           (∀ i, IsFinite (a i).hom.left) ∧
           IsFinite (Sigma.desc fun i => (a i).hom.left) ∧
           Surjective (Sigma.desc fun i => (a i).hom.left) ∧
           (∃ σS : ∀ i, Spec Γ(T, ⊤) ⟶ (M i).X,
             (∀ i, σS i ≫ (M i).f = 𝟙 _) ∧
             ∀ i, κS ≫ σS i = σ i ≫ (M i).p) ∧
           (∀ i : P, IsIso (M i).f) ∧
           (∀ i : {i : I // i ∉ P}, SmoothOfRelativeDimension 1 (M i).f ∧
             GeometricallyIntegral (M i).f) ∧
           ∃ χS : Γ(T, ⊤) ⟶ CommRingCat.of L,
             Spec.map χS = κS ∧
             ∀ i : {i : I // i ∉ P},
               ∃ eS : (M i).X ⟶ ProjectiveSpace Γ(T, ⊤) (ULift.{u} (Fin (n i + 1))),
                 IsClosedImmersion eS ∧
                 eS ≫ ProjectiveSpace.toSpec Γ(T, ⊤) (ULift.{u} (Fin (n i + 1))) = (M i).f ∧
                 (M i).p ≫ eS = e i ≫ ProjectiveSpace.map χS.hom
                   (ULift.{u} (Fin (n i + 1)))) := by
  classical
  obtain ⟨r, hr, hrL, B, hB, hinj, hfrac, N, M, hN, hM,
      ⟨ρ, hρ, hρcomp⟩, arrows, ⟨σB, hσB, hσBcomp⟩, hpointB, embeddings⟩ :=
    exists_captured_cover_models R K L p C q ν hν σ hσ P hpoint n e he
  let : Module.Finite R B := hB
  let Br := Localization.Away (algebraMap R B r)
  let χ := (finiteSubalgebraAwayMap B r hrL).toRingHom
  let : Algebra Br L := χ.toAlgebra
  let : IsFractionRing Br L := hfrac
  let : IsDomain Br := captureAwayDomain B r hrL
  let : IsNoetherianRing B := IsNoetherianRing.of_finite R B
  let : IsNoetherianRing Br := IsLocalization.isNoetherianRing
    (Submonoid.powers (algebraMap R B r)) Br inferInstance
  let κ := Spec.map (CommRingCat.ofHom χ)
  let a (i : I) := Classical.choice (arrows i)
  let : IsProper N.f := hN
  let : ∀ i, IsProper (M i).f := hM
  let J := {i : I // i ∉ P}
  let m (i : I) : Over.mk (q i) ⟶ Over.mk (pullback.snd p (fieldMap R L)) :=
    Over.homMk (ν i) (hν i)
  let : ∀ i, IsFinite (m i).left := fun i => inferInstanceAs (IsFinite (ν i))
  let : Surjective (Sigma.desc fun i => (m i).left) :=
    inferInstanceAs (Surjective (Sigma.desc ν))
  obtain ⟨V, hV, hfin, hsm, hjoint⟩ :=
    exists_common_property_opens Br L N M a {i | i ∉ P}
  obtain ⟨d, hd, hU, hUV, hfinite, hsurj, hAff, hInt, κT,
      hκT, hdom, hκinj, hΓfin⟩ :=
    exists_captured_base_principal_open R K L r hr hrL B hinj V hV
  let U : (Spec (.of (Localization.Away r))).Opens := PrimeSpectrum.basicOpen d
  let β := Spec.map (CommRingCat.ofHom (finiteSubalgebraAwayBaseMap B r).toRingHom)
  let T := pullback β U.ι
  let : IsAffine T := hAff
  let : IsIntegral T := hInt
  let κS := κT ≫ T.isoSpec.hom
  let δS := T.isoSpec.inv ≫ pullback.fst β U.ι
  have hfactor : κS ≫ δS = κ := by
    simp only [κS, δS, Category.assoc, Iso.hom_inv_id_assoc]
    exact hκT
  have hδrange : Set.range δS ⊆ V := by
    rintro _ ⟨z, rfl⟩
    apply hUV
    change β (pullback.fst β U.ι (T.isoSpec.inv z)) ∈ U
    have hh := congrArg (fun f => f (T.isoSpec.inv z))
      (pullback.condition (f := β) (g := U.ι))
    change β (pullback.fst β U.ι (T.isoSpec.inv z)) =
      U.ι (pullback.snd β U.ι (T.isoSpec.inv z)) at hh
    rw [hh]
    exact (pullback.snd β U.ι (T.isoSpec.inv z)).property
  obtain ⟨χS, hχS⟩ := Spec.map_surjective κS
  obtain ⟨ψS, hψS⟩ := Spec.map_surjective δS
  have hring : χS.hom.comp ψS.hom = χ := by
    have hh : ψS ≫ χS = CommRingCat.ofHom χ := by
      apply Spec.map_injective
      rw [Spec.map_comp, hχS, hψS]
      exact hfactor
    exact congrArg CommRingCat.Hom.hom hh
  let NS := N.factorBase κS δS hfactor
  let MS (i : I) := (M i).factorBase κS δS hfactor
  let aS (i : I) := (a i).factorBase κS δS hfactor
  have hχnative : Spec.map (CommRingCat.ofHom χS.hom) = κS := hχS
  have hψnative : Spec.map (CommRingCat.ofHom ψS.hom) = δS := hψS
  have hprops := exists_factorBase_cover_properties_of_maps χ ψS.hom χS.hom hring
    κS δS hχnative hψnative hfactor N M a V hδrange hfin hjoint
    σ hσ σB hσB hσBcomp P hpointB hsm n e he embeddings
  obtain ⟨hNS, hMS, hfinS, htotal, htotalSurj,
    ⟨σS, hσS, hσScomp⟩, hpointS, hcurveS, hembS⟩ := hprops
  let ρS : NS.X ⟶ X := pullback.fst N.f δS ≫ ρ
  have hρS : IsPullback ρS NS.f p
      (δS ≫ Spec.map (CommRingCat.ofHom (algebraMap R Br))) :=
    (IsPullback.of_hasPullback N.f δS).paste_horiz hρ
  have hρScomp : NS.p ≫ ρS = pullback.fst p (fieldMap R L) := by
    dsimp only [ρS]
    rw [← Category.assoc]
    have hf : NS.p ≫ pullback.fst N.f δS = N.p :=
      (IsPullback.of_hasPullback N.f δS).lift_fst _ _ _
    rw [hf, hρcomp]
  exact ⟨r, hr, hrL, B, hB, hinj, hfrac, d, hd, hAff, hInt, hfinite, hsurj,
    κT, hκT, hdom, hκinj, hΓfin, NS, MS, hNS, hMS,
    ⟨ρS, hρS, hρScomp⟩, aS, hfinS, htotal, htotalSurj,
    ⟨σS, hσS, hσScomp⟩, hpointS, hcurveS, χS, hχS, hembS⟩

/-- The original localized finite base arrow, with both spectrum objects fixed. -/
abbrev genericCoverBaseMap {R L : Type u} [CommRing R] [Field L] [Algebra R L]
    (B : Subalgebra R L) (r : R) :
    Spec (.of (Localization.Away (algebraMap R B r))) ⟶
      Spec (.of (Localization.Away r)) :=
  Spec.map (show CommRingCat.of (Localization.Away r) ⟶
      CommRingCat.of (Localization.Away (algebraMap R B r)) from
    CommRingCat.ofHom (finiteSubalgebraAwayBaseMap B r).toRingHom)

/-- The literal base resulting from the captured finite algebra and the chosen
principal open. This abbreviation makes no additional choice. -/
abbrev genericCoverBase {R L : Type u} [CommRing R] [Field L] [Algebra R L]
    (B : Subalgebra R L) (r : R) (d : Localization.Away r) : Scheme.{u} :=
  pullback
    (genericCoverBaseMap B r)
    (Scheme.Opens.ι (X := Spec (.of (Localization.Away r))) (PrimeSpectrum.basicOpen d))

/-- Actual field-cover and spread data, with the literal maps and all their
comparison laws. This is output data, not an assumed spreading certificate. -/
structure GenericFiniteCoverData
    (R K : Type u) [CommRing R] [Field K] [Algebra R K]
    (s : Finset (AlgebraicClosure K)) [Algebra R (FiniteField.stage K s)]
    {X : Scheme.{u}} (p : X ⟶ Spec (.of R)) where
  I : Type u
  finiteI : Finite I
  C : I → Scheme.{u}
  q : ∀ i, C i ⟶ Spec (.of (FiniteField.stage K s))
  proper_q : ∀ i, IsProper (q i)
  ν : ∀ i, C i ⟶ pullback p (fieldMap R (FiniteField.stage K s))
  hν : ∀ i, ν i ≫ pullback.snd p (fieldMap R (FiniteField.stage K s)) = q i
  finite_ν : ∀ i, IsFinite (ν i)
  finite_field_cover : IsFinite (Sigma.desc ν)
  surjective_field_cover : Surjective (Sigma.desc ν)
  σ : ∀ i, Spec (.of (FiniteField.stage K s)) ⟶ C i
  hσ : ∀ i, σ i ≫ q i = 𝟙 _
  P : Set I
  point : ∀ i : P, IsIso (q i)
  n : {i : I // i ∉ P} → ℕ
  e : ∀ i : {i : I // i ∉ P}, C i ⟶
    ProjectiveSpace (FiniteField.stage K s) (ULift.{u} (Fin (n i + 1)))
  closed_e : ∀ i, IsClosedImmersion (e i)
  he : ∀ i, e i ≫ ProjectiveSpace.toSpec (FiniteField.stage K s)
    (ULift.{u} (Fin (n i + 1))) = q i
  smooth_q : ∀ i : {i : I // i ∉ P}, SmoothOfRelativeDimension 1 (q i)
  integral_q : ∀ i : {i : I // i ∉ P}, GeometricallyIntegral (q i)
  r : R
  r_ne_zero : r ≠ 0
  hrL : algebraMap R (FiniteField.stage K s) r ≠ 0
  B : Subalgebra R (FiniteField.stage K s)
  finite_B : Module.Finite R B
  χ_injective : Function.Injective (finiteSubalgebraAwayMap B r hrL)
  fractionField :
    letI : Algebra (Localization.Away (algebraMap R B r)) (FiniteField.stage K s) :=
      (finiteSubalgebraAwayMap B r hrL).toRingHom.toAlgebra
    IsFractionRing (Localization.Away (algebraMap R B r)) (FiniteField.stage K s)
  d : Localization.Away r
  d_ne_zero : d ≠ 0
  baseAffine : IsAffine (genericCoverBase B r d)
  baseIntegral : IsIntegral (genericCoverBase B r d)
  finite_base : IsFinite (pullback.snd
    (genericCoverBaseMap B r)
    (Scheme.Opens.ι (X := Spec (.of (Localization.Away r))) (PrimeSpectrum.basicOpen d)))
  surjective_base : Surjective (pullback.snd
    (genericCoverBaseMap B r)
    (Scheme.Opens.ι (X := Spec (.of (Localization.Away r))) (PrimeSpectrum.basicOpen d)))
  κT : Spec (.of (FiniteField.stage K s)) ⟶ genericCoverBase B r d
  κT_fst : κT ≫ pullback.fst
    (genericCoverBaseMap B r)
    (Scheme.Opens.ι (X := Spec (.of (Localization.Away r))) (PrimeSpectrum.basicOpen d)) =
      Spec.map (CommRingCat.ofHom (finiteSubalgebraAwayMap B r hrL).toRingHom)
  κT_dominant : IsDominant κT
  κT_appTop_injective : Function.Injective κT.appTop
  finite_base_appTop : (pullback.snd
    (genericCoverBaseMap B r)
    (Scheme.Opens.ι (X := Spec (.of (Localization.Away r)))
      (PrimeSpectrum.basicOpen d))).appTop.hom.Finite
  N : letI := baseAffine
    Model (κT ≫ (genericCoverBase B r d).isoSpec.hom)
      (pullback.snd p (fieldMap R (FiniteField.stage K s)))
  M : letI := baseAffine
    ∀ i, Model (κT ≫ (genericCoverBase B r d).isoSpec.hom) (q i)
  proper_N : IsProper N.f
  proper_M : ∀ i, IsProper (M i).f
  ρ : N.X ⟶ X
  ρ_square : letI := baseAffine
    IsPullback ρ N.f p
      (((genericCoverBase B r d).isoSpec.inv ≫ pullback.fst
        (genericCoverBaseMap B r)
        (Scheme.Opens.ι (X := Spec (.of (Localization.Away r))) (PrimeSpectrum.basicOpen d))) ≫
          Spec.map (CommRingCat.ofHom
            (algebraMap R (Localization.Away (algebraMap R B r)))))
  ρ_comparison : N.p ≫ ρ = pullback.fst p (fieldMap R (FiniteField.stage K s))
  arrows : ∀ i, Model.Map (M i) N (Over.homMk (ν i) (hν i))
  finite_arrows : ∀ i, IsFinite (arrows i).hom.left
  finite_cover : IsFinite (Sigma.desc fun i => (arrows i).hom.left)
  surjective_cover : Surjective (Sigma.desc fun i => (arrows i).hom.left)
  sections : ∀ i, Spec Γ(genericCoverBase B r d, ⊤) ⟶ (M i).X
  sections_w : ∀ i, sections i ≫ (M i).f = 𝟙 _
  sections_comparison : letI := baseAffine
    ∀ i, (κT ≫ (genericCoverBase B r d).isoSpec.hom) ≫ sections i = σ i ≫ (M i).p
  point_M : ∀ i : P, IsIso (M i).f
  smooth_M : ∀ i : {i : I // i ∉ P}, SmoothOfRelativeDimension 1 (M i).f
  integral_M : ∀ i : {i : I // i ∉ P}, GeometricallyIntegral (M i).f
  χS : Γ(genericCoverBase B r d, ⊤) ⟶ CommRingCat.of (FiniteField.stage K s)
  χS_spec : letI := baseAffine
    Spec.map χS = κT ≫ (genericCoverBase B r d).isoSpec.hom
  eS : ∀ i : {i : I // i ∉ P}, (M i).X ⟶
    ProjectiveSpace Γ(genericCoverBase B r d, ⊤) (ULift.{u} (Fin (n i + 1)))
  closed_eS : ∀ i, IsClosedImmersion (eS i)
  eS_w : ∀ i, eS i ≫ ProjectiveSpace.toSpec Γ(genericCoverBase B r d, ⊤)
    (ULift.{u} (Fin (n i + 1))) = (M i).f
  eS_comparison : ∀ i : {i : I // i ∉ P}, (M i).p ≫ eS i = e i ≫
    ProjectiveSpace.map χS.hom (ULift.{u} (Fin (n i + 1)))



private theorem genericFiniteCoverData_of_original_field_cover
    (R K : Type u) [CommRing R] [IsDomain R] [IsNoetherianRing R]
    [Field K] [Algebra R K] [IsFractionRing R K]
    (s : Finset (AlgebraicClosure K))
    [Algebra R (FiniteField.stage K s)] [IsScalarTower R K (FiniteField.stage K s)]
    {X : Scheme.{u}} (p : X ⟶ Spec (.of R)) [IsProper p]
    {I : Type u} [Finite I] (C : I → Scheme.{u})
    (q : ∀ i, C i ⟶ Spec (.of (FiniteField.stage K s))) [∀ i, IsProper (q i)]
    (ν : ∀ i, C i ⟶ pullback p (fieldMap R (FiniteField.stage K s)))
    (hν : ∀ i, ν i ≫ pullback.snd p (fieldMap R (FiniteField.stage K s)) = q i)
    (σ : ∀ i, Spec (.of (FiniteField.stage K s)) ⟶ C i)
    (hσ : ∀ i, σ i ≫ q i = 𝟙 _)
    (P : Set I) (hpoint : ∀ i : P, IsIso (q i))
    (n : {i : I // i ∉ P} → ℕ)
    (e : ∀ i : {i : I // i ∉ P}, C i ⟶
      ProjectiveSpace (FiniteField.stage K s) (ULift.{u} (Fin (n i + 1))))
    [∀ i, IsClosedImmersion (e i)]
    (he : ∀ i, e i ≫ ProjectiveSpace.toSpec (FiniteField.stage K s)
      (ULift.{u} (Fin (n i + 1))) = q i)
    [∀ i, IsFinite (ν i)] [Surjective (Sigma.desc ν)]
    [∀ i : {i : I // i ∉ P}, SmoothOfRelativeDimension 1 (q i)]
    [∀ i : {i : I // i ∉ P}, GeometricallyIntegral (q i)] :
    Nonempty (GenericFiniteCoverData R K s p) := by
  classical
  obtain ⟨r, hr, hrL, B, hB, hinj, hfrac, d, hd, hAff, hInt, hfinite, hsurj,
      κT, hκT, hdom, hκinj, hΓfin, N, M, hN, hM, ⟨ρ, hρ, hρcomp⟩,
      arrows, hfin, htotal, htotalSurj, ⟨sections, hsections, hsectionscomp⟩,
      hpointM, hcurveM, χS, hχS, embeddings⟩ :=
    spread_original_field_cover R K (FiniteField.stage K s)
      p C q ν hν σ hσ P hpoint n e he
  choose eS hclosedS hstructS hgenericS using embeddings
  exact ⟨{
    I := I
    finiteI := inferInstance
    C := C
    q := q
    proper_q := fun _ => inferInstance
    ν := ν
    hν := hν
    finite_ν := fun _ => inferInstance
    finite_field_cover := Scheme.Hom.isFinite_sigmaDesc C _ ν
    surjective_field_cover := inferInstance
    σ := σ
    hσ := hσ
    P := P
    point := hpoint
    n := n
    e := e
    closed_e := fun _ => inferInstance
    he := he
    smooth_q := fun _ => inferInstance
    integral_q := fun _ => inferInstance
    r := r
    r_ne_zero := hr
    hrL := hrL
    B := B
    finite_B := hB
    χ_injective := hinj
    fractionField := hfrac
    d := d
    d_ne_zero := hd
    baseAffine := hAff
    baseIntegral := hInt
    finite_base := hfinite
    surjective_base := hsurj
    κT := κT
    κT_fst := hκT
    κT_dominant := hdom
    κT_appTop_injective := hκinj
    finite_base_appTop := hΓfin
    N := N
    M := M
    proper_N := hN
    proper_M := hM
    ρ := ρ
    ρ_square := hρ
    ρ_comparison := hρcomp
    arrows := arrows
    finite_arrows := hfin
    finite_cover := htotal
    surjective_cover := htotalSurj
    sections := sections
    sections_w := hsections
    sections_comparison := hsectionscomp
    point_M := hpointM
    smooth_M := fun i => (hcurveM i).1
    integral_M := fun i => (hcurveM i).2
    χS := χS
    χS_spec := hχS
    eS := eS
    closed_eS := hclosedS
    eS_w := hstructS
    eS_comparison := hgenericS }⟩

/-- An original proper family of generic dimension at most one has an actual
finite cover after a genuine nonempty generic base restriction and finite base
extension. The finite field cover, all common models, sections and relative
projective embeddings are constructed internally and retained in the output. -/
theorem exists_generic_finite_cover
    (R K : Type u) [CommRing R] [IsDomain R] [IsNoetherianRing R]
    [Field K] [Algebra R K] [IsFractionRing R K]
    {X : Scheme.{u}} (p : X ⟶ Spec (.of R)) [IsProper p]
    (hd : topologicalKrullDim (pullback p (Spec.algebraMap R K) : Scheme.{u}) ≤ 1) :
    ∃ s : Finset (AlgebraicClosure K),
      letI : Algebra R (FiniteField.stage K s) := (FiniteField.stage K s).algebra'
      Nonempty (GenericFiniteCoverData R K s p) := by
  classical
  let k := Spec.algebraMap R K
  let pK := pullback.snd p k
  obtain ⟨s, I, hI, C, ν₀, hfinite₀, _, hsurj₀, hshape₀⟩ :=
    FiniteField.exists_finite_field_component_cover K pK hd
  refine ⟨s, ?_⟩
  let L := FiniteField.stage K s
  let : Finite I := hI
  let : Algebra R L := (FiniteField.stage K s).algebra'
  let : IsScalarTower R K L := inferInstance
  let b := FiniteField.stageStructureMap K s
  have hb : b ≫ k = fieldMap R L := by
    rw [← Spec.map_comp]
    congr 1
  let E : pullback pK b ≅ pullback p (fieldMap R L) :=
    pullbackLeftPullbackSndIso p k b ≪≫ pullback.congrHom rfl hb
  have hE : E.hom ≫ pullback.snd p (fieldMap R L) = pullback.snd pK b := by
    simp [E, pK]
  let q (i : I) := ν₀ i ≫ pullback.snd pK b
  let ν (i : I) := ν₀ i ≫ E.hom
  have hν (i : I) : ν i ≫ pullback.snd p (fieldMap R L) = q i := by
    dsimp only [ν, q]
    rw [Category.assoc, hE]
  have hfinite (i : I) : IsFinite (ν i) := by
    let : IsFinite (ν₀ i) := hfinite₀ i
    exact inferInstanceAs (IsFinite (ν₀ i ≫ E.hom))
  let : ∀ i, IsFinite (ν i) := hfinite
  have htotal : Sigma.desc ν = Sigma.desc ν₀ ≫ E.hom := by
    apply Sigma.hom_ext
    intro i
    simp [ν]
  let : Surjective (Sigma.desc ν₀) := hsurj₀
  let : Surjective (Sigma.desc ν) := by
    rw [htotal]
    infer_instance
  choose σ hσ hshape using hshape₀
  have hproper (i : I) : IsProper (q i) := by
    rcases hshape i with hi | hi
    · let : IsIso (q i) := hi
      infer_instance
    · exact hi.1.proper
  let : ∀ i, IsProper (q i) := hproper
  let P : Set I := {i | IsIso (q i)}
  have hpoint (i : P) : IsIso (q i) := i.property
  let J := {i : I // i ∉ P}
  have hcurve (i : J) : Properties (Over.mk (q i)) ∧
      ∃ (N : ℕ) (j : C i ⟶ ProjectiveSpace L (ULift.{u} (Fin (N + 1)))),
        IsClosedImmersion j ∧
          j ≫ ProjectiveSpace.toSpec L (ULift.{u} (Fin (N + 1))) = q i :=
    (hshape i).resolve_left i.property
  choose n e hclosed he using fun i : J => (hcurve i).2
  let : ∀ i, IsClosedImmersion (e i) := hclosed
  let : ∀ i : J, SmoothOfRelativeDimension 1 (q i) := fun i => (hcurve i).1.smooth
  let : ∀ i : J, GeometricallyIntegral (q i) :=
    fun i => (hcurve i).1.isGeometricallyIntegral
  exact genericFiniteCoverData_of_original_field_cover R K s p
    C q ν hν σ hσ P hpoint n e he

end AlgebraicGeometry.Scheme.OverField.Curve.Normalization
