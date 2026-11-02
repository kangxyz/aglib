/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.ProjectiveSpace.BaseChange.Model
public import Aglib.AlgebraicGeometry.Morphisms.Smooth.GenericFieldOpen
public import Aglib.AlgebraicGeometry.Limits.Monomorphisms
public import Aglib.AlgebraicGeometry.Limits.ImmersionBaseChange
public import Aglib.AlgebraicGeometry.Morphisms.Finite.Coproduct
public import Mathlib.AlgebraicGeometry.Geometrically.Integral
public import Mathlib.AlgebraicGeometry.PullbackCarrier

/-! # Actual generic-cover model base change

The original models, arrows, sections and embeddings are transported along one
specified factorization. Finiteness and joint coverage use the original open
restrictions and actual cartesian squares; no new cover model is chosen.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open AlgebraicGeometry.Scheme.FinitePresentationDescent

namespace AlgebraicGeometry.Scheme.OverField.Curve.Normalization

universe u

theorem factorBase_projective_embedding
    {A B L : Type u} [CommRing A] [CommRing B] [CommRing L]
    (φ : A →+* L) (ψ : A →+* B) (χ : B →+* L) (h : χ.comp ψ = φ)
    (ι : Type u) [Finite ι] [Nonempty ι]
    {Z : Scheme.{u}} {t : Z ⟶ Spec (.of L)}
    (M : Model (Spec.map (CommRingCat.ofHom φ)) t)
    (ea : M.X ⟶ ProjectiveSpace A ι) [IsClosedImmersion ea]
    (hea : ea ≫ ProjectiveSpace.toSpec A ι = M.f)
    (e : Z ⟶ ProjectiveSpace L ι)
    (he : e ≫ ProjectiveSpace.toSpec L ι = t)
    (hcomm : M.p ≫ ea = e ≫ ProjectiveSpace.map φ ι) :
    ∃ eb : (M.factorBase (Spec.map (CommRingCat.ofHom χ))
        (Spec.map (CommRingCat.ofHom ψ))
        (ProjectiveSpace.spec_factor φ ψ χ h)).X ⟶ ProjectiveSpace B ι,
      IsClosedImmersion eb ∧
      eb ≫ ProjectiveSpace.toSpec B ι =
        (M.factorBase (Spec.map (CommRingCat.ofHom χ))
          (Spec.map (CommRingCat.ofHom ψ))
          (ProjectiveSpace.spec_factor φ ψ χ h)).f ∧
      (M.factorBase (Spec.map (CommRingCat.ofHom χ))
        (Spec.map (CommRingCat.ofHom ψ))
        (ProjectiveSpace.spec_factor φ ψ χ h)).p ≫ eb =
          e ≫ ProjectiveSpace.map χ ι := by
  let b := Spec.map (CommRingCat.ofHom χ)
  let c := Spec.map (CommRingCat.ofHom ψ)
  let hf := ProjectiveSpace.spec_factor φ ψ χ h
  let P := ProjectiveSpace.model φ ι
  let m : Over.mk t ⟶ Over.mk (ProjectiveSpace.toSpec L ι) := Over.homMk e he
  let a : Model.Map M P m := { hom := Over.homMk ea hea, comm := hcomm }
  let aB := a.factorBase b c hf
  let E := ProjectiveSpace.factorBaseModelIso φ ψ χ h ι
  let eb := aB.hom.left ≫ E.hom
  have haB : IsClosedImmersion aB.hom.left :=
    MorphismProperty.overPullbackMap (P := @IsClosedImmersion) c a.hom
      (show IsClosedImmersion a.hom.left from inferInstanceAs (IsClosedImmersion ea))
  have hclosed : IsClosedImmersion eb :=
    MorphismProperty.comp_mem (@IsClosedImmersion) _ _ haB inferInstance
  have hP : (P.factorBase b c hf).p =
      ProjectiveSpace.map χ ι ≫ (ProjectiveSpace.baseChangeIso ψ ι).hom := by
    have hfst : (P.factorBase b c hf).p ≫
        pullback.fst (ProjectiveSpace.toSpec A ι) c = ProjectiveSpace.map φ ι :=
      (IsPullback.of_hasPullback P.f c).lift_fst _ _ _
    have hsnd : (P.factorBase b c hf).p ≫
        pullback.snd (ProjectiveSpace.toSpec A ι) c =
        ProjectiveSpace.toSpec L ι ≫ b :=
      (IsPullback.of_hasPullback P.f c).lift_snd _ _ _
    have hQfst : (ProjectiveSpace.baseChangeIso ψ ι).hom ≫
        pullback.fst (ProjectiveSpace.toSpec A ι) c = ProjectiveSpace.map ψ ι :=
      ProjectiveSpace.baseChangeIso_hom_fst ψ ι
    have hQsnd : (ProjectiveSpace.baseChangeIso ψ ι).hom ≫
        pullback.snd (ProjectiveSpace.toSpec A ι) c = ProjectiveSpace.toSpec B ι :=
      ProjectiveSpace.baseChangeIso_hom_snd ψ ι
    apply pullback.hom_ext (f := ProjectiveSpace.toSpec A ι) (g := c)
    · rw [hfst, Category.assoc, hQfst, ← ProjectiveSpace.map_comp, h]
    · rw [hsnd, Category.assoc, hQsnd]
      exact (ProjectiveSpace.map_toSpec χ ι).symm
  have hPE : (P.factorBase b c hf).p ≫ E.hom = ProjectiveSpace.map χ ι := by
    rw [hP]
    change (ProjectiveSpace.map χ ι ≫ (ProjectiveSpace.baseChangeIso ψ ι).hom) ≫
      (ProjectiveSpace.baseChangeIso ψ ι).inv = _
    simp only [Category.assoc, Iso.hom_inv_id, Category.comp_id]
  refine ⟨eb, hclosed, ?_, ?_⟩
  · change (aB.hom.left ≫ E.hom) ≫ ProjectiveSpace.toSpec B ι = _
    rw [Category.assoc, ProjectiveSpace.factorBaseModelIso_hom_toSpec]
    exact Over.w aB.hom
  · change (M.factorBase b c hf).p ≫ (aB.hom.left ≫ E.hom) = _
    rw [← Category.assoc, aB.comm, Category.assoc, hPE]
    rfl

/-- Finiteness over an actual base open transports to the same original
pulled-back arrow when the actual new base lands in that open. -/
theorem finite_overPullbackMap_of_range_subset
    {S T : Scheme.{u}} (δ : T ⟶ S) {M N : Over S} (a : M ⟶ N)
    (U : S.Opens) (hδ : Set.range δ ⊆ U)
    [IsFinite (a.left ∣_ (N.hom ⁻¹ᵁ U))] :
    IsFinite ((Over.pullback δ).map a).left := by
  let W := N.hom ⁻¹ᵁ U
  let g := pullback.fst N.hom δ
  have hgrange : Set.range g ⊆ W := by
    rintro _ ⟨y, rfl⟩
    change N.hom (g y) ∈ U
    have hy : N.hom (g y) = δ (pullback.snd N.hom δ y) :=
      congrArg (fun f => f y) (pullback.condition (f := N.hom) (g := δ))
    rw [hy]
    exact hδ ⟨_, rfl⟩
  let gW : pullback N.hom δ ⟶ W := IsOpenImmersion.lift W.ι g (by
    simpa only [Scheme.Opens.range_ι] using hgrange)
  have hgW : gW ≫ W.ι = g := IsOpenImmersion.lift_fac _ _ _
  let E := Scheme.morphismRestrictBaseChangeIso a.left W g gW hgW
  let : IsIso E.hom.left :=
    inferInstanceAs (IsIso ((Over.forget (pullback N.hom δ)).map E.hom))
  have hrestricted : IsFinite (pullback.snd (a.left ∣_ W) gW) := inferInstance
  have hstandard : IsFinite (pullback.snd a.left g) := by
    have hw : E.hom.left ≫ pullback.snd a.left g =
        pullback.snd (a.left ∣_ W) gW := Over.w E.hom
    rw [← hw] at hrestricted
    exact (MorphismProperty.cancel_left_of_respectsIso
      (P := @IsFinite) E.hom.left (pullback.snd a.left g)).mp hrestricted
  let H := isPullback_overPullbackMap δ a
  have hw : H.isoPullback.hom ≫ pullback.snd a.left g =
      ((Over.pullback δ).map a).left := H.isoPullback_hom_snd
  rw [← hw]
  exact MorphismProperty.comp_mem (@IsFinite) _ _ inferInstance hstandard

/-- Joint surjectivity after the same base change uses the actual cartesian
square of each arrow. It does not identify points from two equal projections. -/
theorem jointly_surjective_overPullbackMap_of_range_subset
    {S T : Scheme.{u}} (δ : T ⟶ S) {I : Type u}
    (M : I → Over S) (N : Over S) (a : ∀ i, M i ⟶ N)
    (V : S.Opens) (hδ : Set.range δ ⊆ V)
    (hjoint : ∀ x : N.left, N.hom x ∈ V → ∃ i, ∃ c : (M i).left, (a i).left c = x) :
    ∀ y : ((Over.pullback δ).obj N).left,
      ∃ i, ∃ z : ((Over.pullback δ).obj (M i)).left,
        ((Over.pullback δ).map (a i)).left z = y := by
  intro y
  have hy : N.hom (pullback.fst N.hom δ y) ∈ V := by
    have h := congrArg (fun f => f y) (pullback.condition (f := N.hom) (g := δ))
    change N.hom (pullback.fst N.hom δ y) = δ (pullback.snd N.hom δ y) at h
    rw [h]
    exact hδ ⟨_, rfl⟩
  obtain ⟨i, c, hc⟩ := hjoint (pullback.fst N.hom δ y) hy
  obtain ⟨z, _, hz⟩ := Scheme.exists_preimage_of_isPullback
    (isPullback_overPullbackMap δ (a i)) c y hc
  exact ⟨i, z, hz⟩

/-- Complete transport of the original finite family along the same ring factorization. -/
theorem exists_factorBase_cover_properties
    {A D L : Type u} [CommRing A] [CommRing D] [Field L]
    (χ : A →+* L) (ψ : A →+* D) (χD : D →+* L) (hring : χD.comp ψ = χ)
    {W : Scheme.{u}} {s : W ⟶ Spec (.of L)}
    (N : Model (Spec.map (CommRingCat.ofHom χ)) s) [IsProper N.f]
    {I : Type u} [Finite I] {C : I → Scheme.{u}}
    {q : ∀ i, C i ⟶ Spec (.of L)}
    (M : ∀ i, Model (Spec.map (CommRingCat.ofHom χ)) (q i)) [∀ i, IsProper (M i).f]
    {m : ∀ i, Over.mk (q i) ⟶ Over.mk s} (a : ∀ i, Model.Map (M i) N (m i))
    (V : (Spec (.of A)).Opens)
    (hδrange : Set.range (Spec.map (CommRingCat.ofHom ψ)) ⊆ V)
    (hfin : ∀ i, ∃ U : (Spec (.of A)).Opens, V ≤ U ∧
      IsFinite ((a i).hom.left ∣_ (N.f ⁻¹ᵁ U)))
    (hjoint : ∀ x : N.X, N.f x ∈ V → ∃ i, ∃ c : (M i).X, (a i).hom.left c = x)
    (σ : ∀ i, Spec (.of L) ⟶ C i) (hσ : ∀ i, σ i ≫ q i = 𝟙 _)
    (σA : ∀ i, Spec (.of A) ⟶ (M i).X)
    (hσA : ∀ i, σA i ≫ (M i).f = 𝟙 _)
    (hσcomp : ∀ i, Spec.map (CommRingCat.ofHom χ) ≫ σA i = σ i ≫ (M i).p)
    (P : Set I) (hpoint : ∀ i : P, IsIso (M i).f)
    (hsm : ∀ i : {i : I // i ∉ P}, ∃ U : (Spec (.of A)).Opens, V ≤ U ∧
      SmoothOfRelativeDimension 1 ((M i).f ∣_ U) ∧ GeometricallyIntegral ((M i).f ∣_ U))
    (n : {i : I // i ∉ P} → ℕ)
    (e : ∀ i : {i : I // i ∉ P}, C i ⟶ ProjectiveSpace L (ULift.{u} (Fin (n i + 1))))
    (he : ∀ i, e i ≫ ProjectiveSpace.toSpec L (ULift.{u} (Fin (n i + 1))) = q i)
    (embeddings : ∀ i : {i : I // i ∉ P},
      ∃ ea : (M i).X ⟶ ProjectiveSpace A (ULift.{u} (Fin (n i + 1))),
        IsClosedImmersion ea ∧
        ea ≫ ProjectiveSpace.toSpec A (ULift.{u} (Fin (n i + 1))) = (M i).f ∧
        (M i).p ≫ ea = e i ≫ ProjectiveSpace.map χ (ULift.{u} (Fin (n i + 1)))) :
    let κS := Spec.map (CommRingCat.ofHom χD)
    let δS := Spec.map (CommRingCat.ofHom ψ)
    let hfactor := ProjectiveSpace.spec_factor χ ψ χD hring
    let NS := N.factorBase κS δS hfactor
    let MS := fun i => (M i).factorBase κS δS hfactor
    let aS := fun i => (a i).factorBase κS δS hfactor
    IsProper NS.f ∧ (∀ i, IsProper (MS i).f) ∧
      (∀ i, IsFinite (aS i).hom.left) ∧
      IsFinite (Sigma.desc fun i => (aS i).hom.left) ∧
      Surjective (Sigma.desc fun i => (aS i).hom.left) ∧
      (∃ σS : ∀ i, Spec (.of D) ⟶ (MS i).X,
        (∀ i, σS i ≫ (MS i).f = 𝟙 _) ∧
        ∀ i, κS ≫ σS i = σ i ≫ (MS i).p) ∧
      (∀ i : P, IsIso (MS i).f) ∧
      (∀ i : {i : I // i ∉ P}, SmoothOfRelativeDimension 1 (MS i).f ∧
        GeometricallyIntegral (MS i).f) ∧
      (∀ i : {i : I // i ∉ P},
        ∃ eS : (MS i).X ⟶ ProjectiveSpace D (ULift.{u} (Fin (n i + 1))),
          IsClosedImmersion eS ∧
          eS ≫ ProjectiveSpace.toSpec D (ULift.{u} (Fin (n i + 1))) = (MS i).f ∧
          (MS i).p ≫ eS = e i ≫ ProjectiveSpace.map χD (ULift.{u} (Fin (n i + 1)))) := by
  classical
  let κS := Spec.map (CommRingCat.ofHom χD)
  let δS := Spec.map (CommRingCat.ofHom ψ)
  let hfactor := ProjectiveSpace.spec_factor χ ψ χD hring
  let NS := N.factorBase κS δS hfactor
  let MS (i : I) := (M i).factorBase κS δS hfactor
  let aS (i : I) := (a i).factorBase κS δS hfactor
  have hNS : IsProper NS.f := inferInstanceAs (IsProper (pullback.snd N.f δS))
  have hMS (i : I) : IsProper (MS i).f :=
    inferInstanceAs (IsProper (pullback.snd (M i).f δS))
  have hfinS (i : I) : IsFinite (aS i).hom.left := by
    obtain ⟨W, hVW, hW⟩ := hfin i
    let : IsFinite ((a i).hom.left ∣_ ((Over.mk N.f).hom ⁻¹ᵁ W)) := hW
    exact finite_overPullbackMap_of_range_subset δS (a i).hom W
      (Set.Subset.trans hδrange hVW)
  let : ∀ i, IsFinite (aS i).hom.left := hfinS
  have hjointS : ∀ y : NS.X, ∃ i, ∃ z : (MS i).X, (aS i).hom.left z = y :=
    jointly_surjective_overPullbackMap_of_range_subset δS
      (fun i => Over.mk (M i).f) (Over.mk N.f) (fun i => (a i).hom) V hδrange hjoint
  have htotal : IsFinite (Sigma.desc fun i => (aS i).hom.left) :=
    Scheme.Hom.isFinite_sigmaDesc (fun i => (MS i).X) NS.X (fun i => (aS i).hom.left)
  have htotalSurj : Surjective (Sigma.desc fun i => (aS i).hom.left) := by
    constructor
    intro y
    obtain ⟨i, z, hz⟩ := hjointS y
    refine ⟨Sigma.ι (fun i => (MS i).X) i z, ?_⟩
    exact (congrArg (fun f => f z)
      (Sigma.ι_comp_desc (fun i => (aS i).hom.left) i)).trans hz
  let σS (i : I) : Spec (.of D) ⟶ (MS i).X :=
    pullback.lift (δS ≫ σA i) (𝟙 _) (by
      simp only [Category.assoc, hσA, Category.comp_id, Category.id_comp])
  have hσS (i : I) : σS i ≫ (MS i).f = 𝟙 _ := pullback.lift_snd _ _ _
  have hσScomp (i : I) : κS ≫ σS i = σ i ≫ (MS i).p := by
    have hfst : (MS i).p ≫ pullback.fst (M i).f δS = (M i).p :=
      (IsPullback.of_hasPullback (M i).f δS).lift_fst _ _ _
    have hsnd : (MS i).p ≫ pullback.snd (M i).f δS = q i ≫ κS :=
      (IsPullback.of_hasPullback (M i).f δS).lift_snd _ _ _
    have hσfst : σS i ≫ pullback.fst (M i).f δS = δS ≫ σA i := pullback.lift_fst _ _ _
    have hσsnd : σS i ≫ pullback.snd (M i).f δS = 𝟙 _ := pullback.lift_snd _ _ _
    apply pullback.hom_ext (f := (M i).f) (g := δS)
    · rw [Category.assoc, hσfst, Category.assoc, hfst,
        ← Category.assoc, hfactor, hσcomp]
    · rw [Category.assoc, hσsnd, Category.assoc, hsnd,
        ← Category.assoc, hσ, Category.id_comp, Category.comp_id]
  have hpointS (i : P) : IsIso (MS i).f := by
    let : IsIso (M i).f := hpoint i
    exact inferInstanceAs (IsIso (pullback.snd (M i).f δS))
  have hcurveS (i : {i : I // i ∉ P}) : SmoothOfRelativeDimension 1 (MS i).f ∧
      GeometricallyIntegral (MS i).f := by
    obtain ⟨W, hVW, hsmW, hgiW⟩ := hsm i
    let δW : Spec (.of D) ⟶ W := IsOpenImmersion.lift W.ι δS (by
      simpa only [Scheme.Opens.range_ι] using Set.Subset.trans hδrange hVW)
    let E := Scheme.morphismRestrictBaseChangeIso (M i).f W δS δW
      (IsOpenImmersion.lift_fac _ _ _)
    let : IsIso E.hom.left :=
      inferInstanceAs (IsIso ((Over.forget (Spec (.of D))).map E.hom))
    have hw : E.hom.left ≫ (MS i).f = pullback.snd ((M i).f ∣_ W) δW := Over.w E.hom
    constructor
    · have hh := MorphismProperty.pullback_snd
        (P := @SmoothOfRelativeDimension 1) ((M i).f ∣_ W) δW hsmW
      rw [← hw] at hh
      exact (MorphismProperty.cancel_left_of_respectsIso
        (P := @SmoothOfRelativeDimension 1) E.hom.left (MS i).f).mp hh
    · have hh := MorphismProperty.pullback_snd
        (P := @GeometricallyIntegral) ((M i).f ∣_ W) δW hgiW
      rw [← hw] at hh
      exact (MorphismProperty.cancel_left_of_respectsIso
        (P := @GeometricallyIntegral) E.hom.left (MS i).f).mp hh
  refine ⟨hNS, hMS, hfinS, htotal, htotalSurj, ⟨σS, hσS, hσScomp⟩,
    hpointS, hcurveS, ?_⟩
  intro i
  obtain ⟨ea, hea, hestruct, hegeneric⟩ := embeddings i
  let : IsClosedImmersion ea := hea
  exact factorBase_projective_embedding χ ψ χD hring
    (ULift.{u} (Fin (n i + 1))) (M i) ea hestruct (e i) (he i) hegeneric

/-- The same complete producer with the actual already-constructed base arrows. -/
theorem exists_factorBase_cover_properties_of_maps
    {A D L : Type u} [CommRing A] [CommRing D] [Field L]
    (χ : A →+* L) (ψ : A →+* D) (χD : D →+* L) (hring : χD.comp ψ = χ)
    (κS : Spec (.of L) ⟶ Spec (.of D)) (δS : Spec (.of D) ⟶ Spec (.of A))
    (hκS : Spec.map (CommRingCat.ofHom χD) = κS)
    (hδS : Spec.map (CommRingCat.ofHom ψ) = δS)
    (hfactor : κS ≫ δS = Spec.map (CommRingCat.ofHom χ))
    {W : Scheme.{u}} {s : W ⟶ Spec (.of L)}
    (N : Model (Spec.map (CommRingCat.ofHom χ)) s) [IsProper N.f]
    {I : Type u} [Finite I] {C : I → Scheme.{u}}
    {q : ∀ i, C i ⟶ Spec (.of L)}
    (M : ∀ i, Model (Spec.map (CommRingCat.ofHom χ)) (q i)) [∀ i, IsProper (M i).f]
    {m : ∀ i, Over.mk (q i) ⟶ Over.mk s} (a : ∀ i, Model.Map (M i) N (m i))
    (V : (Spec (.of A)).Opens)
    (hδrange : Set.range δS ⊆ V)
    (hfin : ∀ i, ∃ U : (Spec (.of A)).Opens, V ≤ U ∧
      IsFinite ((a i).hom.left ∣_ (N.f ⁻¹ᵁ U)))
    (hjoint : ∀ x : N.X, N.f x ∈ V → ∃ i, ∃ c : (M i).X, (a i).hom.left c = x)
    (σ : ∀ i, Spec (.of L) ⟶ C i) (hσ : ∀ i, σ i ≫ q i = 𝟙 _)
    (σA : ∀ i, Spec (.of A) ⟶ (M i).X)
    (hσA : ∀ i, σA i ≫ (M i).f = 𝟙 _)
    (hσcomp : ∀ i, Spec.map (CommRingCat.ofHom χ) ≫ σA i = σ i ≫ (M i).p)
    (P : Set I) (hpoint : ∀ i : P, IsIso (M i).f)
    (hsm : ∀ i : {i : I // i ∉ P}, ∃ U : (Spec (.of A)).Opens, V ≤ U ∧
      SmoothOfRelativeDimension 1 ((M i).f ∣_ U) ∧ GeometricallyIntegral ((M i).f ∣_ U))
    (n : {i : I // i ∉ P} → ℕ)
    (e : ∀ i : {i : I // i ∉ P}, C i ⟶ ProjectiveSpace L (ULift.{u} (Fin (n i + 1))))
    (he : ∀ i, e i ≫ ProjectiveSpace.toSpec L (ULift.{u} (Fin (n i + 1))) = q i)
    (embeddings : ∀ i : {i : I // i ∉ P},
      ∃ ea : (M i).X ⟶ ProjectiveSpace A (ULift.{u} (Fin (n i + 1))),
        IsClosedImmersion ea ∧
        ea ≫ ProjectiveSpace.toSpec A (ULift.{u} (Fin (n i + 1))) = (M i).f ∧
        (M i).p ≫ ea = e i ≫ ProjectiveSpace.map χ (ULift.{u} (Fin (n i + 1)))) :
    let NS := N.factorBase κS δS hfactor
    let MS := fun i => (M i).factorBase κS δS hfactor
    let aS := fun i => (a i).factorBase κS δS hfactor
    IsProper NS.f ∧ (∀ i, IsProper (MS i).f) ∧
      (∀ i, IsFinite (aS i).hom.left) ∧
      IsFinite (Sigma.desc fun i => (aS i).hom.left) ∧
      Surjective (Sigma.desc fun i => (aS i).hom.left) ∧
      (∃ σS : ∀ i, Spec (.of D) ⟶ (MS i).X,
        (∀ i, σS i ≫ (MS i).f = 𝟙 _) ∧
        ∀ i, κS ≫ σS i = σ i ≫ (MS i).p) ∧
      (∀ i : P, IsIso (MS i).f) ∧
      (∀ i : {i : I // i ∉ P}, SmoothOfRelativeDimension 1 (MS i).f ∧
        GeometricallyIntegral (MS i).f) ∧
      (∀ i : {i : I // i ∉ P},
        ∃ eS : (MS i).X ⟶ ProjectiveSpace D (ULift.{u} (Fin (n i + 1))),
          IsClosedImmersion eS ∧
          eS ≫ ProjectiveSpace.toSpec D (ULift.{u} (Fin (n i + 1))) = (MS i).f ∧
          (MS i).p ≫ eS = e i ≫ ProjectiveSpace.map χD (ULift.{u} (Fin (n i + 1)))) := by
  subst κS
  subst δS
  exact exists_factorBase_cover_properties χ ψ χD hring N M a V hδrange hfin hjoint
    σ hσ σA hσA hσcomp P hpoint hsm n e he embeddings

end AlgebraicGeometry.Scheme.OverField.Curve.Normalization
