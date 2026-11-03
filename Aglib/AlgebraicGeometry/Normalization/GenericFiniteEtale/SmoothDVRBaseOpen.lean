/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Normalization.GenericFiniteEtale.SmoothDVRPurity
public import Aglib.AlgebraicGeometry.Normalization.GenericFiniteEtale.FullOpenRecovery
public import Aglib.AlgebraicGeometry.Normalization.GenericFiniteEtale.EtaleBaseChange
public import Aglib.AlgebraicGeometry.Morphisms.FiniteEtale.GaloisBaseChange

/-! # The original smooth DVR normalization over an arbitrary nonempty base open

The two native DVR points identify the original open with either the whole base
or its actual function-field image. One open isomorphism and one cover pullback
reduce to the accepted generic-fibre purity theorem. The original normalization
is retained through its native generic-source comparison.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Scheme.FiniteEtale.GenericNormalization.OpenRecovery

universe u

/-- Native normalization transport across one isomorphism of its original sources. -/
private theorem etale_normalization_of_sourceIso {Z Z' X : Scheme.{u}}
    (f : Z ⟶ X) (g : Z' ⟶ X)
    [QuasiCompact f] [QuasiSeparated f] [QuasiCompact g] [QuasiSeparated g]
    (e : Z ≅ Z') (h : e.hom ≫ g = f) [Etale f.fromNormalization] :
    Etale g.fromNormalization := by
  let E := Hom.normalizationSourceIso e f g h
  have he : E.inv ≫ f.fromNormalization = g.fromNormalization := by
    exact (congrArg (fun a => E.inv ≫ a)
      (Hom.normalizationSourceIso_hom_over e f g h)).symm.trans
        (Iso.inv_hom_id_assoc E _)
  rw [← he]
  infer_instance

/-- A section supplies nonemptiness of the original domain of a nonempty base open. -/
theorem section_baseOpen_nonempty {R : Type u} [CommRing R]
    {X U : Scheme.{u}} (p : X ⟶ Spec (.of R)) (s : Spec (.of R) ⟶ X)
    (hs : s ≫ p = 𝟙 _) (W : (Spec (.of R)).Opens) [Nonempty W]
    (j : U ⟶ X) (hj : Set.range j = p ⁻¹' (W : Set (Spec (.of R)))) : Nonempty U := by
  obtain ⟨w⟩ := ‹Nonempty W›
  have hw : s w.val ∈ Set.range j := by
    rw [hj]
    change p (s w.val) ∈ W
    have h := congrArg (fun f : Spec (.of R) ⟶ Spec (.of R) => f w.val) hs
    exact h.symm ▸ w.property
  obtain ⟨u, _⟩ := hw
  exact ⟨u⟩

/-- For a smooth geometrically connected DVR family, the original tame Galois
normalization with a global section is etale, for every nonempty original base open. -/
theorem etale_normalization_of_smoothDVR_baseOpen_section
    (R : Type u) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    {X U : Scheme.{u}} (p : X ⟶ Spec (.of R)) [Smooth p] [GeometricallyConnected p]
    (s : Spec (.of R) ⟶ X) (hs : s ≫ p = 𝟙 _)
    (W : (Spec (.of R)).Opens) [Nonempty W]
    (j : U ⟶ X) [IsOpenImmersion j]
    (hj : Set.range j = p ⁻¹' (W : Set (Spec (.of R))))
    (N : ℕ) (hN : 0 < N) (hunit : IsUnit (N : R)) :
    letI : IsRegularRing R := IsRegularLocalRing.isRegularRing_of_regularLocal R
    letI : GeometricallyIntegral p := geometricallyIntegral_of_smooth_of_geometricallyConnected p
    letI : IsIntegral X := GeometricallyIntegral.isIntegral_of_isLocallyNoetherian p
    letI : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian p
    letI : ∀ x : X, IsIntegrallyClosed (X.presheaf.stalk x) := fun x =>
      @IsRegularLocalRing.isIntegrallyClosed_of_regularLocal _ _
        (regularStalks_of_smooth p (regularStalks_spec R) x)
    letI : Nonempty U := section_baseOpen_nonempty p s hs W j hj
    letI : IsIntegral U := isIntegral_of_isOpenImmersion j
    ∀ (Y : FiniteEtale U) [IsIntegral Y.obj.left]
      [CategoryTheory.PreGaloisCategory.IsGalois Y], Nat.card (Aut Y) ∣ N →
      ∀ (a : Spec (.of R) ⟶ (genericMap j Y.obj.hom).normalization),
        a ≫ (genericMap j Y.obj.hom).fromNormalization = s →
        Etale (genericMap j Y.obj.hom).fromNormalization := by
  let : IsRegularRing R := IsRegularLocalRing.isRegularRing_of_regularLocal R
  let : GeometricallyIntegral p := geometricallyIntegral_of_smooth_of_geometricallyConnected p
  let : IsIntegral X := GeometricallyIntegral.isIntegral_of_isLocallyNoetherian p
  let : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian p
  let : ∀ x : X, IsIntegrallyClosed (X.presheaf.stalk x) := fun x =>
    @IsRegularLocalRing.isIntegrallyClosed_of_regularLocal _ _
      (regularStalks_of_smooth p (regularStalks_spec R) x)
  let : Nonempty U := section_baseOpen_nonempty p s hs W j hj
  let : IsIntegral U := isIntegral_of_isOpenImmersion j
  intro Y hY hG hcard a ha
  by_cases hc : IsLocalRing.closedPoint R ∈ W
  · have ht : W = ⊤ := by
      exact preimage_eq_top_of_closedPoint_mem (f := 𝟙 (Spec (.of R))) hc
    apply fromNormalization_etale_of_surjective_open j Y.obj.hom
    intro x
    have hx : x ∈ Set.range j := by
      rw [hj]
      change p x ∈ W
      rw [ht]
      trivial
    exact hx
  let K := (Spec (.of R)).functionField
  let : Algebra R K := instAlgebraCarrierFunctionFieldSpec (.of R)
  let : IsFractionRing R K := functionField_isFractionRing_of_affine (.of R)
  let gR := Spec.algebraMap R K
  let : IsOpenImmersion gR := LocalRing.GenericFiber.baseMap_openImmersion
  let UK := pullback p gR
  let jK : UK ⟶ X := pullback.fst p gR
  let : IsOpenImmersion jK := inferInstanceAs (IsOpenImmersion (pullback.fst p gR))
  let : IsIntegral UK := GeometricallyIntegral.geometrically_isIntegral gR jK
    (pullback.snd p gR) (.of_hasPullback _ _)
  have hgen : genericPoint (Spec (.of R)) ∈ W := by
    obtain ⟨w⟩ := ‹Nonempty W›
    exact (genericPoint_specializes w.val).mem_open W.isOpen w.property
  have hrange : Set.range gR = (W : Set (Spec (.of R))) := by
    ext z
    constructor
    · rintro ⟨t, rfl⟩
      have ht : t = IsLocalRing.closedPoint K := Subsingleton.elim _ _
      rw [ht]
      exact (LocalRing.GenericFiber.baseMap_closedPoint_eq_genericPoint R K).symm ▸ hgen
    · intro hz
      rcases Scheme.Spec.DiscreteValuationRing.eq_genericPoint_or_closedPoint R z with h | h
      · exact ⟨IsLocalRing.closedPoint K,
          (LocalRing.GenericFiber.baseMap_closedPoint_eq_genericPoint R K).trans h.symm⟩
      · exact (hc (h ▸ hz)).elim
  have hsame : Set.range jK = Set.range j := by
    rw [Scheme.Pullback.range_fst, hj]
    exact congrArg (fun T : Set (Spec (.of R)) => p ⁻¹' T) hrange
  let e : UK ≅ U := IsOpenImmersion.isoOfRangeEq jK j hsame
  have he : e.hom ≫ j = jK := IsOpenImmersion.isoOfRangeEq_hom_fac _ _ _
  let : IsIso e.hom := e.isIso_hom
  let : IsIso (pullback.fst Y.obj.hom e.hom) :=
    (IsPullback.of_hasPullback Y.obj.hom e.hom).isIso_fst_of_isIso
  let YK := (baseChange e.hom).obj Y
  let : IsFinite YK.obj.hom := inferInstanceAs (IsFinite (pullback.snd Y.obj.hom e.hom))
  let : Etale YK.obj.hom := inferInstanceAs (Etale (pullback.snd Y.obj.hom e.hom))
  let eY : pullback Y.obj.hom e.hom ≅ Y.obj.left :=
    asIso (pullback.fst Y.obj.hom e.hom)
  have hYK : IsIntegral (pullback Y.obj.hom e.hom) := IsIntegral.of_isIso eY.inv
  let : IsIntegral YK.obj.left := hYK
  let : CategoryTheory.PreGaloisCategory.IsGalois YK := baseChange_isGalois_of_connected e.hom Y
  have hcardK : Nat.card (Aut YK) ∣ N := by
    rw [baseChange_card_aut_of_connected e.hom Y]
    exact hcard
  let rK : Spec (.of K) ⟶ UK := GenericSection.genericSection R K p s hs
  let t := rK ≫ e.hom
  have ht : t ≫ j = gR ≫ s := by
    exact (Category.assoc rK e.hom j).trans
      ((congrArg (fun f => rK ≫ f) he).trans
        (GenericSection.genericSection_projection R K p s hs))
  have hsq : (gR ≫ a) ≫ (genericMap j Y.obj.hom).fromNormalization = t ≫ j := by
    rw [Category.assoc, ha, ht]
  let d := pullback.lift (gR ≫ a) t hsq
  let a₀ := d ≫ (iso j Y.obj.hom).inv
  have hi : (iso j Y.obj.hom).inv ≫ Y.obj.hom =
      pullback.snd (genericMap j Y.obj.hom).fromNormalization j := by
    exact (congrArg (fun f => (iso j Y.obj.hom).inv ≫ f)
      (iso_hom_snd j Y.obj.hom)).symm.trans
        (Iso.inv_hom_id_assoc (iso j Y.obj.hom) _)
  have ha₀ : a₀ ≫ Y.obj.hom = rK ≫ e.hom := by
    rw [Category.assoc, hi]
    exact pullback.lift_snd (gR ≫ a) t hsq
  let aK : Spec (.of K) ⟶ YK.obj.left := pullback.lift a₀ rK ha₀
  have haK : aK ≫ YK.obj.hom ≫ jK =
      (Spec (.of R)).fromSpecStalk (genericPoint (Spec (.of R))) ≫ s := by
    have hproj : aK ≫ YK.obj.hom = rK := pullback.lift_snd a₀ rK ha₀
    exact (Category.assoc aK YK.obj.hom jK).symm.trans
      ((congrArg (fun f => f ≫ jK) hproj).trans
        ((GenericSection.genericSection_projection R K p s hs).trans
          (congrArg (fun f => f ≫ s) (Spec.fromSpecStalk_eq' (.of R) _).symm)))
  have hpur := (etale_normalization_of_smoothDVR_genericSection R p s hs N hN hunit
    YK hcardK aK haK).1
  let : Etale (genericMap jK YK.obj.hom).fromNormalization := hpur
  have H : IsPullback e.hom jK j (𝟙 X) :=
    IsPullback.of_horiz_isIso ⟨by simpa only [Category.comp_id] using he⟩
  have HG := genericMap_baseChange_isPullback j jK (𝟙 X) e.hom H Y
  let m : (genericCover jK YK.obj.hom).obj.left ⟶
      (genericCover j Y.obj.hom).obj.left := genericPullbackMap e.hom Y.obj.hom
  let : IsIso m := HG.isIso_fst_of_isIso
  have hm : m ≫ genericMap j Y.obj.hom = genericMap jK YK.obj.hom := by
    exact HG.w.trans (Category.comp_id _)
  let : QuasiCompact (genericMap jK YK.obj.hom) := by
    unfold genericMap
    infer_instance
  let : QuasiSeparated (genericMap jK YK.obj.hom) := by
    unfold genericMap
    infer_instance
  exact etale_normalization_of_sourceIso (genericMap jK YK.obj.hom)
    (genericMap j Y.obj.hom) (asIso m) hm

end AlgebraicGeometry.Scheme.FiniteEtale.GenericNormalization.OpenRecovery
