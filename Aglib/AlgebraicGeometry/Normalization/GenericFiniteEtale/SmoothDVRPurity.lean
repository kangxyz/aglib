/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Normalization.GenericFiniteEtale.SmoothDVRTransverse
public import Aglib.AlgebraicGeometry.Normalization.GenericFiniteEtale.RegularBase
public import Aglib.AlgebraicGeometry.Normalization.GenericFiniteEtale.GaloisAffineChart
public import Aglib.AlgebraicGeometry.Normalization.GenericFiniteEtale.OpenEtaleLocus
public import Aglib.AlgebraicGeometry.Stalk.DVRVerticalCodimension
public import Aglib.AlgebraicGeometry.Stalk.GenericSection
public import Aglib.AlgebraicGeometry.Morphisms.Etale.PointwiseImage
public import Aglib.AlgebraicGeometry.Morphisms.Etale.PointwiseBaseChange

/-! # Purity for the original smooth DVR normalization

The transverse section supplies one original etale point. Its etale open
image contains the actual special-fibre generic point. Original Galois fibre
transitivity on one original affine chart propagates etaleness to every point
above it. The original generic-open locus handles horizontal points, and
native source-stalk purity applies to the unchanged normalization.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Scheme.FiniteEtale.GenericNormalization.OpenRecovery

universe u

/-- The original normalization of a tame Galois generic cover admitting a
point over a smooth DVR section is etale everywhere. Its original unique
section extension and both original triangles are retained. -/
theorem etale_normalization_of_smoothDVR_genericSection
    (R : Type u) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    {X : Scheme.{u}} (p : X ⟶ Spec (.of R)) [Smooth p] [GeometricallyConnected p]
    (s : Spec (.of R) ⟶ X) (hs : s ≫ p = 𝟙 (Spec (.of R)))
    (N : ℕ) (hN : 0 < N) (hunit : IsUnit (N : R)) :
    letI : IsRegularRing R := IsRegularLocalRing.isRegularRing_of_regularLocal R
    letI : GeometricallyIntegral p := geometricallyIntegral_of_smooth_of_geometricallyConnected p
    letI : IsIntegral X := GeometricallyIntegral.isIntegral_of_isLocallyNoetherian p
    letI : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian p
    letI : ∀ x : X, IsIntegrallyClosed (X.presheaf.stalk x) := fun x =>
      @IsRegularLocalRing.isIntegrallyClosed_of_regularLocal _ _
        (regularStalks_of_smooth p (regularStalks_spec R) x)
    let K := (Spec (.of R)).functionField
    letI : Algebra R K := instAlgebraCarrierFunctionFieldSpec (.of R)
    letI : IsFractionRing R K := functionField_isFractionRing_of_affine (.of R)
    letI : IsOpenImmersion (Spec.algebraMap R K) := LocalRing.GenericFiber.baseMap_openImmersion
    let U := pullback p (Spec.algebraMap R K)
    let j := pullback.fst p (Spec.algebraMap R K)
    letI : IsIntegral U := GeometricallyIntegral.geometrically_isIntegral
      (Spec.algebraMap R K) j (pullback.snd p (Spec.algebraMap R K)) (.of_hasPullback _ _)
    ∀ (Y : FiniteEtale U) [IsIntegral Y.obj.left] [CategoryTheory.PreGaloisCategory.IsGalois Y],
    Nat.card (Aut Y) ∣ N →
    ∀ (a : Spec K ⟶ Y.obj.left),
    a ≫ Y.obj.hom ≫ j = (Spec (.of R)).fromSpecStalk (genericPoint (Spec (.of R))) ≫ s →
    Etale (genericMap j Y.obj.hom).fromNormalization ∧
    ∃ l : Spec (.of R) ⟶ (genericMap j Y.obj.hom).normalization,
      l ≫ (genericMap j Y.obj.hom).fromNormalization = s ∧
      (Spec (.of R)).fromSpecStalk (genericPoint (Spec (.of R))) ≫ l =
        a ≫ inclusion j Y.obj.hom ∧
      (∀ l' : Spec (.of R) ⟶ (genericMap j Y.obj.hom).normalization,
        l' ≫ (genericMap j Y.obj.hom).fromNormalization = s →
        (Spec (.of R)).fromSpecStalk (genericPoint (Spec (.of R))) ≫ l' =
          a ≫ inclusion j Y.obj.hom → l' = l) ∧
      (genericMap j Y.obj.hom).fromNormalization.etaleAt (l (IsLocalRing.closedPoint R)) := by
  let : IsRegularRing R := IsRegularLocalRing.isRegularRing_of_regularLocal R
  let : GeometricallyIntegral p := geometricallyIntegral_of_smooth_of_geometricallyConnected p
  let : IsIntegral X := GeometricallyIntegral.isIntegral_of_isLocallyNoetherian p
  let : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian p
  let : ∀ x : X, IsIntegrallyClosed (X.presheaf.stalk x) := fun x =>
    @IsRegularLocalRing.isIntegrallyClosed_of_regularLocal _ _
      (regularStalks_of_smooth p (regularStalks_spec R) x)
  let K := (Spec (.of R)).functionField
  let : Algebra R K := instAlgebraCarrierFunctionFieldSpec (.of R)
  let : IsFractionRing R K := functionField_isFractionRing_of_affine (.of R)
  let : IsOpenImmersion (Spec.algebraMap R K) := LocalRing.GenericFiber.baseMap_openImmersion
  let U := pullback p (Spec.algebraMap R K)
  let j := pullback.fst p (Spec.algebraMap R K)
  let : IsIntegral U := GeometricallyIntegral.geometrically_isIntegral
    (Spec.algebraMap R K) j (pullback.snd p (Spec.algebraMap R K)) (.of_hasPullback _ _)
  dsimp only
  intro Y hY hG hcard a ha
  let q := genericMap j Y.obj.hom
  have hsection := exists_smoothDVR_transverseGenericLift R p s hs N hN hunit Y hcard a ha
  obtain ⟨l, hl, hgeneric, huniq, hletale⟩ := hsection
  let r := Spec.map (CommRingCat.ofHom (IsLocalRing.residue R))
  let C : Scheme.{u} := pullback p r
  let : IsIntegral C := GeometricallyIntegral.geometrically_isIntegral r
    (pullback.fst p r) (pullback.snd p r) (.of_hasPullback _ _)
  let ξ := (pullback.fst p r) (genericPoint C)
  have hsclosed : p (s (IsLocalRing.closedPoint R)) = IsLocalRing.closedPoint R :=
    congrArg (fun k : Spec (.of R) ⟶ Spec (.of R) => k (IsLocalRing.closedPoint R)) hs
  have hspecial : ξ ⤳ s (IsLocalRing.closedPoint R) :=
    p.specialFiber_generic_specializes R (s (IsLocalRing.closedPoint R)) hsclosed
  have hlclosed : q.fromNormalization (l (IsLocalRing.closedPoint R)) =
      s (IsLocalRing.closedPoint R) :=
    congrArg (fun k : Spec (.of R) ⟶ X => k (IsLocalRing.closedPoint R)) hl
  have hspecial' : ξ ⤳ q.fromNormalization (l (IsLocalRing.closedPoint R)) :=
    hlclosed.symm ▸ hspecial
  obtain ⟨z₀, hz₀, het₀⟩ := hletale.exists_preimage_of_specializes hspecial'
  obtain ⟨_, ⟨V, hV, rfl⟩, hsV, _⟩ := X.isBasis_affineOpens.exists_subset_of_mem_open
    (Set.mem_univ (s (IsLocalRing.closedPoint R))) isOpen_univ
  have hξV : ξ ∈ V := hspecial.mem_open V.isOpen hsV
  have hglobal : Etale q.fromNormalization := by
    let (x : X) : IsRegularLocalRing (X.presheaf.stalk x) :=
      regularStalks_of_smooth p (regularStalks_spec R) x
    apply GenericNormalization.etale_of_unramified_stalk_dimension_one X (genericCover j Y.obj.hom)
    intro z hz
    have hdim : ringKrullDim (X.presheaf.stalk (q.fromNormalization z)) = 1 :=
      (stalk_ringKrullDim X (genericCover j Y.obj.hom) z).symm.trans hz
    have hco : Order.coheight (q.fromNormalization z) = 1 := by
      rw [ringKrullDim_stalk_eq_coheight] at hdim
      exact WithBot.coe_injective hdim
    have het : q.fromNormalization.etaleAt z := by
      rcases Scheme.Spec.DiscreteValuationRing.eq_genericPoint_or_closedPoint R
        (p (q.fromNormalization z)) with hbase | hbase
      · apply fromNormalization_etaleAt_of_image_mem j Y.obj.hom z
        rw [Scheme.Pullback.range_fst]
        exact ⟨IsLocalRing.closedPoint K,
          (LocalRing.GenericFiber.baseMap_closedPoint_eq_genericPoint R K).trans hbase.symm⟩
      · have hzξ : q.fromNormalization z = ξ :=
          p.eq_specialFiber_genericPoint_of_coheight_one R (q.fromNormalization z) hco hbase
        exact genericNormalization_etaleAt_of_image_eq_in_affineOpen j Y V hV z₀ z
          (by rw [hz₀]; exact hξV) (hz₀.trans hzξ.symm) het₀
    exact (RingHom.FormallyEtale.iff_formallyUnramified_and_formallySmooth _).mp
      het.stalkMap_formallyEtale |>.1
  exact ⟨hglobal, l, hl, hgeneric, huniq, hletale⟩

end AlgebraicGeometry.Scheme.FiniteEtale.GenericNormalization.OpenRecovery
