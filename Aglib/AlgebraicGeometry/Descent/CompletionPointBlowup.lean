/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Descent.CompletionNormalization
public import Aglib.AlgebraicGeometry.Blowup.FlatBaseChange
public import Aglib.AlgebraicGeometry.Blowup.Integral
public import Aglib.AlgebraicGeometry.Blowup.Properness
public import Aglib.RingTheory.AdicCompletion.FiniteTypeLocalComparison
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import Mathlib.AlgebraicGeometry.Morphisms.Preimmersion

/-!
# Normalized point blowups under local completion

On the original closed fibre, the residue-field coefficient algebra is
annihilated by the original maximal ideal. The actual nilpotent tensor
comparison therefore makes its completion fibre unchanged. The resulting
point square uses the original residue-field map and gives equality of
the full point ideals. The ordinary blowup comparison is the existing
canonical flat-base-change map, with both original projections retained.

Transport of the original generic normalization along that ordinary
comparison and the finite normalization/completion theorem give one
complete normalized point step on a proper birational surface model.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits TopologicalSpace AlgebraicGeometry
open scoped TensorProduct

universe u

namespace AlgebraicGeometry.Scheme.Blowup

private theorem point_isPullback_of_isIso_fibre
    {X Y : Scheme.{u}} (β : Y ⟶ X) (y : Y)
    [IsIso (pullback.snd β (X.fromSpecResidueField (β y)))] :
    IsPullback (Y.fromSpecResidueField y)
      (Spec.map (β.residueFieldMap y)) β (X.fromSpecResidueField (β y)) := by
  let iX := X.fromSpecResidueField (β y)
  let iY := Y.fromSpecResidueField y
  let P : Scheme.{u} := pullback β iX
  let π₁ : P ⟶ Y := pullback.fst β iX
  let π₂ : P ⟶ Spec (X.residueField (β y)) := pullback.snd β iX
  have hw : iY ≫ β = Spec.map (β.residueFieldMap y) ≫ iX :=
    (β.SpecMap_residueFieldMap_fromSpecResidueField y).symm
  let l : Spec (Y.residueField y) ⟶ P :=
    pullback.lift iY (Spec.map (β.residueFieldMap y)) hw
  have hl : l ≫ π₁ = iY := pullback.lift_fst _ _ _
  let : IsPreimmersion π₁ := by
    change IsPreimmersion (pullback.fst β iX)
    infer_instance
  let : IsPreimmersion (l ≫ π₁) := by
    rw [hl]
    infer_instance
  let : IsPreimmersion l := IsPreimmersion.of_comp l π₁
  let : IsIso π₂ := inferInstance
  let : Subsingleton P := ⟨fun p q =>
    π₂.isOpenEmbedding.injective (Subsingleton.elim (π₂ p) (π₂ q))⟩
  let : Surjective l := ⟨fun p =>
    ⟨genericPoint (Spec (Y.residueField y)), Subsingleton.elim _ _⟩⟩
  let : IsClosedImmersion l := IsClosedImmersion.of_isPreimmersion l (by
    rw [Set.range_eq_univ.mpr l.surjective]
    exact isClosed_univ)
  let : IsReduced P := isReduced_of_isOpenImmersion π₂
  let : IsIso l := isIso_of_isClosedImmersion_of_surjective l
  exact IsPullback.of_iso_pullback ⟨hw⟩ (asIso l)
    (pullback.lift_fst _ _ _) (pullback.lift_snd _ _ _)

section CompletionPoint

variable {A : Type u} [CommRing A] [IsNoetherianRing A] [IsLocalRing A]
  {X : Scheme.{u}} (f : X ⟶ Spec (.of A))

private theorem completion_residuePullback_fst_isIso (x : X)
    (hx : IsLocalRing.maximalIdeal A ≤ (f x).asIdeal) :
    IsIso (pullback.fst (X.fromSpecResidueField x ≫ f)
      (Scheme.LocalRing.completionSpecMap A)) := by
  let K := X.residueField x
  let H := AdicCompletion (IsLocalRing.maximalIdeal A) A
  let scalar : A →+* K := (Spec.preimage (X.fromSpecResidueField x ≫ f)).hom
  let := scalar.toAlgebra
  have hscalar : Spec.algebraMap A K = X.fromSpecResidueField x ≫ f :=
    Spec.map_preimage _
  let z : Spec K := ⟨⊥, inferInstance⟩
  have hpoint : Spec.algebraMap A K z = f x := by
    rw [hscalar]
    change f ((X.fromSpecResidueField x) z) = f x
    exact congrArg f (Scheme.fromSpecResidueField_apply (X := X) x z)
  have hker : IsLocalRing.maximalIdeal A ≤ RingHom.ker (algebraMap A K) := by
    intro a ha
    have hmem := hx ha
    rw [← hpoint] at hmem
    change algebraMap A K a = 0 at hmem
    exact hmem
  have hpow : IsLocalRing.maximalIdeal A ^ 1 ≤ RingHom.ker (algebraMap A K) := by
    simpa only [pow_one] using hker
  let e : K ⊗[A] H ≃ₐ[K] K :=
    AdicCompletion.nilpotentTensorEquiv (IsLocalRing.maximalIdeal A) K
      (IsLocalRing.maximalIdeal A).fg_of_isNoetherianRing 1 hpow
  have hbij : Function.Bijective (algebraMap K (K ⊗[A] H)) := by
    change Function.Bijective e.symm
    exact e.symm.bijective
  let : IsIso (CommRingCat.ofHom (algebraMap K (K ⊗[A] H))) :=
    (ConcreteCategory.isIso_iff_bijective _).mpr hbij
  have Hsq : IsPullback (Spec.algebraMap K (K ⊗[A] H))
      (Spec.map (CommRingCat.ofHom
        (Algebra.TensorProduct.includeRight (R := A) (A := K) (B := H)).toRingHom))
      (Spec.algebraMap A K) (Scheme.LocalRing.completionSpecMap A) :=
    isPullback_SpecMap_of_isPushout _ _ _ _ (CommRingCat.isPushout_tensorProduct A K H)
  have hfst : IsIso (pullback.fst (Spec.algebraMap A K)
      (Scheme.LocalRing.completionSpecMap A)) := by
    let : IsIso (Hsq.isoPullback.hom ≫ pullback.fst (Spec.algebraMap A K)
        (Scheme.LocalRing.completionSpecMap A)) := by
      rw [Hsq.isoPullback_hom_fst]
      infer_instance
    exact IsIso.of_isIso_comp_left Hsq.isoPullback.hom _
  let eP : pullback (Spec.algebraMap A K) (Scheme.LocalRing.completionSpecMap A) ≅
      pullback (X.fromSpecResidueField x ≫ f) (Scheme.LocalRing.completionSpecMap A) :=
    pullback.congrHom hscalar rfl
  have heP : eP.hom ≫ pullback.fst (X.fromSpecResidueField x ≫ f)
      (Scheme.LocalRing.completionSpecMap A) =
      pullback.fst (Spec.algebraMap A K) (Scheme.LocalRing.completionSpecMap A) := by
    simp only [eP, pullback.congrHom_hom, pullback.map,
      pullback.lift_fst, Category.comp_id]
  let : IsIso (eP.hom ≫ pullback.fst (X.fromSpecResidueField x ≫ f)
      (Scheme.LocalRing.completionSpecMap A)) := by
    rw [heP]
    exact hfst
  exact IsIso.of_isIso_comp_left eP.hom _

private theorem completion_pointFibreProjection_isIso (x : X)
    (hx : IsLocalRing.maximalIdeal A ≤ (f x).asIdeal) :
    IsIso (pullback.snd (pullback.fst f (Scheme.LocalRing.completionSpecMap A))
      (X.fromSpecResidueField x)) := by
  let β := pullback.fst f (Scheme.LocalRing.completionSpecMap A)
  let i := X.fromSpecResidueField x
  let e := pullbackSymmetry β i ≪≫
    pullbackRightPullbackFstIso f (Scheme.LocalRing.completionSpecMap A) i
  let : IsIso (pullback.fst (i ≫ f) (Scheme.LocalRing.completionSpecMap A)) :=
    completion_residuePullback_fst_isIso f x hx
  have he : e.hom ≫ pullback.fst (i ≫ f) (Scheme.LocalRing.completionSpecMap A) =
      pullback.snd β i := by
    dsimp only [e, Iso.trans_hom]
    rw [Category.assoc, pullbackRightPullbackFstIso_hom_fst]
    change (pullbackSymmetry β i).hom ≫ pullback.fst i β = pullback.snd β i
    exact pullbackSymmetry_hom_comp_fst β i
  rw [← he]
  infer_instance

/-- The reduced point square on the original closed fibre is cartesian.
Its second arrow is the original residue-field map of the completion projection. -/
theorem completionPoint_isPullback
    (y : (pullback f (Scheme.LocalRing.completionSpecMap A) : Scheme.{u}))
    (hy : IsLocalRing.maximalIdeal A ≤
      (f (pullback.fst f (Scheme.LocalRing.completionSpecMap A) y)).asIdeal) :
    let β := pullback.fst f (Scheme.LocalRing.completionSpecMap A)
    IsPullback
      ((pullback f (Scheme.LocalRing.completionSpecMap A)).fromSpecResidueField y)
      (Spec.map (β.residueFieldMap y)) β (X.fromSpecResidueField (β y)) := by
  let β := pullback.fst f (Scheme.LocalRing.completionSpecMap A)
  let : IsIso (pullback.snd β (X.fromSpecResidueField (β y))) :=
    completion_pointFibreProjection_isIso f (β y) hy
  exact point_isPullback_of_isIso_fibre β y

end CompletionPoint

/-- A proved original point square gives equality of the full point ideals. -/
theorem pointCentre_comap_of_isPullback
    {X Y : Scheme.{u}} (β : Y ⟶ X) (y : Y)
    (hx : IsClosed ({β y} : Set X))
    (H : IsPullback (Y.fromSpecResidueField y)
      (Spec.map (β.residueFieldMap y)) β (X.fromSpecResidueField (β y))) :
    (X.fromSpecResidueField (β y)).ker.comap β = (Y.fromSpecResidueField y).ker := by
  let : IsClosedImmersion (X.fromSpecResidueField (β y)) :=
    isClosed_singleton_iff_isClosedImmersion.mp hx
  calc
    (X.fromSpecResidueField (β y)).ker.comap β =
        (pullback.fst β (X.fromSpecResidueField (β y))).ker :=
      (IdealSheafData.ker_fst_of_isClosedImmersion _ β).symm
    _ = (H.isoPullback.hom ≫ pullback.fst β (X.fromSpecResidueField (β y))).ker :=
      (Hom.ker_comp_of_isIso H.isoPullback.hom _).symm
    _ = (Y.fromSpecResidueField y).ker :=
      congrArg (fun i : Spec (Y.residueField y) ⟶ Y => i.ker) H.isoPullback_hom_fst

/-- The original point ideal is unchanged by its actual completion pullback. -/
theorem completionPointCentre_comap
    {A : Type u} [CommRing A] [IsNoetherianRing A] [IsLocalRing A]
    {X : Scheme.{u}} (f : X ⟶ Spec (.of A))
    (y : (pullback f (Scheme.LocalRing.completionSpecMap A) : Scheme.{u}))
    (hy : IsLocalRing.maximalIdeal A ≤
      (f (pullback.fst f (Scheme.LocalRing.completionSpecMap A) y)).asIdeal)
    (hx : IsClosed ({pullback.fst f (Scheme.LocalRing.completionSpecMap A) y} : Set X)) :
    let β := pullback.fst f (Scheme.LocalRing.completionSpecMap A)
    (X.fromSpecResidueField (β y)).ker.comap β =
      ((pullback f (Scheme.LocalRing.completionSpecMap A)).fromSpecResidueField y).ker :=
  pointCentre_comap_of_isPullback _ y hx (completionPoint_isPullback f y hy)

/-- The ordinary point-blowup comparison is the canonical universal flat-base-change map. -/
def pointBlowupBaseChangeIso
    {X Y : Scheme.{u}} (β : Y ⟶ X) [Flat β] (y : Y)
    (hx : IsClosed ({β y} : Set X))
    (H : IsPullback (Y.fromSpecResidueField y)
      (Spec.map (β.residueFieldMap y)) β (X.fromSpecResidueField (β y))) :
    (blowupDatum (Y.fromSpecResidueField y).ker).Y ≅
      pullback (blowupDatum (X.fromSpecResidueField (β y)).ker).map β :=
  BaseChange.isoPullback blowupFlatBaseChange β inferInstance
    (pointCentre_comap_of_isPullback β y hx H) (blowupDatum _) (blowupDatum _)

@[reassoc]
theorem pointBlowupBaseChangeIso_hom_snd
    {X Y : Scheme.{u}} (β : Y ⟶ X) [Flat β] (y : Y)
    (hx : IsClosed ({β y} : Set X))
    (H : IsPullback (Y.fromSpecResidueField y)
      (Spec.map (β.residueFieldMap y)) β (X.fromSpecResidueField (β y))) :
    (pointBlowupBaseChangeIso β y hx H).hom ≫
        pullback.snd (blowupDatum (X.fromSpecResidueField (β y)).ker).map β =
      (blowupDatum (Y.fromSpecResidueField y).ker).map :=
  BaseChange.isoPullback_hom_snd blowupFlatBaseChange β inferInstance
    (pointCentre_comap_of_isPullback β y hx H) (blowupDatum _) (blowupDatum _)

@[reassoc]
theorem pointBlowupBaseChangeIso_hom_fst
    {X Y : Scheme.{u}} (β : Y ⟶ X) [Flat β] (y : Y)
    (hx : IsClosed ({β y} : Set X))
    (H : IsPullback (Y.fromSpecResidueField y)
      (Spec.map (β.residueFieldMap y)) β (X.fromSpecResidueField (β y))) :
    (pointBlowupBaseChangeIso β y hx H).hom ≫
        pullback.fst (blowupDatum (X.fromSpecResidueField (β y)).ker).map β =
      BaseChange.map β (pointCentre_comap_of_isPullback β y hx H)
        (blowupDatum (X.fromSpecResidueField (β y)).ker)
        (blowupDatum (Y.fromSpecResidueField y).ker) :=
  BaseChange.isoPullback_hom_fst blowupFlatBaseChange β inferInstance
    (pointCentre_comap_of_isPullback β y hx H) (blowupDatum _) (blowupDatum _)

end AlgebraicGeometry.Scheme.Blowup

namespace AlgebraicGeometry.Scheme

section NormalizationTransport

variable {V W : Scheme.{u}} [IsIntegral V] [IsIntegral W] (e : V ≅ W)

/-- Transport the original generic normalization using the actual
function-field map of the specified scheme isomorphism. -/
def genericNormalizationMapOfIso :
    (V.fromSpecStalk (genericPoint V)).normalization ⟶
      (W.fromSpecStalk (genericPoint W)).normalization := by
  let γV := V.fromSpecStalk (genericPoint V)
  let γW := W.fromSpecStalk (genericPoint W)
  let σ := Spec.map (CommRingCat.ofHom (functionFieldMap e.hom))
  let m := σ ≫ γW.toNormalization
  let q := γW.fromNormalization ≫ e.inv
  have hnat : γV ≫ e.hom = σ ≫ γW :=
    fromSpecStalk_genericPoint_naturality e.hom
  have hfactor : γV = m ≫ q := by
    calc
      γV = (γV ≫ e.hom) ≫ e.inv := by simp
      _ = (σ ≫ γW) ≫ e.inv := congrArg (fun k => k ≫ e.inv) hnat
      _ = m ≫ q := by
        simp only [m, q, Category.assoc, Hom.toNormalization_fromNormalization_assoc]
  exact γV.normalizationDesc m q hfactor

/-- The transported normalization retains its original structural map. -/
@[reassoc]
theorem genericNormalizationMapOfIso_over :
    genericNormalizationMapOfIso e ≫
        (W.fromSpecStalk (genericPoint W)).fromNormalization =
      (V.fromSpecStalk (genericPoint V)).fromNormalization ≫ e.hom := by
  let γV := V.fromSpecStalk (genericPoint V)
  let γW := W.fromSpecStalk (genericPoint W)
  have h : genericNormalizationMapOfIso e ≫ (γW.fromNormalization ≫ e.inv) =
      γV.fromNormalization := by
    dsimp only [genericNormalizationMapOfIso]
    exact Hom.normalizationDesc_comp _ _ _ _
  apply (cancel_mono e.inv).mp
  calc
    (genericNormalizationMapOfIso e ≫ γW.fromNormalization) ≫ e.inv =
        γV.fromNormalization := (Category.assoc _ _ _).trans h
    _ = (γV.fromNormalization ≫ e.hom) ≫ e.inv := by simp

/-- The generic restriction uses the original function-field map of `e.hom`. -/
@[reassoc]
theorem genericNormalizationMapOfIso_generic :
    (V.fromSpecStalk (genericPoint V)).toNormalization ≫
        genericNormalizationMapOfIso e =
      Spec.map (CommRingCat.ofHom (functionFieldMap e.hom)) ≫
        (W.fromSpecStalk (genericPoint W)).toNormalization := by
  dsimp only [genericNormalizationMapOfIso]
  exact Hom.toNormalization_normalizationDesc _ _ _ _

private theorem genericSpecMaps_comp_inverse :
    Spec.map (CommRingCat.ofHom (functionFieldMap e.hom)) ≫
        Spec.map (CommRingCat.ofHom (functionFieldMap e.inv)) =
      𝟙 (Spec V.functionField) := by
  apply (cancel_mono (V.fromSpecStalk (genericPoint V))).mp
  rw [Category.assoc, ← fromSpecStalk_genericPoint_naturality e.inv,
    ← Category.assoc, ← fromSpecStalk_genericPoint_naturality e.hom,
    Category.assoc, e.hom_inv_id, Category.comp_id]
  exact (Category.id_comp (V.fromSpecStalk (genericPoint V))).symm

private theorem genericNormalizationMapOfIso_comp_symm :
    genericNormalizationMapOfIso e ≫ genericNormalizationMapOfIso e.symm =
      𝟙 (V.fromSpecStalk (genericPoint V)).normalization := by
  let γV := V.fromSpecStalk (genericPoint V)
  let γW := W.fromSpecStalk (genericPoint W)
  let a := genericNormalizationMapOfIso e
  let b := genericNormalizationMapOfIso e.symm
  apply Hom.normalization.hom_ext γV (a ≫ b) (𝟙 _) γV.fromNormalization
  · change γV.toNormalization ≫ (a ≫ b) = γV.toNormalization ≫ 𝟙 _
    rw [← Category.assoc, genericNormalizationMapOfIso_generic]
    rw [Category.assoc, genericNormalizationMapOfIso_generic e.symm]
    rw [← Category.assoc, genericSpecMaps_comp_inverse e,
      Category.id_comp, Category.comp_id]
  · change (a ≫ b) ≫ γV.fromNormalization = γV.fromNormalization
    rw [Category.assoc, genericNormalizationMapOfIso_over e.symm,
      ← Category.assoc, genericNormalizationMapOfIso_over e,
      Category.assoc]
    change γV.fromNormalization ≫ e.hom ≫ e.inv = γV.fromNormalization
    rw [e.hom_inv_id, Category.comp_id]
  · exact Category.id_comp _

/-- The canonical isomorphism between the two original generic normalizations. -/
def genericNormalizationIsoOfIso :
    (V.fromSpecStalk (genericPoint V)).normalization ≅
      (W.fromSpecStalk (genericPoint W)).normalization where
  hom := genericNormalizationMapOfIso e
  inv := genericNormalizationMapOfIso e.symm
  hom_inv_id := private_decl% (genericNormalizationMapOfIso_comp_symm e)
  inv_hom_id := private_decl% (genericNormalizationMapOfIso_comp_symm e.symm)

@[reassoc]
theorem genericNormalizationIsoOfIso_hom_over :
    (genericNormalizationIsoOfIso e).hom ≫
        (W.fromSpecStalk (genericPoint W)).fromNormalization =
      (V.fromSpecStalk (genericPoint V)).fromNormalization ≫ e.hom :=
  genericNormalizationMapOfIso_over e

@[reassoc]
theorem genericNormalizationIsoOfIso_hom_generic :
    (V.fromSpecStalk (genericPoint V)).toNormalization ≫
        (genericNormalizationIsoOfIso e).hom =
      Spec.map (CommRingCat.ofHom (functionFieldMap e.hom)) ≫
        (W.fromSpecStalk (genericPoint W)).toNormalization :=
  genericNormalizationMapOfIso_generic e

end NormalizationTransport

end AlgebraicGeometry.Scheme

namespace AlgebraicGeometry.Scheme.Blowup

private theorem proper_point_image_closedPoint
    {A : Type u} [CommRing A] [IsLocalRing A]
    {Y : Scheme.{u}} (p : Y ⟶ Spec (.of A)) [IsProper p]
    (y : Y) (hy : IsClosed ({y} : Set Y)) :
    p y = (show Spec (.of A) from IsLocalRing.closedPoint A) := by
  have hp : IsClosed ({p y} : Set (Spec (.of A))) := by
    simpa only [Set.image_singleton] using p.isClosedMap _ hy
  apply PrimeSpectrum.ext
  exact IsLocalRing.eq_maximalIdeal
    ((PrimeSpectrum.isClosed_singleton_iff_isMaximal (p y)).mp hp)

/-- A specified closed point of the completed proper model lies on the
original closed fibre and gives a closed point of the original model. -/
theorem completionClosedPoint_data
    {A : Type u} [CommRing A] [IsNoetherianRing A] [IsLocalRing A]
    {X : Scheme.{u}} (f : X ⟶ Spec (.of A)) [IsProper f]
    (y : (pullback f (Scheme.LocalRing.completionSpecMap A) : Scheme.{u}))
    (hy : IsClosed
      ({y} : Set (pullback f (Scheme.LocalRing.completionSpecMap A) : Scheme.{u}))) :
    let β := pullback.fst f (Scheme.LocalRing.completionSpecMap A)
    IsClosed ({β y} : Set X) ∧
      IsLocalRing.maximalIdeal A ≤ (f (β y)).asIdeal := by
  let H := AdicCompletion (IsLocalRing.maximalIdeal A) A
  let Y : Scheme.{u} := pullback f (Scheme.LocalRing.completionSpecMap A)
  let β : Y ⟶ X := pullback.fst f (Scheme.LocalRing.completionSpecMap A)
  let p : Y ⟶ Spec (.of H) := pullback.snd f (Scheme.LocalRing.completionSpecMap A)
  have hpy := proper_point_image_closedPoint p y hy
  let FY : Scheme.{u} := pullback p (Scheme.LocalRing.residueSpecMap H)
  let FX : Scheme.{u} := pullback f (Scheme.LocalRing.residueSpecMap A)
  let iY : FY ⟶ Y := pullback.fst p (Scheme.LocalRing.residueSpecMap H)
  let iX : FX ⟶ X := pullback.fst f (Scheme.LocalRing.residueSpecMap A)
  have hyrange : y ∈ Set.range iY := by
    change y ∈ Set.range (pullback.fst p (Scheme.LocalRing.residueSpecMap H))
    rw [Scheme.Pullback.range_fst]
    exact ⟨IsLocalRing.closedPoint (IsLocalRing.ResidueField H),
      (IsLocalRing.comap_closedPoint (IsLocalRing.residue H)).trans hpy.symm⟩
  obtain ⟨u, hu⟩ := hyrange
  have hpre : iY ⁻¹' ({y} : Set Y) = ({u} : Set FY) := by
    ext z
    change iY z = y ↔ z = u
    rw [← hu]
    exact iY.isClosedEmbedding.injective.eq_iff
  have huclosed : IsClosed ({u} : Set FY) := by
    rw [← hpre]
    exact hy.preimage iY.continuous
  let E : FY ≅ FX := Scheme.LocalRing.completionResidueFiberIso f
  have hzclosed : IsClosed ({E.hom u} : Set FX) := by
    simpa only [Set.image_singleton] using E.hom.isClosedMap _ huclosed
  have hxclosed : IsClosed ({iX (E.hom u)} : Set X) := by
    simpa only [Set.image_singleton] using iX.isClosedMap _ hzclosed
  have hvalue : iX (E.hom u) = β y := by
    have h := congrArg (fun k : FY ⟶ X => k u)
      (Scheme.LocalRing.completionResidueFiberIso_hom_fst f)
    change iX (E.hom u) = β (iY u) at h
    exact h.trans (congrArg β hu)
  have htri : f (β y) = Scheme.LocalRing.completionSpecMap A (p y) := by
    have h := congrArg (fun k : Y ⟶ Spec (.of A) => k y)
      (pullback.condition (f := f) (g := Scheme.LocalRing.completionSpecMap A))
    exact h
  have hbase : f (β y) = (show Spec (.of A) from IsLocalRing.closedPoint A) :=
    htri.trans ((congrArg (Scheme.LocalRing.completionSpecMap A) hpy).trans
      (IsLocalRing.comap_closedPoint (algebraMap A H)))
  refine ⟨?_, ?_⟩
  · rwa [hvalue] at hxclosed
  · exact (congrArg (fun z : Spec (.of A) => z.asIdeal) hbase).symm.le

/-- Relabeling the original completed model by an actual isomorphism keeps
the point square and the original residue map of the composite projection. -/
theorem completionPoint_isPullback_of_iso
    {A : Type u} [CommRing A] [IsNoetherianRing A] [IsLocalRing A]
    {X Y : Scheme.{u}} (f : X ⟶ Spec (.of A))
    (e : Y ≅ pullback f (Scheme.LocalRing.completionSpecMap A)) (y : Y)
    (hy : IsLocalRing.maximalIdeal A ≤
      (f (pullback.fst f (Scheme.LocalRing.completionSpecMap A) (e.hom y))).asIdeal) :
    let p := e.hom ≫ pullback.fst f (Scheme.LocalRing.completionSpecMap A)
    IsPullback (Y.fromSpecResidueField y) (Spec.map (p.residueFieldMap y))
      p (X.fromSpecResidueField (p y)) := by
  let β := pullback.fst f (Scheme.LocalRing.completionSpecMap A)
  have he : IsPullback (Y.fromSpecResidueField y)
      (Spec.map (e.hom.residueFieldMap y)) e.hom
      ((pullback f (Scheme.LocalRing.completionSpecMap A)).fromSpecResidueField (e.hom y)) :=
    IsPullback.of_vert_isIso
      ⟨(e.hom.SpecMap_residueFieldMap_fromSpecResidueField y).symm⟩
  have hc := completionPoint_isPullback f (e.hom y) hy
  let residueMap : X.residueField (β (e.hom y)) ⟶ Y.residueField y :=
    (e.hom ≫ β).residueFieldMap y
  have hresidue : residueMap = β.residueFieldMap (e.hom y) ≫
      e.hom.residueFieldMap y := Scheme.residueFieldMap_comp e.hom β y
  change IsPullback (Y.fromSpecResidueField y)
    (Spec.map residueMap) (e.hom ≫ β)
    (X.fromSpecResidueField (β (e.hom y)))
  rw [hresidue, Spec.map_comp]
  exact he.paste_vert hc

private theorem ne_genericPoint_of_closedFibre
    {A : Type u} [CommRing A] [IsLocalRing A] [IsDomain A]
    {X : Scheme.{u}} [IsIntegral X] (f : X ⟶ Spec (.of A)) [IsDominant f]
    (hd : ringKrullDim A = 2) (x : X)
    (hx : IsLocalRing.maximalIdeal A ≤ (f x).asIdeal) : x ≠ genericPoint X := by
  intro h
  have hgen : f x = (⊥ : PrimeSpectrum A) := by
    rw [h, Scheme.map_genericPoint_of_isDominant,
      genericPoint_eq_bot_of_affine]
  have hm : IsLocalRing.maximalIdeal A = ⊥ := by
    have hbot := hx
    rw [hgen] at hbot
    change IsLocalRing.maximalIdeal A ≤ (⊥ : Ideal A) at hbot
    exact le_bot_iff.mp hbot
  let : Field A := (IsLocalRing.isField_iff_maximalIdeal_eq.mpr hm).toField
  have hzero : ringKrullDim A = 0 := ringKrullDim_eq_zero_of_field A
  rw [hd] at hzero
  norm_num at hzero

private theorem ordinaryPoint_stalkMap_isIso_off_centre
    {Y : Scheme.{u}} (y : Y) (hy : IsClosed ({y} : Set Y))
    (v : (blowupDatum (Y.fromSpecResidueField y).ker).Y)
    (hv : (blowupDatum (Y.fromSpecResidueField y).ker).map v ≠ y) :
    IsIso ((blowupDatum (Y.fromSpecResidueField y).ker).map.stalkMap v) := by
  let B := blowupDatum (Y.fromSpecResidueField y).ker
  let U : Y.Opens := ⟨({y} : Set Y)ᶜ, hy.isOpen_compl⟩
  let : IsClosedImmersion (Y.fromSpecResidueField y) :=
    isClosed_singleton_iff_isClosedImmersion.mp hy
  have hU : Disjoint (U : Set Y) ((Y.fromSpecResidueField y).ker.support : Set Y) := by
    rw [Scheme.Hom.support_ker, Scheme.range_fromSpecResidueField, hy.closure_eq]
    exact Set.disjoint_left.mpr fun z hz hz' => hz hz'
  let : IsIso (B.map ∣_ U) := B.restrict_isIso_of_disjoint U hU
  let p : (B.map ⁻¹ᵁ U).toScheme := ⟨v, hv⟩
  let e := Scheme.Hom.stalkMapIsoOfIsPullbackOfFlatOfPreimmersion
    (isPullback_morphismRestrict B.map U).flip p v rfl
  exact ((MorphismProperty.isomorphisms CommRingCat).arrow_mk_iso_iff e).mpr inferInstance

/-- Descend one specified normalized point blowup from an actual completed
proper birational model. The lower normalization finiteness, original point
ideal equality and both comparison projections are derived here. -/
theorem exists_normalizedPointCompletion
    {A : Type u} [CommRing A] [IsNoetherianRing A] [IsLocalRing A] [IsDomain A]
    [IsDomain (AdicCompletion (IsLocalRing.maximalIdeal A) A)]
    {X Y : Scheme.{u}} [IsIntegral X] [IsIntegral Y]
    (f : X ⟶ Spec (.of A)) [IsProper f] [IsDominant f]
    (hd : ringKrullDim A = 2)
    (hff : IsIso (CommRingCat.ofHom (Scheme.functionFieldMap f)))
    (e : Y ≅ pullback f (Scheme.LocalRing.completionSpecMap A))
    (hY : NormalStalks Y) (y : Y) (hy : IsClosed ({y} : Set Y))
    (hyne : y ≠ genericPoint Y) :
    let π := e.hom ≫ pullback.fst f (Scheme.LocalRing.completionSpecMap A)
    let x := π y
    ∃ (hx : IsClosed ({x} : Set X)) (hxne : x ≠ genericPoint X)
      (hI : (X.fromSpecResidueField x).ker.comap π = (Y.fromSpecResidueField y).ker),
      let BX := blowupDatum (X.fromSpecResidueField x).ker
      let BY := blowupDatum (Y.fromSpecResidueField y).ker
      letI : IsIntegral BX.Y := pointBlowup_isIntegral X x hx hxne
      letI : IsIntegral BY.Y := pointBlowup_isIntegral Y y hy hyne
      let νX := (BX.Y.fromSpecStalk (genericPoint BX.Y)).fromNormalization
      let νY := (BY.Y.fromSpecStalk (genericPoint BY.Y)).fromNormalization
      IsFinite νX ∧
        ∃ E : (BY.Y.fromSpecStalk (genericPoint BY.Y)).normalization ≅
            pullback (νX ≫ BX.map ≫ f) (Scheme.LocalRing.completionSpecMap A),
          E.hom ≫ pullback.snd (νX ≫ BX.map ≫ f)
              (Scheme.LocalRing.completionSpecMap A) =
            νY ≫ BY.map ≫ e.hom ≫ pullback.snd f (Scheme.LocalRing.completionSpecMap A) ∧
          E.hom ≫ pullback.fst (νX ≫ BX.map ≫ f)
              (Scheme.LocalRing.completionSpecMap A) ≫ νX =
            νY ≫ BaseChange.map π hI BX BY := by
  let c := Scheme.LocalRing.completionSpecMap A
  let β := pullback.fst f c
  let π := e.hom ≫ β
  let gY := e.hom ≫ pullback.snd f c
  let x := π y
  have hyhat : IsClosed ({e.hom y} : Set (pullback f c : Scheme.{u})) := by
    simpa only [Set.image_singleton] using e.hom.isClosedMap _ hy
  have hdata := completionClosedPoint_data f (e.hom y) hyhat
  have hx : IsClosed ({x} : Set X) := hdata.1
  have hbase : IsLocalRing.maximalIdeal A ≤ (f x).asIdeal := hdata.2
  have hxne : x ≠ genericPoint X := ne_genericPoint_of_closedFibre f hd x hbase
  have hpoint : IsPullback (Y.fromSpecResidueField y)
      (Spec.map (π.residueFieldMap y)) π (X.fromSpecResidueField x) :=
    completionPoint_isPullback_of_iso f e y hbase
  have hI : (X.fromSpecResidueField x).ker.comap π = (Y.fromSpecResidueField y).ker :=
    pointCentre_comap_of_isPullback π y hx hpoint
  let BX := blowupDatum (X.fromSpecResidueField x).ker
  let BY := blowupDatum (Y.fromSpecResidueField y).ker
  let : IsIntegral BX.Y := pointBlowup_isIntegral X x hx hxne
  let : IsIntegral BY.Y := pointBlowup_isIntegral Y y hy hyne
  let : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian f
  let : IsProper BX.map := BX.isProper_of_isLocallyNoetherian
  let : IsDominant BX.map := pointBlowup_isDominant X x hx hxne
  let w := BX.map ≫ f
  let : IsProper w := inferInstance
  let : IsDominant w := inferInstance
  let := hff
  let : IsIso (CommRingCat.ofHom (Scheme.functionFieldMap BX.map)) :=
    BX.functionFieldMap_isIso (genericPoint_not_mem_pointCentre x hx hxne)
  have hffw : IsIso (CommRingCat.ofHom (Scheme.functionFieldMap w)) := by
    change IsIso (CommRingCat.ofHom (Scheme.functionFieldMap (BX.map ≫ f)))
    rw [Scheme.functionFieldMap_comp, CommRingCat.ofHom_comp]
    infer_instance
  let : Flat c := (CompletionNormalization.completion_flat_surjective A).1
  let : Surjective c := (CompletionNormalization.completion_flat_surjective A).2
  let : Flat β := MorphismProperty.of_isPullback
    (P := @Flat) (IsPullback.of_hasPullback f c).flip inferInstance
  let : Flat π := by
    dsimp only [π]
    infer_instance
  have Hmodel : IsPullback π gY f c :=
    IsPullback.of_iso_pullback
      ⟨by simp only [π, gY, β, Category.assoc, pullback.condition]⟩ e rfl rfl
  let bmap := BaseChange.map π hI BX BY
  have Hblowup : IsPullback bmap BY.map BX.map π :=
    BaseChange.isPullback_of_flat π inferInstance hI BX BY
  have Htotal : IsPullback bmap (BY.map ≫ gY) w c := Hblowup.paste_vert Hmodel
  let b : BY.Y ≅ pullback w c := Htotal.isoPullback
  let What : Scheme.{u} := pullback w c
  let : IsIntegral What := IsIntegral.of_isIso b.hom
  have hbInv : b.inv ≫ bmap = pullback.fst w c := by
    calc
      b.inv ≫ bmap = b.inv ≫ b.hom ≫ pullback.fst w c :=
        congrArg (fun k => b.inv ≫ k) Htotal.isoPullback_hom_fst.symm
      _ = pullback.fst w c := b.inv_hom_id_assoc _
  have hnormal : ∀ z : What,
      ¬ IsLocalRing.maximalIdeal A ≤ (w (pullback.fst w c z)).asIdeal →
        IsIntegrallyClosed (What.presheaf.stalk z) := by
    intro z hz
    let v := b.inv z
    have hproj : bmap v = pullback.fst w c z :=
      congrArg (fun k : What ⟶ BX.Y => k z) hbInv
    have htri : BX.map (bmap v) = π (BY.map v) :=
      congrArg (fun k : BY.Y ⟶ X => k v) (BaseChange.map_triangle π hI BX BY)
    have hv : BY.map v ≠ y := by
      intro h
      apply hz
      have hvalue : w (pullback.fst w c z) = f x := by
        change f (BX.map (pullback.fst w c z)) = f x
        rw [← hproj, htri, h]
      rwa [hvalue]
    let : IsIntegrallyClosed (Y.presheaf.stalk (BY.map v)) := (hY (BY.map v)).2
    let : IsIso (BY.map.stalkMap v) := ordinaryPoint_stalkMap_isIso_off_centre y hy v hv
    let : IsIntegrallyClosed (BY.Y.presheaf.stalk v) :=
      IsIntegrallyClosed.of_equiv (asIso (BY.map.stalkMap v)).commRingCatIsoToRingEquiv
    let : IsIso (b.inv.stalkMap z) :=
      ((IsOpenImmersion.iff_isIso_stalkMap (f := b.inv)).mp inferInstance).2 z
    exact IsIntegrallyClosed.of_equiv (asIso (b.inv.stalkMap z)).commRingCatIsoToRingEquiv
  have hC2 := CompletionNormalization.finite_normalization_and_isIso_completionComparison
    w hd hffw hnormal
  let νX := (BX.Y.fromSpecStalk (genericPoint BX.Y)).fromNormalization
  let νY := (BY.Y.fromSpecStalk (genericPoint BY.Y)).fromNormalization
  let νWhat := (What.fromSpecStalk (genericPoint What)).fromNormalization
  let E := genericNormalizationIsoOfIso b ≪≫
    CompletionNormalization.normalizationCompletionIso w hd hffw hnormal
  have hC2model : CompletionNormalization.completionComparison A w ≫
      pullback.fst (νX ≫ w) c ≫ νX = νWhat ≫ pullback.fst w c := by
    let := genericNormalization_isDominant What
    have hfst := CompletionNormalization.completionComparison_fst (A := CommRingCat.of A) w
    have h := congrArg (fun k => k ≫ νX) hfst
    exact (Category.assoc _ _ _).symm.trans
      (h.trans (genericNormalizationLift_over (νWhat ≫ pullback.fst w c)
        (genericNormalization_normalStalks What)))
  have hEsnd : E.hom ≫ pullback.snd (νX ≫ w) c = νY ≫ BY.map ≫ gY := by
    dsimp only [E, Iso.trans_hom, CompletionNormalization.normalizationCompletionIso,
      asIso_hom]
    rw [Category.assoc, CompletionNormalization.completionComparison_snd,
      ← Category.assoc, genericNormalizationIsoOfIso_hom_over,
      Category.assoc, Htotal.isoPullback_hom_snd]
  have hEmodel : E.hom ≫ pullback.fst (νX ≫ w) c ≫ νX = νY ≫ bmap := by
    dsimp only [E, Iso.trans_hom, CompletionNormalization.normalizationCompletionIso,
      asIso_hom]
    rw [Category.assoc, hC2model, ← Category.assoc,
      genericNormalizationIsoOfIso_hom_over, Category.assoc,
      Htotal.isoPullback_hom_fst]
  exact ⟨hx, hxne, hI, hC2.1, E, hEsnd, hEmodel⟩

end AlgebraicGeometry.Scheme.Blowup
