/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Spec.AffineFiniteResiduePoint
public import Aglib.AlgebraicGeometry.Spec.AffineFiniteSectionAlgebra
public import Aglib.AlgebraicGeometry.Spec.HartogsEtaleLocal
public import Aglib.AlgebraicGeometry.Spec.PowerSeriesHartogsSmoothFiniteAlgebra
public import Aglib.AlgebraicGeometry.AffineScheme.BaseChangeChart
public import Aglib.AlgebraicGeometry.Normalization.GenericFiniteEtale.SmoothRelativePurityCompletion
public import Aglib.AlgebraicGeometry.Morphisms.FiniteType.ClosedFiberSpecialization
public import Aglib.AlgebraicGeometry.Morphisms.Etale.PointwiseOpenBaseChange
public import Aglib.RingTheory.Smooth.SplitSectionAugmentation

/-! # The original smooth relative-purity step

This step uses the same affine source algebra, the original tensor chart,
and its actual section completion. The closed point of the power-series
ring used for descent is distinct from its extended-maximal-ideal generic
point used for effectivity. No new normalization or cover model is chosen.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits IsLocalRing
open scoped TensorProduct

namespace AlgebraicGeometry.Scheme.Hom

universe u

/-- The five effectivity inputs are constructed from the original puncture,
section and chart. Pointwise flat descent retains the same finite algebra
and the original point above the section's closed point. -/
theorem etaleAt_of_original_flat_local_section
    (A B C R : Type u) [CommRing A] [CommRing B] [CommRing C] [CommRing R]
    [IsDomain A] [IsLocalRing A] [IsNoetherianRing A] [IsIntegrallyClosed A]
    [IsDomain B] [Algebra A B] [Algebra.Smooth A B]
    [IsDomain C] [IsIntegrallyClosed C] [Algebra B C]
    [FaithfulSMul B C] [Module.Finite B C]
    [IsLocalRing R] [Algebra A R] [Algebra.EssFiniteType A R] [Module.Flat A R]
    (hm : (maximalIdeal A).map (algebraMap A R) = maximalIdeal R)
    {X : Scheme.{u}} (p : X ⟶ Spec (.of A)) [GeometricallyIrreducible p]
    (s : Spec (.of A) ⟶ X) (hs : s ≫ p = 𝟙 _)
    (j : Spec (.of B) ⟶ X) [IsOpenImmersion j]
    (hj : j ≫ p = Spec.algebraMap A B)
    (E : X.Opens) (hsE : Set.range s ⊆ E)
    (hpE : p ⁻¹ᵁ puncturedSpecOpen A ≤ E)
    [Etale (Spec.algebraMap B C ∣_ (j ⁻¹ᵁ E))]
    (hdim : 2 ≤ ringKrullDim A) (ε : B →ₐ[A] R)
    (hbad : j (Spec.map (CommRingCat.ofHom ε.toRingHom) (closedPoint R)) ∉ E)
    (y : Spec (.of C))
    (hy : Spec.algebraMap B C y =
      Spec.map (CommRingCat.ofHom ε.toRingHom) (closedPoint R)) :
    (Spec.algebraMap B C).etaleAt y := by
  let : IsNoetherianRing R := Algebra.EssFiniteType.isNoetherianRing A R
  let : IsNoetherianRing B := Algebra.EssFiniteType.isNoetherianRing A B
  let D := B ⊗[A] R
  let : Algebra R D := Algebra.TensorProduct.rightAlgebra
  let ecomm : R ⊗[A] B ≃ₐ[R] D :=
    { __ := Algebra.TensorProduct.comm A R B, commutes' _ := rfl }
  let : Algebra.Smooth R D := Algebra.Smooth.of_equiv ecomm
  let : IsNoetherianRing D := Algebra.EssFiniteType.isNoetherianRing R D
  let εD : D →ₐ[R] R :=
    { (Algebra.TensorProduct.lift ε (AlgHom.id A R) (fun _ _ => .all _ _)).toRingHom with
      commutes' r := by
        change (Algebra.TensorProduct.lift ε (AlgHom.id A R)
          (fun _ _ => .all _ _)) (1 ⊗ₜ[A] r) = r
        rw [Algebra.TensorProduct.lift_tmul, map_one, one_mul]
        rfl }
  obtain ⟨n, _, e, _, heaug⟩ := Algebra.Smooth.exists_fin_splitSectionCompletion_augmentation εD
  let PS := MvPowerSeries (Fin n) R
  let φ := smoothCompletionPowerSeriesMap εD (Fin n) e
  let γ : B →+* PS := φ.toRingHom.comp (algebraMap B D)
  let : Algebra B PS := γ.toAlgebra
  let : Module.Flat B PS := RingHom.flat_algebraMap_iff.mp
    ((RingHom.flat_algebraMap_iff.mpr (inferInstance : Module.Flat B D)).comp
      (smoothCompletionPowerSeriesMap_flat εD (Fin n) e))
  let i := AffineBaseChange.tensorChartMap (C := R) p j hj
  let a := Spec.algebraMap A R
  let g := Spec.algebraMap B PS ≫ j
  have hcomp : Spec.map (CommRingCat.ofHom φ.toRingHom) ≫ i ≫ pullback.fst p a = g := by
    rw [AffineBaseChange.tensorChartMap_fst, ← Category.assoc, ← Spec.map_comp]
    rfl
  have hi : i ≫ pullback.snd p a = Spec.algebraMap R D :=
    AffineBaseChange.tensorChartMap_snd p j hj
  let c := Spec.map (CommRingCat.ofHom (MvPowerSeries.C : R →+* PS))
  let z := Spec.map (CommRingCat.ofHom (MvPowerSeries.constantCoeff : PS →+* R))
  have hg : g ≫ p = c ≫ a := by
    rw [Category.assoc, hj]
    change Spec.map _ ≫ Spec.map _ = Spec.map _ ≫ Spec.map _
    rw [← Spec.map_comp, ← Spec.map_comp]
    congr 1
    apply CommRingCat.hom_ext
    apply RingHom.ext
    intro r
    change φ ((algebraMap B D) (algebraMap A B r)) =
      MvPowerSeries.C (algebraMap A R r)
    rw [← IsScalarTower.algebraMap_apply A B D,
      IsScalarTower.algebraMap_apply A R D, φ.commutes]
    rfl
  have haug : (MvPowerSeries.constantCoeff : PS →+* R).comp
      (algebraMap B PS) = ε.toRingHom := by
    apply RingHom.ext
    intro b
    have he := RingHom.congr_fun heaug (e.symm (algebraMap D _ (algebraMap B D b)))
    change MvPowerSeries.constantCoeff (e.symm (algebraMap D _ (algebraMap B D b))) = ε b
    rw [← he]
    change AdicCompletion.kerProj (Algebra.Smooth.splitSection_surjective εD)
      (e (e.symm (algebraMap D _ (algebraMap B D b)))) = ε b
    rw [e.apply_symm_apply]
    change AdicCompletion.kerProj (Algebra.Smooth.splitSection_surjective εD)
      (AdicCompletion.of (RingHom.ker εD.toRingHom) D (algebraMap B D b)) = ε b
    refine (AdicCompletion.kerProj_of (f := εD)
      (Algebra.Smooth.splitSection_surjective εD) (algebraMap B D b)).trans ?_
    change (Algebra.TensorProduct.lift ε (AlgHom.id A R)
      (fun _ _ => .all _ _)) (b ⊗ₜ[A] 1) = ε b
    rw [Algebra.TensorProduct.lift_tmul, map_one, mul_one]
  have hz : z ≫ g = Spec.map (CommRingCat.ofHom ε.toRingHom) ≫ j := by
    change Spec.map _ ≫ (Spec.map _ ≫ j) = _
    rw [← Category.assoc, ← Spec.map_comp, ← CommRingCat.ofHom_comp, haug]
  let U := puncturedSpecOpen R
  let V := g ⁻¹ᵁ E
  have hpuncture : a ⁻¹ᵁ puncturedSpecOpen A = U :=
    preimage_puncturedSpecOpen_of_map_maximalIdeal (algebraMap A R) hm
  have hA : Function.Bijective (affineScalarMap (puncturedSpecOpen A).ι) := by
    have h := puncturedSpecScalarMap_bijective A hdim
    rw [← affineScalarMap_topIso (puncturedSpecOpen A)] at h
    exact Function.Bijective.of_comp_left
      (f := (puncturedSpecOpen A).topIso.hom.hom)
      (g := affineScalarMap (puncturedSpecOpen A).ι) h
      (ConcreteCategory.bijective_of_isIso (puncturedSpecOpen A).topIso.hom).injective
  have hU : Function.Bijective (affineScalarMap U.ι) :=
    puncturedAffineScalar_bijective_of_flat_of_map_maximalIdeal (algebraMap A R)
      (RingHom.flat_algebraMap_iff.mpr inferInstance) hm hA
  have hbase : Spec.algebraMap B PS ⁻¹ᵁ
      (Spec.algebraMap A B ⁻¹ᵁ puncturedSpecOpen A) ≤ V := by
    intro q hq
    apply hpE
    change p (g q) ∈ puncturedSpecOpen A
    change (g ≫ p) q ∈ puncturedSpecOpen A
    change ((Spec.algebraMap B PS ≫ j) ≫ p) q ∈ puncturedSpecOpen A
    rw [Category.assoc, hj]
    exact hq
  have hUV : c ⁻¹ᵁ U ≤ V := by
    intro q hq
    apply hpE
    change (g ≫ p) q ∈ puncturedSpecOpen A
    rw [hg]
    change c q ∈ a ⁻¹ᵁ puncturedSpecOpen A
    rw [hpuncture]
    exact hq
  have hzero : z ⁻¹ᵁ V = U := by
    ext q
    change g (z q) ∈ E ↔ q ≠ closedPoint R
    constructor
    · intro h hq
      subst q
      apply hbad
      have he := congrArg (fun k => k (closedPoint R)) hz
      exact he ▸ h
    · intro hq
      apply hpE
      change (z ≫ g ≫ p) q ∈ puncturedSpecOpen A
      rw [hg]
      have hzc : z ≫ c = 𝟙 _ := by
        rw [← Spec.map_comp, ← Spec.map_id]
        congr 1
      rw [← Category.assoc, hzc, Category.id_comp]
      change q ∈ a ⁻¹ᵁ puncturedSpecOpen A
      rw [hpuncture]
      exact hq
  have hmem : powerSeriesClosedFiberPoint (Fin n) R ∈ V := by
    have h := completionPoint_mem_sectionOpen_of_baseChange p s hs E hsE R D a i hi εD
      (Fin n) e
    rw [hcomp] at h
    exact h
  let T := PS ⊗[B] C
  have het := property_morphismRestrict_of_isPullback (@Etale)
    (isPullback_tensorSpec B PS C) (j ⁻¹ᵁ E) inferInstance
  let : Etale (Spec.algebraMap PS T ∣_ V) := by
    simpa only [V, g, Hom.comp_preimage] using het
  let : IsLocalHom (MvPowerSeries.constantCoeff : PS →+* R) :=
    ⟨fun _ h => MvPowerSeries.isUnit_iff_constantCoeff.mpr h⟩
  have hzcpoint : z (closedPoint R) = closedPoint PS := by
    apply PrimeSpectrum.ext
    exact maximalIdeal_comap (MvPowerSeries.constantCoeff : PS →+* R)
  have hpoint : Spec.algebraMap B PS (closedPoint PS) =
      Spec.map (CommRingCat.ofHom ε.toRingHom) (closedPoint R) := by
    rw [← hzcpoint]
    change (z ≫ Spec.algebraMap B PS) (closedPoint R) = _
    have he : z ≫ Spec.algebraMap B PS = Spec.map (CommRingCat.ofHom ε.toRingHom) := by
      rw [← Spec.map_comp, ← CommRingCat.ofHom_comp, haug]
    rw [he]
  obtain ⟨Q, hQ, _⟩ := exists_preimage_of_isPullback
    (isPullback_tensorSpec B PS C) y (closedPoint PS) (hy.trans hpoint.symm)
  have h := powerSeriesHartogsSmoothFiniteTensor_etaleAt_image
    A B C R (Fin n) hdim U hU V hbase hUV hzero hmem Q
  exact hQ ▸ h

/-- The full relative-purity step for the original finite normal source.
The only open is its canonical target etale locus. The section and the full
puncture inputs are the ones supplied by the local-dimension induction. -/
theorem etale_of_puncture_and_section
    (A : Type u) [CommRing A] [IsDomain A] [IsLocalRing A]
    [IsNoetherianRing A] [IsIntegrallyClosed A]
    {X Y : Scheme.{u}} [IsIntegral X] [IsIntegral Y]
    [∀ y : Y, IsIntegrallyClosed (Y.presheaf.stalk y)]
    (p : X ⟶ Spec (.of A)) [Smooth p] [GeometricallyIrreducible p]
    (f : Y ⟶ X) [IsFinite f] [IsDominant f]
    (s : Spec (.of A) ⟶ X) (hs : s ≫ p = 𝟙 _)
    (hdim : 2 ≤ ringKrullDim A)
    (hsE : Set.range s ⊆ f.etaleTargetOpen f.isClosedMap)
    (hpE : p ⁻¹ᵁ puncturedSpecOpen A ≤ f.etaleTargetOpen f.isClosedMap) : Etale f := by
  classical
  let E := f.etaleTargetOpen f.isClosedMap
  have htop : ∀ x : X, x ∈ E := by
    intro x
    by_contra hx
    have hpx : p x = closedPoint A := by
      by_contra h
      exact hx (hpE h)
    obtain ⟨z, hzclosed, _, hzbad, _⟩ :=
      exists_closed_fiber_specialization_outside_open p (closedPoint A) x hpx E hx
    have hbadsource : ∃ y : Y, ¬ f.etaleAt y ∧ f y = p.fiberι (closedPoint A) z := by
      change ¬ ¬ ∃ y, y ∈ (f.etaleSourceOpen : Set Y)ᶜ ∧
        f y = p.fiberι (closedPoint A) z at hzbad
      exact not_not.mp hzbad
    obtain ⟨y, hynot, hy⟩ := hbadsource
    let L := (p.fiber (closedPoint A)).residueField z
    let c : Spec (.of L) ⟶ X :=
      (p.fiber (closedPoint A)).fromSpecResidueField z ≫ p.fiberι (closedPoint A)
    have hcimage : c (closedPoint L) = p.fiberι (closedPoint A) z := by
      exact congrArg (p.fiberι (closedPoint A))
        ((p.fiber (closedPoint A)).fromSpecResidueField_apply z (closedPoint L))
    let : IsClosedImmersion c :=
      AffineFiniteResiduePoint.closedFiberPoint_isClosedImmersion p z hzclosed
    have hcbase : (c ≫ p) (closedPoint L) = closedPoint A :=
      AffineFiniteResiduePoint.closedFiberPoint_maps_closed p z
    obtain ⟨V, hV, hcV, _⟩ := exists_isAffineOpen_mem_and_subset
      (show c (closedPoint L) ∈ (⊤ : X.Opens) from trivial)
    let B := Γ(X, V)
    let Z := f ⁻¹ᵁ V
    let C := Γ(Y, Z)
    let hZ : IsAffineOpen Z := hV.preimage f
    have hyZ : y ∈ Z := by
      change f y ∈ V
      rw [hy, ← hcimage]
      exact hcV
    let : Nonempty V := ⟨⟨c (closedPoint L), hcV⟩⟩
    let : Nonempty Z := ⟨⟨y, hyZ⟩⟩
    let : Algebra A B := (affineSectionCoefficientMap p V).toAlgebra
    let : Algebra A L := (AffineFiniteResiduePoint.baseScalar p c).toAlgebra
    let : Algebra B C := LocalNormAlgebra.chartAlgebra f V
    let : Algebra.Smooth A B :=
      RingHom.smooth_algebraMap.mp (affineSectionCoefficientMap_smooth p hV)
    let : Module.Finite B C := LocalNormAlgebra.chart_finite f V hV
    let : FaithfulSMul B C := (faithfulSMul_iff_algebraMap_injective B C).mpr
      (LocalNormAlgebra.chartMap_injective f V)
    let : IsDomain B := inferInstance
    let : IsDomain C := inferInstance
    let : IsIntegrallyClosed C := isIntegrallyClosed_sections_of_isAffineOpen Y Z hZ
    obtain ⟨R, hR, hAR, hlocalR, hflatR, hftR, hlocalAR, hm, ε, l,
      _, hlocalL, hεl⟩ := AffineFiniteResiduePoint.exists_local_section p c hcbase hV hcV
    let : CommRing R := hR
    let : Algebra A R := hAR
    let : IsLocalRing R := hlocalR
    let : Module.Flat A R := hflatR
    let : Algebra.EssFiniteType A R := hftR
    let : IsLocalHom (algebraMap A R) := hlocalAR
    let : IsLocalHom l.toRingHom := hlocalL
    have hlpoint : Spec.map (CommRingCat.ofHom l.toRingHom) (closedPoint L) =
        closedPoint R := by
      apply PrimeSpectrum.ext
      exact maximalIdeal_comap l.toRingHom
    have hεtriangle : Spec.map (CommRingCat.ofHom l.toRingHom) ≫
        Spec.map (CommRingCat.ofHom ε.toRingHom) ≫ hV.fromSpec = c := by
      rw [← Category.assoc, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
      have he : l.toRingHom.comp ε.toRingHom =
          (AffineFiniteResiduePoint.pointAlgHom p c hV hcV).toRingHom :=
        congrArg AlgHom.toRingHom hεl
      change Spec.map (CommRingCat.ofHom (l.toRingHom.comp ε.toRingHom)) ≫ _ = _
      rw [he]
      exact affineLocalSectionRetraction_spec c hV hcV
    have hεimage : hV.fromSpec
        (Spec.map (CommRingCat.ofHom ε.toRingHom) (closedPoint R)) = c (closedPoint L) := by
      have he : hV.fromSpec (Spec.map (CommRingCat.ofHom ε.toRingHom)
          (Spec.map (CommRingCat.ofHom l.toRingHom) (closedPoint L))) =
            c (closedPoint L) := congrArg (fun k => k (closedPoint L)) hεtriangle
      exact (congrArg (fun q => hV.fromSpec
        (Spec.map (CommRingCat.ofHom ε.toRingHom) q)) hlpoint).symm.trans he
    have H : hZ.fromSpec ≫ f = Spec.algebraMap B C ≫ hV.fromSpec :=
      (affineFiniteSection_spec f hV).symm
    let : Etale (Spec.algebraMap B C ∣_ (hV.fromSpec ⁻¹ᵁ E)) :=
      etale_restrict_of_preimage_le_etaleSourceOpen _ _ (by
        intro q hq
        apply (etaleAt_iff_of_open_square hZ.fromSpec _ f hV.fromSpec H q).mpr
        apply f.preimage_etaleTargetOpen_le f.isClosedMap
        change f (hZ.fromSpec q) ∈ E
        have he := congrArg (fun k => k q) H
        exact he.symm ▸ hq)
    obtain ⟨q, hq⟩ : ∃ q : Spec (.of C), hZ.fromSpec q = y := by
      have h : y ∈ Set.range hZ.fromSpec := by rw [hZ.range_fromSpec]; exact hyZ
      exact h
    have hqpoint : Spec.algebraMap B C q =
        Spec.map (CommRingCat.ofHom ε.toRingHom) (closedPoint R) := by
      apply hV.fromSpec.isEmbedding.injective
      have he := congrArg (fun k => k q) H
      exact he.symm.trans ((congrArg f hq).trans
        (hy.trans (hcimage.symm.trans hεimage.symm)))
    have het := etaleAt_of_original_flat_local_section A B C R hm p s hs hV.fromSpec
      (affineSectionCoefficientMap_spec p hV).symm E hsE hpE hdim ε
      (by rw [hεimage, hcimage]; exact hzbad) q hqpoint
    have h := (etaleAt_iff_of_open_square hZ.fromSpec _ f hV.fromSpec H q).mp het
    exact hynot (hq ▸ h)
  apply etale_of_forall_etaleAt
  intro y
  exact f.preimage_etaleTargetOpen_le f.isClosedMap (htop (f y))

end AlgebraicGeometry.Scheme.Hom
