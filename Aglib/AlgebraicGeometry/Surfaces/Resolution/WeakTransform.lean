/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.IdealSheaf.Colon
public import Aglib.AlgebraicGeometry.IdealSheaf.Invertible.Affine
public import Aglib.AlgebraicGeometry.Blowup.RegularPoint.Scheme
public import Aglib.AlgebraicGeometry.Blowup.Properness
public import Aglib.RingTheory.Blowup.Colength
public import Mathlib.AlgebraicGeometry.Artinian
public import Mathlib.RingTheory.LocalRing.Quotient

/-!
# The genuine weak ideal on the actual blowup

The quotient of the original inverse-image ideal by a power of the actual
exceptional Cartier ideal defines a native ideal sheaf. Its affine and stalk
equations identify it with division in the literal saturated blowup charts.
The Cartier factorization holds when the original ideal is contained in the
chosen power of the centre.
-/

@[expose] public section

noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

open CategoryTheory Opposite TopologicalSpace

namespace AlgebraicGeometry.Scheme.Blowup

variable {X : Scheme.{u}} [IsLocallyNoetherian X] {I : X.IdealSheafData}

/-- The actual universal blowup over a locally Noetherian scheme is locally
Noetherian, by its proved properness. -/
instance BlowupDatum.isLocallyNoetherian (B : BlowupDatum I) : IsLocallyNoetherian B.Y := by
  let : IsProper B.map := B.isProper_of_isLocallyNoetherian
  exact LocallyOfFiniteType.isLocallyNoetherian B.map

/-- Division by a power of the actual exceptional ideal on the original
universal blowup. The exponent is explicit; later order lemmas choose it from
the original local ideal. -/
def BlowupDatum.weakTransform (B : BlowupDatum I) (J : X.IdealSheafData) (r : ℕ) :
    B.Y.IdealSheafData :=
  (J.comap B.map).colon ((I.comap B.map) ^ r)

/-- On every affine open the global weak ideal is the ordinary quotient of
the original section ideals. -/
theorem BlowupDatum.weakTransform_ideal (B : BlowupDatum I) (J : X.IdealSheafData)
    (r : ℕ) (U : B.Y.affineOpens) :
    (B.weakTransform J r).ideal U =
      ((J.comap B.map).ideal U).colon
        ((((I.comap B.map).ideal U) ^ r : Ideal Γ(B.Y, U)) : Set Γ(B.Y, U)) := rfl

/-- The same quotient holds in each actual blowup local ring. -/
theorem BlowupDatum.stalkIdeal_weakTransform (B : BlowupDatum I)
    (J : X.IdealSheafData) (r : ℕ) (y : B.Y) :
    (B.weakTransform J r).stalkIdeal y =
      ((J.stalkIdeal (B.map y)).map (B.map.stalkMap y).hom).colon
        (((I.stalkIdeal (B.map y)).map (B.map.stalkMap y).hom) ^ r : Set _) := by
  rw [weakTransform, IdealSheafData.stalkIdeal_colon, IdealSheafData.stalkIdeal_pow,
    IdealSheafData.stalkIdeal_comap, IdealSheafData.stalkIdeal_comap]

/-- Division by the actual Cartier power recovers the full inverse-image
ideal, with no radical or saturation in the equation. -/
theorem BlowupDatum.exceptional_pow_mul_weakTransform (B : BlowupDatum I)
    (J : X.IdealSheafData) (r : ℕ) (hJ : J ≤ I ^ r) :
    (I.comap B.map) ^ r * B.weakTransform J r = J.comap B.map := by
  apply IdealSheafData.ext_stalkIdeal
  intro y
  let E := I.comap B.map
  let L := J.comap B.map
  have hL : L ≤ E ^ r := by
    change J.comap B.map ≤ (I.comap B.map) ^ r
    rw [← IdealSheafData.comap_pow]
    exact IdealSheafData.comap_mono B.map hJ
  obtain ⟨U, hU, hyU, a, ha, he⟩ :=
    Scheme.Hom.exists_affine_regular_idealGenerator_of_isLocallyRankOne
      E.subschemeι B.cartier y
  rw [E.ker_subschemeι_app ⟨U, hU⟩] at he
  have he' : E.stalkIdeal y =
      Ideal.span {(B.Y.presheaf.germ U y hyU).hom a} := by
    rw [E.stalkIdeal_eq_map ⟨U, hU⟩ y hyU, he, Ideal.map_span, Set.image_singleton]
  change (E ^ r * L.colon (E ^ r)).stalkIdeal y = L.stalkIdeal y
  rw [IdealSheafData.stalkIdeal_mul, IdealSheafData.stalkIdeal_colon,
    IdealSheafData.stalkIdeal_pow, he', Ideal.span_singleton_pow]
  apply Ideal.span_singleton_mul_colon_of_le
  have h := IdealSheafData.le_iff_stalkIdeal_le.mp hL y
  simpa only [IdealSheafData.stalkIdeal_pow, he', Ideal.span_singleton_pow] using h

/-- Base change with isomorphic actual stalk maps retains the original weak
ideal quotient and exponent. -/
theorem BlowupDatum.comap_weakTransform_of_isIso_stalkMap
    {T : Scheme.{u}} [IsLocallyNoetherian T]
    (B : BlowupDatum I) (J : X.IdealSheafData) (r : ℕ)
    (f : T ⟶ B.Y) (hf : ∀ t, IsIso (f.stalkMap t)) :
    (B.weakTransform J r).comap f =
      (J.comap (f ≫ B.map)).colon ((I.comap (f ≫ B.map)) ^ r) := by
  rw [weakTransform, IdealSheafData.comap_colon_of_isIso_stalkMap _ _ f hf,
    IdealSheafData.comap_pow, ← IdealSheafData.comap_comp, ← IdealSheafData.comap_comp]

/-- Restricting the genuine weak ideal to any actual open chart retains its
original inverse-image ideals and exponent. -/
theorem BlowupDatum.comap_weakTransform {T : Scheme.{u}} [IsLocallyNoetherian T]
    (B : BlowupDatum I) (J : X.IdealSheafData) (r : ℕ)
    (f : T ⟶ B.Y) [IsOpenImmersion f] :
    (B.weakTransform J r).comap f =
      (J.comap (f ≫ B.map)).colon ((I.comap (f ≫ B.map)) ^ r) :=
  B.comap_weakTransform_of_isIso_stalkMap J r f fun _ ↦ inferInstance

section Spectrum

variable {A : Type u} [CommRing A]

/-- The spectral ideal correspondence returns the original ring ideal. -/
theorem spectrumIdeal_affineCenter (J : Ideal A) :
    spectrumIdeal (affineCenter A J) = J := by
  rw [spectrumIdeal, affineCenter, IdealSheafData.specMap_kernel_top, Ideal.mk_ker]
  exact Ideal.map_comap_of_surjective _
    (ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso (.of A)).hom).surjective _

/-- The spectral ideal correspondence preserves powers. -/
theorem spectrumIdeal_pow (J : (Spec (.of A)).IdealSheafData) (r : ℕ) :
    spectrumIdeal (J ^ r) = spectrumIdeal J ^ r :=
  Ideal.map_pow _ _ _

/-- The spectral ideal correspondence preserves the ordinary ideal quotient. -/
theorem spectrumIdeal_colon [IsNoetherianRing A]
    (J K : (Spec (.of A)).IdealSheafData) :
    spectrumIdeal (J.colon K) = (spectrumIdeal J).colon (spectrumIdeal K : Set A) :=
  Ideal.map_colon_of_bijective (Scheme.ΓSpecIso (.of A)).hom.hom
    (ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso (.of A)).hom) _ _

variable [IsNoetherianRing A] (I J : Ideal A)
  (B : BlowupDatum (affineCenter A I)) (a : I) (r : ℕ)

/-- On every original saturated chart, the genuine global weak ideal has
exactly the ring ideal defined by division by the actual exceptional parameter. -/
theorem spectrumIdeal_chart_weakTransform :
    spectrumIdeal ((B.weakTransform (affineCenter A J) r).comap ((affineAtlas B).chart a)) =
      Localization.Away.weakTransform I J a r := by
  let C := affineBlowupAlgebra A I a
  let f := (affineAtlas B).chart a
  let : IsOpenImmersion f := (affineAtlas B).openImmersion a
  let : IsLocallyNoetherian (Spec (.of C)) := isLocallyNoetherian_of_isOpenImmersion f
  let : IsNoetherianRing C := (isLocallyNoetherian_Spec (R := .of C)).mp inferInstance
  rw [B.comap_weakTransform (affineCenter A J) r f,
    (affineAtlas B).triangle, affineChartMap,
    BaseChange.affineCenter_comap, BaseChange.affineCenter_comap,
    spectrumIdeal_colon, spectrumIdeal_pow, spectrumIdeal_affineCenter,
    spectrumIdeal_affineCenter,
    Localization.Away.map_center_eq_span I (a : A) a.property,
    Ideal.span_singleton_pow, Ideal.colon_span]
  rfl

/-- The chart identification is an equality of the actual ideal sheaves, not
only a statement about their supports or quotient lengths. -/
theorem chart_weakTransform_eq_affineCenter :
    (B.weakTransform (affineCenter A J) r).comap ((affineAtlas B).chart a) =
      affineCenter (affineBlowupAlgebra A I a) (Localization.Away.weakTransform I J a r) := by
  rw [← spectrumIdeal_chart_weakTransform I J B a r, affineCenter_spectrumIdeal]

end Spectrum

omit [IsLocallyNoetherian X] in
/-- Extension to the original local spectrum recovers the actual stalk ideal,
through the canonical global-sections isomorphism of that spectrum. -/
theorem spectrumIdeal_comap_fromSpecStalk (J : X.IdealSheafData) (x : X) :
    spectrumIdeal (J.comap (X.fromSpecStalk x)) = J.stalkIdeal x := by
  obtain ⟨_, ⟨U, hU, rfl⟩, hxU, -⟩ :=
    X.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ x) isOpen_univ
  have hpre : (⊤ : (Spec (X.presheaf.stalk x)).Opens) ≤ (X.fromSpecStalk x) ⁻¹ᵁ U := by
    intro z _
    exact (Scheme.range_fromSpecStalk.le ⟨z, rfl⟩).mem_open U.isOpen hxU
  have happ : (X.fromSpecStalk x).appLE U ⊤ hpre ≫
      (Scheme.ΓSpecIso (X.presheaf.stalk x)).hom = X.presheaf.germ U x hxU := by
    rw [Scheme.Hom.appLE, Scheme.fromSpecStalk_app hxU]
    have hcomp : (homOfLE (show (X.fromSpecStalk x) ⁻¹ᵁ U ≤ ⊤ from le_top)).op ≫
        (homOfLE hpre).op = 𝟙 (op (⊤ : (Spec (X.presheaf.stalk x)).Opens)) :=
      Subsingleton.elim _ _
    simp only [Category.assoc, ← Functor.map_comp, hcomp]
    rw [CategoryTheory.Functor.map_id, Category.id_comp, Iso.inv_hom_id, Category.comp_id]
  calc
    spectrumIdeal (J.comap (X.fromSpecStalk x)) =
        ((J.comap (X.fromSpecStalk x)).ideal ⟨⊤, isAffineOpen_top _⟩).map
          (Scheme.ΓSpecIso (X.presheaf.stalk x)).hom.hom := rfl
    _ = ((J.ideal ⟨U, hU⟩).map ((X.fromSpecStalk x).appLE U ⊤ hpre).hom).map
          (Scheme.ΓSpecIso (X.presheaf.stalk x)).hom.hom :=
      congrArg (fun K ↦ K.map (Scheme.ΓSpecIso (X.presheaf.stalk x)).hom.hom)
        (J.ideal_comap_eq_map_appLE (X.fromSpecStalk x)
          ⟨U, hU⟩ ⟨⊤, isAffineOpen_top _⟩ hpre)
    _ = (J.ideal ⟨U, hU⟩).map (((X.fromSpecStalk x).appLE U ⊤ hpre) ≫
          (Scheme.ΓSpecIso (X.presheaf.stalk x)).hom).hom := Ideal.map_map _ _
    _ = (J.ideal ⟨U, hU⟩).map (X.presheaf.germ U x hxU).hom :=
      congrArg (fun φ : Γ(X, U) ⟶ X.presheaf.stalk x ↦ (J.ideal ⟨U, hU⟩).map φ.hom) happ
    _ = J.stalkIdeal x := (J.stalkIdeal_eq_map ⟨U, hU⟩ x hxU).symm

omit [IsLocallyNoetherian X] in
/-- The actual closed-point centre has the original maximal ideal as its
stalk at the centre. -/
theorem pointCentre_stalkIdeal (x : X) (hx : IsClosed ({x} : Set X)) :
    (X.fromSpecResidueField x).ker.stalkIdeal x =
      IsLocalRing.maximalIdeal (X.presheaf.stalk x) := by
  calc
    _ = spectrumIdeal (A := X.presheaf.stalk x)
        ((X.fromSpecResidueField x).ker.comap (X.fromSpecStalk x)) :=
      (spectrumIdeal_comap_fromSpecStalk (X.fromSpecResidueField x).ker x).symm
    _ = spectrumIdeal (A := X.presheaf.stalk x)
        (affineCenter (X.presheaf.stalk x) (IsLocalRing.maximalIdeal (X.presheaf.stalk x))) :=
      congrArg (spectrumIdeal (A := X.presheaf.stalk x))
        (RegularPoint.pointCentre_comap_fromSpecStalk X x hx)
    _ = _ := spectrumIdeal_affineCenter _

omit [IsLocallyNoetherian X] in
/-- The actual point-blowup comparison induces isomorphisms of the original
local rings at every point of the local-spectrum blowup. -/
theorem pointBlowupComparison_isIso_stalkMap (x : X) (hx : IsClosed ({x} : Set X))
    (y : (blowupDatum (affineCenter (X.presheaf.stalk x)
      (IsLocalRing.maximalIdeal (X.presheaf.stalk x)))).Y) :
    IsIso ((RegularPoint.stalkBlowupComparison X x hx).stalkMap y) := by
  let : Flat (X.fromSpecStalk x) := Scheme.fromSpecStalk_flat X x
  let : Flat (RegularPoint.stalkBlowupComparison X x hx) :=
    MorphismProperty.of_isPullback (RegularPoint.stalkBlowupComparison_isPullback X x hx).flip
      (inferInstance : Flat (X.fromSpecStalk x))
  let : IsPreimmersion (RegularPoint.stalkBlowupComparison X x hx) :=
    MorphismProperty.of_isPullback (RegularPoint.stalkBlowupComparison_isPullback X x hx).flip
      (inferInstance : IsPreimmersion (X.fromSpecStalk x))
  exact Scheme.Hom.isIso_stalkMap_of_flat_of_surjectiveOnStalks _ y

/-- The global weak ideal restricts along the actual point-blowup comparison
to the weak ideal of the original maximal ideal and original stalk ideal. -/
theorem pointBlowupComparison_comap_weakTransform
    (J : X.IdealSheafData) (x : X) (hx : IsClosed ({x} : Set X)) (r : ℕ) :
    ((blowupDatum (X.fromSpecResidueField x).ker).weakTransform J r).comap
        (RegularPoint.stalkBlowupComparison X x hx) =
      (blowupDatum (affineCenter (X.presheaf.stalk x)
        (IsLocalRing.maximalIdeal (X.presheaf.stalk x)))).weakTransform
          (affineCenter (X.presheaf.stalk x) (J.stalkIdeal x)) r := by
  rw [BlowupDatum.comap_weakTransform_of_isIso_stalkMap _ J r _
    (pointBlowupComparison_isIso_stalkMap x hx),
    (RegularPoint.stalkBlowupComparison_isPullback X x hx).w,
    IdealSheafData.comap_comp, IdealSheafData.comap_comp,
    RegularPoint.pointCentre_comap_fromSpecStalk X x hx]
  have hJ : J.comap (X.fromSpecStalk x) =
      affineCenter (X.presheaf.stalk x) (J.stalkIdeal x) := by
    rw [← spectrumIdeal_comap_fromSpecStalk J x, affineCenter_spectrumIdeal]
  rw [hJ]
  rfl

omit [IsLocallyNoetherian X] in
/-- Away from the original closed point, its actual centre ideal is the unit
ideal in the original stalk ring. -/
theorem pointCentre_stalkIdeal_of_ne (x : X) (hx : IsClosed ({x} : Set X))
    (y : X) (hy : y ≠ x) :
    (X.fromSpecResidueField x).ker.stalkIdeal y = ⊤ := by
  let : IsClosedImmersion (X.fromSpecResidueField x) :=
    isClosed_singleton_iff_isClosedImmersion.mp hx
  apply IdealSheafData.stalkIdeal_eq_top_of_notMem_support
  change y ∉ ((X.fromSpecResidueField x).ker.support : Set X)
  rw [Scheme.Hom.support_ker, Scheme.range_fromSpecResidueField, hx.closure_eq]
  exact hy

omit [IsLocallyNoetherian X] in
/-- Containment in a power of the actual closed-point ideal is completely
determined in the original local ring at that point. -/
theorem le_pointCentre_pow_iff (J : X.IdealSheafData) (x : X)
    (hx : IsClosed ({x} : Set X)) (r : ℕ) :
    J ≤ (X.fromSpecResidueField x).ker ^ r ↔
      J.stalkIdeal x ≤ IsLocalRing.maximalIdeal (X.presheaf.stalk x) ^ r := by
  rw [IdealSheafData.le_iff_stalkIdeal_le]
  constructor
  · intro h
    simpa only [IdealSheafData.stalkIdeal_pow, pointCentre_stalkIdeal x hx] using h x
  · intro h y
    by_cases hy : y = x
    · subst y
      simpa only [IdealSheafData.stalkIdeal_pow, pointCentre_stalkIdeal x hx] using h
    · rw [IdealSheafData.stalkIdeal_pow, pointCentre_stalkIdeal_of_ne x hx y hy]
      rw [Ideal.top_pow]
      exact le_top

omit [IsLocallyNoetherian X] in
/-- A proper finite-colength original stalk ideal at a two-dimensional regular
point has a positive actual order in the global closed-point ideal. -/
theorem exists_positive_pointCentre_order (J : X.IdealSheafData) (x : X)
    (hx : IsClosed ({x} : Set X)) [IsRegularLocalRing (X.presheaf.stalk x)]
    (hd : ringKrullDim (X.presheaf.stalk x) = 2)
    (hproper : J.stalkIdeal x ≠ ⊤)
    (hfin : IsFiniteLength (X.presheaf.stalk x)
      (X.presheaf.stalk x ⧸ J.stalkIdeal x)) :
    ∃ r : ℕ, 0 < r ∧ J ≤ (X.fromSpecResidueField x).ker ^ r ∧
      ¬ J ≤ (X.fromSpecResidueField x).ker ^ (r + 1) := by
  let A := X.presheaf.stalk x
  let K := J.stalkIdeal x
  let : IsArtinian A (A ⧸ K) :=
    (isFiniteLength_iff_isNoetherian_isArtinian.mp hfin).2
  let : IsArtinianRing (A ⧸ K) := isArtinian_of_tower A inferInstance
  obtain ⟨N, hN⟩ := IsLocalRing.exists_maximalIdeal_pow_le_of_isArtinianRing_quotient K
  let a := RegularPoint.firstParameter A hd
  let b := RegularPoint.secondParameter A hd
  obtain ⟨_, _, hm, ha, hb, _, _⟩ := RegularPoint.parameters_spec A hd
  change Ideal.span {a, b} = IsLocalRing.maximalIdeal A at hm
  have hne : Ideal.span {a, b} ≠ ⊤ := by
    rw [hm]
    exact (inferInstance : (IsLocalRing.maximalIdeal A).IsMaximal).ne_top
  have hN' : (Ideal.span {a, b}) ^ N ≤ K := by simpa only [hm] using hN
  have hK' : K ≤ Ideal.span {a, b} := by
    simpa only [hm] using IsLocalRing.le_maximalIdeal hproper
  obtain ⟨r, hr, _, hKr, hKn⟩ := Ideal.exists_positive_parameter_order a b ha hb
    hne K hN' hK'
  refine ⟨r, hr, (le_pointCentre_pow_iff J x hx r).mpr ?_, ?_⟩
  · simpa only [hm] using hKr
  · intro h
    exact hKn (by simpa only [hm] using (le_pointCentre_pow_iff J x hx (r + 1)).mp h)

omit [IsLocallyNoetherian X] in
/-- An actual Artinian closed subscheme gives finite support of its original
quotient ideal sheaf. -/
theorem finite_support_of_isArtinian_subscheme (J : X.IdealSheafData)
    [IsArtinianScheme J.subscheme] : (J.support : Set X).Finite := by
  rw [← J.range_subschemeι]
  exact Set.finite_range J.subschemeι

omit [IsLocallyNoetherian X] in
/-- Every point of the support of an actual Artinian closed subscheme is
closed in the original ambient scheme. -/
theorem isClosed_singleton_of_mem_support_of_isArtinian_subscheme
    (J : X.IdealSheafData) [IsArtinianScheme J.subscheme]
    (x : X) (hx : x ∈ J.support) : IsClosed ({x} : Set X) := by
  change x ∈ (J.support : Set X) at hx
  rw [← J.range_subschemeι] at hx
  obtain ⟨z, rfl⟩ := hx
  simpa only [Set.image_singleton] using
    J.subschemeι.isClosedEmbedding.isClosedMap _ (isClosed_discrete ({z} : Set J.subscheme))

omit [IsLocallyNoetherian X] in
/-- A locally Artinian actual closed subscheme gives an Artinian quotient of
every original ambient stalk by its original ideal. -/
theorem stalkQuotient_isArtinian_of_isLocallyArtinian_subscheme
    (J : X.IdealSheafData) [IsLocallyArtinian J.subscheme] (x : X) :
    IsArtinianRing (X.presheaf.stalk x ⧸ J.stalkIdeal x) := by
  obtain ⟨_, ⟨U, hU, rfl⟩, hxU, -⟩ :=
    X.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ x) isOpen_univ
  let A := Γ(X, U)
  let S := X.presheaf.stalk x
  let K := J.ideal ⟨U, hU⟩
  let P := (hU.primeIdealOf ⟨x, hxU⟩).asIdeal
  let : Algebra A S := X.presheaf.algebra_section_stalk ⟨x, hxU⟩
  have : IsLocalization.AtPrime S P := hU.isLocalization_stalk ⟨x, hxU⟩
  have : IsArtinianRing Γ(J.subscheme, J.subschemeι ⁻¹ᵁ U) :=
    IsLocallyArtinian.isArtinianRing_presheaf_obj ⟨_, hU.preimage J.subschemeι⟩
  let : IsArtinianRing (A ⧸ K) :=
    (J.subschemeObjIso ⟨U, hU⟩).commRingCatIsoToRingEquiv.isArtinianRing
  rw [J.stalkIdeal_eq_map ⟨U, hU⟩ x hxU]
  exact IsArtinianRing.localization_artinian
    (Algebra.algebraMapSubmonoid (A ⧸ K) P.primeCompl)
    (S ⧸ K.map (algebraMap A S))

/-- The finite local colength comes from the original Artinian quotient
subscheme; it is not an additional transform datum. -/
theorem stalkQuotient_finiteLength_of_isLocallyArtinian_subscheme
    (J : X.IdealSheafData) [IsLocallyArtinian J.subscheme] (x : X) :
    IsFiniteLength (X.presheaf.stalk x) (X.presheaf.stalk x ⧸ J.stalkIdeal x) := by
  let S := X.presheaf.stalk x
  let Q := S ⧸ J.stalkIdeal x
  let : IsArtinianRing Q := stalkQuotient_isArtinian_of_isLocallyArtinian_subscheme J x
  let : IsArtinian S Q := isArtinian_of_surjective_algebraMap
    (R := Q) (S := S) (M := Q) Ideal.Quotient.mk_surjective
  exact isFiniteLength_iff_isNoetherian_isArtinian.mpr ⟨inferInstance, inferInstance⟩

end AlgebraicGeometry.Scheme.Blowup
