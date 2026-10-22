/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Surfaces.Resolution.WeakTransform
public import Aglib.AlgebraicGeometry.Blowup.Integral
public import Aglib.AlgebraicGeometry.IdealSheaf.Artinian
public import Aglib.RingTheory.RegularLocalRing.HeightOnePrincipal
public import Mathlib.AlgebraicGeometry.FunctionField
public import Mathlib.RingTheory.KrullDimension.Field
public import Mathlib.Data.Multiset.DershowitzManna
public import Mathlib.Data.Finset.Filter
public import Mathlib.Data.Finset.Image
public import Aglib.AlgebraicGeometry.IdealSheaf.Cartier.Product
public import Aglib.AlgebraicGeometry.IdealSheaf.Cartier.Restriction
public import Aglib.AlgebraicGeometry.IdealSheaf.Cartier.Avoidance

/-!
# Finite point-blowup chains and their actual local colengths

The chain is built from the original point blowups. Properness and regularity
follow along that finite chain. Actual quotient lengths are transported through
ring and stalk isomorphisms, and the original two parameter charts supply
finite local transform support. The finite nonfree-stalk multiset is defined
from the original ideal. The well-founded multiset recursion constructs a
terminal chain. The original embedded Cartier factors are retained through
the actual composite maps.
-/

@[expose] public section

noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

open CategoryTheory Opposite TopologicalSpace
open CategoryTheory.Limits
open Module

namespace AlgebraicGeometry.Scheme.Blowup

/-- A finite chain of the original constructed blowups at actual closed
points with two-dimensional local rings. All arrows are the original maps. -/
inductive PointBlowupChain : {Y X : Scheme.{u}} → (Y ⟶ X) → Type (u + 1)
  | refl (X : Scheme.{u}) : PointBlowupChain (𝟙 X)
  | cons {X Y : Scheme.{u}} (x : X) (hx : IsClosed ({x} : Set X))
      (hd : ringKrullDim (X.presheaf.stalk x) = 2)
      (g : Y ⟶ (blowupDatum (X.fromSpecResidueField x).ker).Y)
      (tail : PointBlowupChain g) :
      PointBlowupChain (g ≫ (blowupDatum (X.fromSpecResidueField x).ker).map)

/-- The number of actual point blowups in the constructed chain. -/
def PointBlowupChain.length : {Y X : Scheme.{u}} → {f : Y ⟶ X} → PointBlowupChain f → ℕ
  | _, _, _, .refl _ => 0
  | _, _, _, .cons _ _ _ _ tail => tail.length + 1

/-- Every finite chain is proper over a locally Noetherian original scheme. -/
theorem PointBlowupChain.isProper {X Y : Scheme.{u}} {f : Y ⟶ X}
    (c : PointBlowupChain f) : IsLocallyNoetherian X → IsProper f := by
  induction c with
  | refl X => intro _; infer_instance
  | @cons X Y x hx hd g tail ih =>
    intro hN
    let : IsLocallyNoetherian X := hN
    let : IsProper (blowupDatum (X.fromSpecResidueField x).ker).map :=
      (blowupDatum (X.fromSpecResidueField x).ker).isProper_of_isLocallyNoetherian
    let : IsProper g := ih inferInstance
    infer_instance

/-- The original regularity is preserved through the actual finite chain. -/
theorem PointBlowupChain.regularStalks {X Y : Scheme.{u}} {f : Y ⟶ X}
    (c : PointBlowupChain f) :
    IsLocallyNoetherian X → Scheme.RegularStalks X → Scheme.RegularStalks Y := by
  induction c with
  | refl X => exact fun _ hX ↦ hX
  | @cons X Y x hx hd g tail ih =>
    intro hN hX
    let : IsLocallyNoetherian X := hN
    exact ih inferInstance (RegularPoint.regularStalks_pointBlowup X hX x hx hd)

private theorem quotientLength_ringEquiv {R S : Type u} [CommRing R] [CommRing S]
    (e : R ≃+* S) (K : Ideal R) :
    Module.length R (R ⧸ K) = Module.length S (S ⧸ K.map e.toRingHom) := by
  let f : R →ₛₗ[e.toRingHom] S :=
    { __ := e.toAddEquiv.toAddMonoidHom
      map_smul' := e.map_mul }
  let : RingHomSurjective e.toRingHom := ⟨e.surjective⟩
  let F := Submodule.orderIsoMapComapOfBijective f e.bijective
  have hmap : F K = K.map e.toRingHom := by
    change Submodule.map f K = K.map e.toRingHom
    ext y
    rw [Submodule.mem_map, Ideal.mem_map_iff_of_surjective e.toRingHom e.surjective]
    rfl
  rw [Module.length_quotient, Module.length_quotient, ← hmap]
  exact (Order.coheight_orderIso F K).symm

/-- Colength of the actual local quotient by an actual ideal sheaf. -/
def localColength {X : Scheme.{u}} (J : X.IdealSheafData) (x : X) : ℕ∞ :=
  Module.length (X.presheaf.stalk x) (X.presheaf.stalk x ⧸ J.stalkIdeal x)

/-- An isomorphism of the actual stalk maps preserves the original colength. -/
theorem localColength_comap_of_isIso_stalkMap {X Y : Scheme.{u}}
    (J : X.IdealSheafData) (f : Y ⟶ X) (y : Y) [IsIso (f.stalkMap y)] :
    localColength (J.comap f) y = localColength J (f y) := by
  unfold localColength
  rw [IdealSheafData.stalkIdeal_comap]
  exact (quotientLength_ringEquiv (asIso (f.stalkMap y)).commRingCatIsoToRingEquiv
    (J.stalkIdeal (f y))).symm

/-- The actual spectral stalk ideal is extension of the original ring ideal
along the canonical ring-to-stalk homomorphism. -/
theorem stalkIdeal_affineCenter {A : Type u} [CommRing A]
    (J : Ideal A) (x : Spec (.of A)) :
    (affineCenter A J).stalkIdeal x = J.map (StructureSheaf.toStalk A x).hom := by
  calc
    _ = spectrumIdeal (A := (Spec (.of A)).presheaf.stalk x)
        ((affineCenter A J).comap ((Spec (.of A)).fromSpecStalk x)) :=
      (spectrumIdeal_comap_fromSpecStalk (affineCenter A J) x).symm
    _ = spectrumIdeal (A := (Spec (.of A)).presheaf.stalk x)
        ((affineCenter A J).comap (Spec.map (StructureSheaf.toStalk A x))) :=
      congrArg (fun f : Spec ((Spec (.of A)).presheaf.stalk x) ⟶ Spec (.of A) ↦
        spectrumIdeal (A := (Spec (.of A)).presheaf.stalk x) ((affineCenter A J).comap f))
        (AlgebraicGeometry.Spec.fromSpecStalk_eq' (.of A) x)
    _ = spectrumIdeal (A := (Spec (.of A)).presheaf.stalk x)
        (affineCenter ((Spec (.of A)).presheaf.stalk x)
          (J.map (StructureSheaf.toStalk A x).hom)) :=
      congrArg (spectrumIdeal (A := (Spec (.of A)).presheaf.stalk x))
        (BaseChange.affineCenter_comap (StructureSheaf.toStalk A x).hom J)
    _ = _ := spectrumIdeal_affineCenter _

/-- Colength on the actual spectrum is the original ring-localization
colength through the canonical localization equivalence. -/
theorem localColength_affineCenter {A : Type u} [CommRing A]
    (J : Ideal A) (x : Spec (.of A)) :
    localColength (affineCenter A J) x =
      Module.length (Localization.AtPrime x.asIdeal) (Ideal.quotientAtPrime J x.asIdeal) := by
  let S := (Spec (.of A)).presheaf.stalk x
  let : Algebra A S := (StructureSheaf.toStalk A x).hom.toAlgebra
  let : IsLocalization.AtPrime S x.asIdeal := StructureSheaf.IsLocalization.to_stalk A x
  let e := IsLocalization.algEquiv (R := A) x.asIdeal.primeCompl
    (Localization.AtPrime x.asIdeal) S
  have hmap : (J.map (algebraMap A (Localization.AtPrime x.asIdeal))).map e.toRingHom =
      J.map (algebraMap A S) := by
    rw [Ideal.map_map]
    congr 1
    exact e.toAlgHom.comp_algebraMap
  rw [localColength, stalkIdeal_affineCenter]
  change Module.length S (S ⧸ J.map (algebraMap A S)) = _
  rw [← hmap]
  exact (quotientLength_ringEquiv e.toRingEquiv
    (J.map (algebraMap A (Localization.AtPrime x.asIdeal)))).symm

/-- The strict algebraic decrease is a strict decrease of the actual scheme
stalk colength at every point of the original parameter chart. -/
theorem localColength_chart_weakTransform_toNat_lt
    {A : Type u} [CommRing A] [IsNoetherianRing A]
    (a b : A) (ha : IsSMulRegular A a)
    (hb : IsSMulRegular (A ⧸ Ideal.span {a}) b)
    (hmax : (Ideal.span {a, b}).IsMaximal) (J : Ideal A) (r N : ℕ)
    (hr : 0 < r) (hJ : J ≤ (Ideal.span {a, b}) ^ r)
    (hnext : ¬ J ≤ (Ideal.span {a, b}) ^ (r + 1))
    (hN : (Ideal.span {a, b}) ^ N ≤ J) (hrN : r ≤ N)
    (hfin : IsFiniteLength A (A ⧸ J))
    (B : BlowupDatum (affineCenter A (Ideal.span {a, b})))
    (p : Spec (.of (affineBlowupAlgebra A (Ideal.span {a, b}) a))) :
    (localColength (B.weakTransform (affineCenter A J) r)
      ((affineAtlas B).chart ⟨a, Ideal.subset_span (by simp)⟩ p)).toNat <
        (Module.length A (A ⧸ J)).toNat := by
  let ga : Ideal.span {a, b} := ⟨a, Ideal.subset_span (by simp)⟩
  let f := (affineAtlas B).chart ga
  let : IsOpenImmersion f := (affineAtlas B).openImmersion ga
  rw [← localColength_comap_of_isIso_stalkMap _ f p,
    chart_weakTransform_eq_affineCenter, localColength_affineCenter]
  exact Localization.Away.weakTransform_local_colength_toNat_lt a b ha hb hmax J r N
    hr hJ hnext hN hrN hfin p.asIdeal

/-- At every point away from the original centre, the weak ideal is exactly
the original inverse-image ideal in the actual local ring. -/
theorem pointBlowup_stalkIdeal_weakTransform_of_ne
    {X : Scheme.{u}} [IsLocallyNoetherian X]
    (J : X.IdealSheafData) (x : X) (hx : IsClosed ({x} : Set X)) (r : ℕ)
    (y : (blowupDatum (X.fromSpecResidueField x).ker).Y)
    (hy : (blowupDatum (X.fromSpecResidueField x).ker).map y ≠ x) :
    ((blowupDatum (X.fromSpecResidueField x).ker).weakTransform J r).stalkIdeal y =
      (J.stalkIdeal ((blowupDatum (X.fromSpecResidueField x).ker).map y)).map
        ((blowupDatum (X.fromSpecResidueField x).ker).map.stalkMap y).hom := by
  rw [BlowupDatum.stalkIdeal_weakTransform, pointCentre_stalkIdeal_of_ne x hx _ hy,
    Ideal.map_top]
  rw [Ideal.top_pow, Submodule.top_coe, Submodule.colon_univ]

theorem support_affineCenter {A : Type u} [CommRing A] (J : Ideal A) :
    ((affineCenter A J).support : Set (Spec (.of A))) = PrimeSpectrum.zeroLocus (J : Set A) := by
  rw [affineCenter, Scheme.Hom.support_ker]
  change closure (Set.range (PrimeSpectrum.comap (Ideal.Quotient.mk J))) = _
  rw [_root_.range_comap_of_surjective (A ⧸ J) (Ideal.Quotient.mk J)
    Ideal.Quotient.mk_surjective, Ideal.mk_ker]
  exact (PrimeSpectrum.isClosed_zeroLocus _).closure_eq

/-- The genuine weak ideal has finite support on the actual blowup of a
maximal ideal generated by a regular parameter pair. -/
theorem finite_support_weakTransform_of_regular_pair
    {A : Type u} [CommRing A] [IsNoetherianRing A]
    (a b : A) (ha : IsSMulRegular A a)
    (hb : IsSMulRegular (A ⧸ Ideal.span {a}) b)
    (hb' : IsSMulRegular A b) (ha' : IsSMulRegular (A ⧸ Ideal.span {b}) a)
    (hmax : (Ideal.span {a, b}).IsMaximal) (J : Ideal A) (r N : ℕ)
    (hJ : J ≤ (Ideal.span {a, b}) ^ r)
    (hnext : ¬ J ≤ (Ideal.span {a, b}) ^ (r + 1))
    (hN : (Ideal.span {a, b}) ^ N ≤ J) (hrN : r ≤ N)
    (B : BlowupDatum (affineCenter A (Ideal.span {a, b}))) :
    ((B.weakTransform (affineCenter A J) r).support : Set B.Y).Finite := by
  classical
  let I : Ideal A := Ideal.span {a, b}
  let ga : I := ⟨a, Ideal.subset_span (by simp)⟩
  let gb : I := ⟨b, Ideal.subset_span (by simp)⟩
  let fa := (affineAtlas B).chart ga
  let fb := (affineAtlas B).chart gb
  let W := B.weakTransform (affineCenter A J) r
  let g : Bool → I := fun t ↦ if t then gb else ga
  have hg : Ideal.span (Set.range fun t ↦ (g t : A)) = I := by
    have hset : Set.range (fun t ↦ (g t : A)) = {a, b} := by
      ext c
      constructor
      · rintro ⟨t, rfl⟩
        cases t <;> simp [g, ga, gb]
      · intro hc
        rcases (show c = a ∨ c = b by simpa only [Set.mem_insert_iff,
          Set.mem_singleton_iff] using hc) with rfl | rfl
        · exact ⟨false, rfl⟩
        · exact ⟨true, rfl⟩
    rw [hset]
  have hcover (y : B.Y) : y ∈ Set.range fa ∨ y ∈ Set.range fb := by
    obtain ⟨t, ht⟩ := AffineAtlas.generator_covers g hg (affineAtlas B) y
    cases t
    · exact Or.inl ht
    · exact Or.inr ht
  have hprea : fa ⁻¹' (W.support : Set B.Y) =
      PrimeSpectrum.zeroLocus
        (Localization.Away.weakTransform I J a r : Set (affineBlowupAlgebra A I a)) := by
    calc
      _ = ((W.comap fa).support : Set (Spec (.of (affineBlowupAlgebra A I a)))) := by
        rw [IdealSheafData.support_comap]
        rfl
      _ = _ := by
        rw [chart_weakTransform_eq_affineCenter I J B ga r, support_affineCenter]
  have hpreb : fb ⁻¹' (W.support : Set B.Y) =
      PrimeSpectrum.zeroLocus
        (Localization.Away.weakTransform I J b r : Set (affineBlowupAlgebra A I b)) := by
    calc
      _ = ((W.comap fb).support : Set (Spec (.of (affineBlowupAlgebra A I b)))) := by
        rw [IdealSheafData.support_comap]
        rfl
      _ = _ := by
        rw [chart_weakTransform_eq_affineCenter I J B gb r, support_affineCenter]
  have hfina : (fa ⁻¹' (W.support : Set B.Y)).Finite := by
    rw [hprea]
    exact Localization.Away.weakTransform_zeroLocus_finite a b ha hb hmax J r N
      hJ hnext hN hrN
  have hIba : Ideal.span {b, a} = I := Ideal.span_pair_comm
  have hfinb : (fb ⁻¹' (W.support : Set B.Y)).Finite := by
    rw [hpreb]
    have hfinite :=
      Localization.Away.weakTransform_zeroLocus_finite b a hb' ha'
        (by simpa only [hIba] using hmax) J r N
        (by simpa only [hIba] using hJ) (by simpa only [hIba] using hnext)
        (by simpa only [hIba] using hN) hrN
    exact Eq.mp (congrArg (fun K : Ideal A ↦
      (PrimeSpectrum.zeroLocus (Localization.Away.weakTransform K J b r :
        Set (affineBlowupAlgebra A K b))).Finite) hIba) hfinite
  apply ((hfina.image fa).union (hfinb.image fb)).subset
  intro y hy
  rcases hcover y with ⟨p, rfl⟩ | ⟨p, rfl⟩
  · exact Or.inl ⟨p, hy, rfl⟩
  · exact Or.inr ⟨p, hy, rfl⟩


private theorem isPrincipalIdealRing_localization
    {R S : Type u} [CommRing R] [CommRing S] [Algebra R S]
    (M : Submonoid R) [IsLocalization M S] [IsPrincipalIdealRing R] :
    IsPrincipalIdealRing S where
  principal J := by
    rw [← IsLocalization.map_under M S J]
    infer_instance

/-- A regular prime-local ring above an equation with principal-ideal quotient
has dimension at most two. This uses the actual localized quotient. -/
private theorem ringKrullDim_atPrime_le_two_of_principal_quotient
    {R : Type u} [CommRing R] [IsNoetherianRing R]
    (e : R) [IsPrincipalIdealRing (R ⧸ Ideal.span {e})]
    (P : Ideal R) [P.IsPrime] (heP : e ∈ P)
    [IsRegularLocalRing (Localization.AtPrime P)] :
    ringKrullDim (Localization.AtPrime P) ≤ 2 := by
  let S := Localization.AtPrime P
  let K := (Ideal.span {e}).map (algebraMap R S)
  have hK : K = Ideal.span {algebraMap R S e} := by
    simp only [K, Ideal.map_span, Set.image_singleton]
  have hproper : K ≠ ⊤ := by
    apply ne_top_of_le_ne_top (IsLocalRing.maximalIdeal.isMaximal S).ne_top
    rw [hK, Ideal.span_singleton_le_iff_mem, ← Localization.AtPrime.map_eq_maximalIdeal]
    exact Ideal.mem_map_of_mem _ heP
  let : Nontrivial (S ⧸ K) := Ideal.Quotient.nontrivial_iff.mpr hproper
  let : IsLocalRing (S ⧸ K) :=
    IsLocalRing.of_surjective' (Ideal.Quotient.mk K) Ideal.Quotient.mk_surjective
  let : IsPrincipalIdealRing (S ⧸ K) := isPrincipalIdealRing_localization
    (Algebra.algebraMapSubmonoid (R ⧸ Ideal.span {e}) P.primeCompl)
  let : IsLocalRing (S ⧸ Ideal.span {algebraMap R S e}) := by rw [← hK]; infer_instance
  let eK := Ideal.quotEquivOfEq hK
  let : IsPrincipalIdealRing (S ⧸ Ideal.span {algebraMap R S e}) :=
    IsPrincipalIdealRing.of_surjective eK.toRingHom eK.surjective
  have hsmall' : (IsLocalRing.maximalIdeal
      (S ⧸ Ideal.span {algebraMap R S e})).spanFinrank ≤ 1 := by
    obtain ⟨a, ha⟩ := Submodule.IsPrincipal.principal
      (IsLocalRing.maximalIdeal (S ⧸ Ideal.span {algebraMap R S e}))
    rw [ha]
    exact (Submodule.spanFinrank_span_le_ncard_of_finite (Set.finite_singleton a)).trans
      (by simp)
  have hgen := IsLocalRing.spanFinrank_maximalIdeal_le_quotient_add_one S (algebraMap R S e)
  rw [← IsRegularLocalRing.spanFinrank_maximalIdeal]
  exact_mod_cast hgen.trans (Nat.add_le_add_right hsmall' 1)


/-- The actual ideal stalks that do not admit a singleton module basis. -/
def nonfreeIdealStalks {X : Scheme.{u}} (J : X.IdealSheafData) : Set X :=
  {x | ¬ Nonempty (Basis PUnit.{u + 1} (X.presheaf.stalk x) (J.stalkIdeal x))}

/-- Every nonfree ideal stalk belongs to the support of the original quotient. -/
theorem nonfreeIdealStalks_subset_support {X : Scheme.{u}} (J : X.IdealSheafData) :
    nonfreeIdealStalks J ⊆ (J.support : Set X) := by
  intro x hx
  by_contra h
  apply hx
  rw [J.stalkIdeal_eq_top_of_notMem_support x h]
  exact ⟨(Basis.singleton PUnit (X.presheaf.stalk x)).map
    (Submodule.topEquiv : (⊤ : Submodule (X.presheaf.stalk x) (X.presheaf.stalk x))
      ≃ₗ[X.presheaf.stalk x] X.presheaf.stalk x).symm⟩

/-- An actual Artinian quotient has only finitely many nonfree ideal stalks. -/
theorem finite_nonfreeIdealStalks {X : Scheme.{u}} (J : X.IdealSheafData)
    [IsArtinianScheme J.subscheme] : (nonfreeIdealStalks J).Finite :=
  (finite_support_of_isArtinian_subscheme J).subset (nonfreeIdealStalks_subset_support J)

/-- The finite multiset of actual natural local colengths at the nonfree ideal stalks. -/
def nonfreeIdealColengths {X : Scheme.{u}} (J : X.IdealSheafData)
    [IsArtinianScheme J.subscheme] : Multiset ℕ :=
  (finite_nonfreeIdealStalks J).toFinset.val.map fun x ↦ (localColength J x).toNat

/-- With no nonfree actual ideal stalk, the original embedded ideal module is
locally free of rank one. -/
theorem isLocallyRankOne_of_nonfreeIdealStalks_eq_empty
    {X : Scheme.{u}} [IsLocallyNoetherian X] (J : X.IdealSheafData)
    (h : nonfreeIdealStalks J = ∅) :
    Scheme.Modules.Invertible.IsLocallyRankOne X (Scheme.Hom.idealModule J.subschemeι) := by
  apply Scheme.Hom.idealModule_isLocallyRankOne_of_stalkKernelBasis
  intro c
  have hc : J.subschemeι c ∉ nonfreeIdealStalks J := by rw [h]; exact Set.notMem_empty _
  change ¬ ¬ Nonempty (Basis PUnit.{u + 1} (X.presheaf.stalk (J.subschemeι c))
    (J.stalkIdeal (J.subschemeι c))) at hc
  rw [← IdealSheafData.stalkIdeal_subschemeι_eq_ker_stalkMap J c]
  exact not_not.mp hc

/-- A nonzero nonfree ideal stalk in the regular dimension-at-most-two locus
has dimension exactly two. -/
theorem nonfreeIdealStalk_dimension_two {X : Scheme.{u}}
    (hX : Scheme.RegularStalks X) (J : X.IdealSheafData) (x : X)
    (hx : x ∈ nonfreeIdealStalks J) (hJ : J.stalkIdeal x ≠ ⊥)
    (hd : ringKrullDim (X.presheaf.stalk x) ≤ 2) :
    ringKrullDim (X.presheaf.stalk x) = 2 := by
  let R := X.presheaf.stalk x
  let : IsRegularLocalRing R := hX x
  let : IsDomain R := IsRegularLocalRing.isDomain_of_regularLocal R
  have hn : (IsLocalRing.maximalIdeal R).spanFinrank ≤ 2 := by
    exact_mod_cast IsRegularLocalRing.spanFinrank_maximalIdeal.trans_le hd
  by_contra hdim
  have hne : (IsLocalRing.maximalIdeal R).spanFinrank ≠ 2 := by
    intro he
    apply hdim
    rw [← IsRegularLocalRing.spanFinrank_maximalIdeal, he]
    rfl
  have hn' : (IsLocalRing.maximalIdeal R).spanFinrank ≤ 1 := by omega
  let : IsPrincipalIdealRing R :=
    IsRegularLocalRing.isPrincipalIdealRing_of_regularLocal_dimension_le_one R (by
      rw [← IsRegularLocalRing.spanFinrank_maximalIdeal]
      exact_mod_cast hn')
  exact hx ⟨Ideal.principalIdealBasis (J.stalkIdeal x) hJ⟩


/-- Extension from an actual stalk to the original function field gives the
same generic ideal, through the actual specialization map. -/
theorem stalkIdeal_map_functionField {X : Scheme.{u}} [IsIntegral X]
    (J : X.IdealSheafData) (x : X) :
    (J.stalkIdeal x).map (algebraMap (X.presheaf.stalk x) X.functionField) =
      J.stalkIdeal (genericPoint X) := by
  obtain ⟨_, ⟨U, hU, rfl⟩, hxU, -⟩ :=
    X.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ x) isOpen_univ
  let h : genericPoint X ⤳ x := (genericPoint_spec X).specializes trivial
  have hηU : genericPoint X ∈ U := h.mem_open U.isOpen hxU
  rw [J.stalkIdeal_eq_map ⟨U, hU⟩ x hxU,
    J.stalkIdeal_eq_map ⟨U, hU⟩ (genericPoint X) hηU, Ideal.map_map]
  change (J.ideal ⟨U, hU⟩).map
    (X.presheaf.germ U x hxU ≫ X.presheaf.stalkSpecializes h).hom = _
  rw [X.presheaf.germ_stalkSpecializes]

/-- A nonzero original ideal sheaf on an integral scheme has nonzero ideals
in all original stalk rings. -/
theorem stalkIdeal_ne_bot_of_isIntegral {X : Scheme.{u}} [IsIntegral X]
    (J : X.IdealSheafData) (hJ : J ≠ ⊥) (x : X) : J.stalkIdeal x ≠ ⊥ := by
  intro hx
  have hη : J.stalkIdeal (genericPoint X) = ⊥ := by
    rw [← stalkIdeal_map_functionField J x, hx, Ideal.map_bot]
  have hall (y : X) : J.stalkIdeal y = ⊥ :=
    (Ideal.map_eq_bot_iff_of_injective
      (IsFractionRing.injective (X.presheaf.stalk y) X.functionField)).mp
      ((stalkIdeal_map_functionField J y).trans hη)
  apply hJ
  apply IdealSheafData.ext_stalkIdeal
  intro y
  obtain ⟨_, ⟨U, hU, rfl⟩, hyU, -⟩ :=
    X.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ y) isOpen_univ
  rw [hall y, (⊥ : X.IdealSheafData).stalkIdeal_eq_map ⟨U, hU⟩ y hyU]
  exact Ideal.map_bot.symm

/-- A nonzero ideal cannot have a nonfree stalk at the original generic point. -/
theorem nonfreeIdealStalk_ne_genericPoint {X : Scheme.{u}} [IsIntegral X]
    (J : X.IdealSheafData) (hJ : J ≠ ⊥) (x : X)
    (hx : x ∈ nonfreeIdealStalks J) : x ≠ genericPoint X := by
  intro h
  subst x
  let : Field (X.presheaf.stalk (genericPoint X)) := inferInstanceAs (Field X.functionField)
  exact hx ⟨Ideal.principalIdealBasis (J.stalkIdeal (genericPoint X))
    (stalkIdeal_ne_bot_of_isIntegral J hJ (genericPoint X))⟩

/-- Every actual point above the original centre comes from the original
local-spectrum blowup under its canonical comparison map. -/
theorem mem_range_pointBlowupComparison_of_map_eq
    {X : Scheme.{u}} (x : X) (hx : IsClosed ({x} : Set X))
    (y : (blowupDatum (X.fromSpecResidueField x).ker).Y)
    (hy : (blowupDatum (X.fromSpecResidueField x).ker).map y = x) :
    y ∈ Set.range (RegularPoint.stalkBlowupComparison X x hx) := by
  let B := blowupDatum (X.fromSpecResidueField x).ker
  let e := RegularPoint.stalkBlowupIso X x hx
  have hyrange : y ∈ Set.range (pullback.fst B.map (X.fromSpecStalk x)) := by
    rw [Scheme.Pullback.range_fst]
    change B.map y ∈ Set.range (X.fromSpecStalk x)
    rw [hy]
    exact ⟨IsLocalRing.closedPoint (X.presheaf.stalk x), Scheme.fromSpecStalk_closedPoint⟩
  obtain ⟨p, hp⟩ := hyrange
  refine ⟨e.inv p, ?_⟩
  have he := congrArg (fun f ↦ f (e.inv p)) (RegularPoint.stalkBlowupIso_hom_fst X x hx)
  change (pullback.fst B.map (X.fromSpecStalk x)) (e.hom (e.inv p)) =
    (RegularPoint.stalkBlowupComparison X x hx) (e.inv p) at he
  have hep : e.hom (e.inv p) = p := by
    change (e.inv ≫ e.hom) p = p
    rw [e.inv_hom_id]
    rfl
  rw [hep] at he
  exact he.symm.trans hp

/-- The two original saturated charts of any displayed generator pair cover
the actual universal blowup. -/
theorem pairCharts_cover {A : Type u} [CommRing A]
    (I : Ideal A) (a b : A) (hI : Ideal.span {a, b} = I)
    (B : BlowupDatum (affineCenter A I)) (y : B.Y) :
    y ∈ Set.range ((affineAtlas B).chart (RegularPoint.firstGenerator I a b hI)) ∨
      y ∈ Set.range ((affineAtlas B).chart
        (RegularPoint.firstGenerator I b a (Ideal.span_pair_comm.trans hI))) := by
  let ga := RegularPoint.firstGenerator I a b hI
  let gb := RegularPoint.firstGenerator I b a (Ideal.span_pair_comm.trans hI)
  let g : Bool → I := fun t ↦ if t then gb else ga
  have hg : Ideal.span (Set.range fun t ↦ (g t : A)) = I := by
    have hset : Set.range (fun t ↦ (g t : A)) = {a, b} := by
      ext c
      constructor
      · rintro ⟨t, rfl⟩
        cases t <;> simp [g, ga, gb, RegularPoint.firstGenerator]
      · intro hc
        rcases (show c = a ∨ c = b by simpa only [Set.mem_insert_iff,
          Set.mem_singleton_iff] using hc) with rfl | rfl
        · exact ⟨false, rfl⟩
        · exact ⟨true, rfl⟩
    rw [hset, hI]
  obtain ⟨t, ht⟩ := AffineAtlas.generator_covers g hg (affineAtlas B) y
  cases t
  · exact Or.inl ht
  · exact Or.inr ht

/-- The original-chart colength inequality with an explicit equality to the
original centre ideal. -/
theorem localColength_chart_weakTransform_toNat_lt_of_span_eq
    {A : Type u} [CommRing A] [IsNoetherianRing A]
    (I J : Ideal A) (a b : A) (hI : Ideal.span {a, b} = I)
    (ha : IsSMulRegular A a) (hb : IsSMulRegular (A ⧸ Ideal.span {a}) b)
    (hmax : I.IsMaximal) (r N : ℕ) (hr : 0 < r)
    (hJ : J ≤ I ^ r) (hnext : ¬ J ≤ I ^ (r + 1))
    (hN : I ^ N ≤ J) (hrN : r ≤ N) (hfin : IsFiniteLength A (A ⧸ J))
    (B : BlowupDatum (affineCenter A I))
    (p : Spec (.of (affineBlowupAlgebra A I a))) :
    (localColength (B.weakTransform (affineCenter A J) r)
      ((affineAtlas B).chart (RegularPoint.firstGenerator I a b hI) p)).toNat <
        (Module.length A (A ⧸ J)).toNat := by
  subst I
  exact localColength_chart_weakTransform_toNat_lt a b ha hb hmax J r N
    hr hJ hnext hN hrN hfin B p

/-- Every actual local colength on the maximal-ideal blowup strictly decreases
at the original ideal order, using the original two parameter charts. -/
theorem localColength_weakTransform_toNat_lt_of_regular_pair
    {A : Type u} [CommRing A] [IsNoetherianRing A]
    (I J : Ideal A) (a b : A) (hI : Ideal.span {a, b} = I)
    (ha : IsSMulRegular A a) (hb : IsSMulRegular (A ⧸ Ideal.span {a}) b)
    (hb' : IsSMulRegular A b) (ha' : IsSMulRegular (A ⧸ Ideal.span {b}) a)
    (hmax : I.IsMaximal) (r N : ℕ) (hr : 0 < r)
    (hJ : J ≤ I ^ r) (hnext : ¬ J ≤ I ^ (r + 1))
    (hN : I ^ N ≤ J) (hrN : r ≤ N) (hfin : IsFiniteLength A (A ⧸ J))
    (B : BlowupDatum (affineCenter A I)) (y : B.Y) :
    (localColength (B.weakTransform (affineCenter A J) r) y).toNat <
      (Module.length A (A ⧸ J)).toNat := by
  rcases pairCharts_cover I a b hI B y with ⟨p, rfl⟩ | ⟨p, rfl⟩
  · exact localColength_chart_weakTransform_toNat_lt_of_span_eq I J a b hI
      ha hb hmax r N hr hJ hnext hN hrN hfin B p
  · exact localColength_chart_weakTransform_toNat_lt_of_span_eq I J b a
      (Ideal.span_pair_comm.trans hI) hb' ha' hmax r N hr hJ hnext hN hrN hfin B p

/-- The strict decreasing invariant is the actual local colength on the
original global point blowup, at every point over its original centre. -/
theorem localColength_pointWeakTransform_toNat_lt
    {X : Scheme.{u}} [IsLocallyNoetherian X] (J : X.IdealSheafData)
    (x : X) (hx : IsClosed ({x} : Set X)) [IsRegularLocalRing (X.presheaf.stalk x)]
    (hd : ringKrullDim (X.presheaf.stalk x) = 2) (r N : ℕ) (hr : 0 < r)
    (hJ : J.stalkIdeal x ≤ IsLocalRing.maximalIdeal (X.presheaf.stalk x) ^ r)
    (hnext : ¬ J.stalkIdeal x ≤ IsLocalRing.maximalIdeal (X.presheaf.stalk x) ^ (r + 1))
    (hN : IsLocalRing.maximalIdeal (X.presheaf.stalk x) ^ N ≤ J.stalkIdeal x)
    (hrN : r ≤ N)
    (hfin : IsFiniteLength (X.presheaf.stalk x) (X.presheaf.stalk x ⧸ J.stalkIdeal x))
    (y : (blowupDatum (X.fromSpecResidueField x).ker).Y)
    (hy : (blowupDatum (X.fromSpecResidueField x).ker).map y = x) :
    (localColength ((blowupDatum (X.fromSpecResidueField x).ker).weakTransform J r) y).toNat <
      (localColength J x).toNat := by
  obtain ⟨z, rfl⟩ := mem_range_pointBlowupComparison_of_map_eq x hx y hy
  let c := RegularPoint.stalkBlowupComparison X x hx
  let : IsIso (c.stalkMap z) := pointBlowupComparison_isIso_stalkMap x hx z
  rw [← localColength_comap_of_isIso_stalkMap _ c z,
    pointBlowupComparison_comap_weakTransform J x hx r]
  let A := X.presheaf.stalk x
  let a := RegularPoint.firstParameter A hd
  let b := RegularPoint.secondParameter A hd
  obtain ⟨_, _, hm, ha, hb, hb', ha'⟩ := RegularPoint.parameters_spec A hd
  exact localColength_weakTransform_toNat_lt_of_regular_pair
    (IsLocalRing.maximalIdeal A) (J.stalkIdeal x) a b hm ha hb hb' ha' inferInstance
    r N hr hJ hnext hN hrN hfin _ z

/-- Finite support in the two parameter charts, with the literal original
centre ideal retained by its generator equality. -/
theorem finite_support_weakTransform_of_regular_pair_span_eq
    {A : Type u} [CommRing A] [IsNoetherianRing A]
    (I J : Ideal A) (a b : A) (hI : Ideal.span {a, b} = I)
    (ha : IsSMulRegular A a) (hb : IsSMulRegular (A ⧸ Ideal.span {a}) b)
    (hb' : IsSMulRegular A b) (ha' : IsSMulRegular (A ⧸ Ideal.span {b}) a)
    (hmax : I.IsMaximal) (r N : ℕ) (hJ : J ≤ I ^ r)
    (hnext : ¬ J ≤ I ^ (r + 1)) (hN : I ^ N ≤ J) (hrN : r ≤ N)
    (B : BlowupDatum (affineCenter A I)) :
    ((B.weakTransform (affineCenter A J) r).support : Set B.Y).Finite := by
  subst I
  exact finite_support_weakTransform_of_regular_pair a b ha hb hb' ha' hmax J r N
    hJ hnext hN hrN B

/-- Only finitely many points of the genuine global weak quotient lie over
the original blown-up centre. -/
theorem finite_pointWeakTransform_support_fibre
    {X : Scheme.{u}} [IsLocallyNoetherian X] (J : X.IdealSheafData)
    (x : X) (hx : IsClosed ({x} : Set X)) [IsRegularLocalRing (X.presheaf.stalk x)]
    (hd : ringKrullDim (X.presheaf.stalk x) = 2) (r N : ℕ)
    (hJ : J.stalkIdeal x ≤ IsLocalRing.maximalIdeal (X.presheaf.stalk x) ^ r)
    (hnext : ¬ J.stalkIdeal x ≤ IsLocalRing.maximalIdeal (X.presheaf.stalk x) ^ (r + 1))
    (hN : IsLocalRing.maximalIdeal (X.presheaf.stalk x) ^ N ≤ J.stalkIdeal x)
    (hrN : r ≤ N) :
    ((((blowupDatum (X.fromSpecResidueField x).ker).weakTransform J r).support :
        Set (blowupDatum (X.fromSpecResidueField x).ker).Y) ∩
      {y | (blowupDatum (X.fromSpecResidueField x).ker).map y = x}).Finite := by
  let A := X.presheaf.stalk x
  let I := IsLocalRing.maximalIdeal A
  let L := blowupDatum (affineCenter A I)
  let B := blowupDatum (X.fromSpecResidueField x).ker
  let W := B.weakTransform J r
  let V := L.weakTransform (affineCenter A (J.stalkIdeal x)) r
  let c := RegularPoint.stalkBlowupComparison X x hx
  let a := RegularPoint.firstParameter A hd
  let b := RegularPoint.secondParameter A hd
  obtain ⟨_, _, hm, ha, hb, hb', ha'⟩ := RegularPoint.parameters_spec A hd
  have hfinite : (V.support : Set L.Y).Finite :=
    finite_support_weakTransform_of_regular_pair_span_eq I (J.stalkIdeal x) a b hm
      ha hb hb' ha' inferInstance r N hJ hnext hN hrN L
  have hc : W.comap c = V := pointBlowupComparison_comap_weakTransform J x hx r
  apply (hfinite.image c).subset
  rintro y ⟨hyW, hy⟩
  obtain ⟨z, rfl⟩ := mem_range_pointBlowupComparison_of_map_eq x hx y hy
  refine ⟨z, ?_, rfl⟩
  have hz : z ∈ (W.comap c).support := by
    rw [IdealSheafData.support_comap]
    exact hyW
  rwa [hc] at hz

/-- The original blowdown is an isomorphism on actual local rings away from
the original closed point. -/
theorem pointBlowup_stalkMap_isIso_of_ne {X : Scheme.{u}}
    (x : X) (hx : IsClosed ({x} : Set X))
    (y : (blowupDatum (X.fromSpecResidueField x).ker).Y)
    (hy : (blowupDatum (X.fromSpecResidueField x).ker).map y ≠ x) :
    IsIso ((blowupDatum (X.fromSpecResidueField x).ker).map.stalkMap y) := by
  let B := blowupDatum (X.fromSpecResidueField x).ker
  let U : X.Opens := ⟨({x} : Set X)ᶜ, hx.isOpen_compl⟩
  let : IsClosedImmersion (X.fromSpecResidueField x) :=
    isClosed_singleton_iff_isClosedImmersion.mp hx
  have hU : Disjoint (U : Set X) ((X.fromSpecResidueField x).ker.support : Set X) := by
    rw [Scheme.Hom.support_ker, Scheme.range_fromSpecResidueField, hx.closure_eq]
    exact Set.disjoint_left.mpr fun z hz hz' ↦ hz hz'
  let : IsIso (B.map ∣_ U) := B.restrict_isIso_of_disjoint U hU
  let p : (B.map ⁻¹ᵁ U).toScheme := ⟨y, hy⟩
  let e := Scheme.Hom.stalkMapIsoOfIsPullbackOfFlatOfPreimmersion
    (isPullback_morphismRestrict B.map U).flip p y rfl
  exact ((MorphismProperty.isomorphisms CommRingCat).arrow_mk_iso_iff e).mpr inferInstance

/-- The actual point blowdown is injective on the original centre complement. -/
theorem pointBlowup_injOn_complement {X : Scheme.{u}}
    (x : X) (hx : IsClosed ({x} : Set X)) :
    Set.InjOn (blowupDatum (X.fromSpecResidueField x).ker).map
      {y | (blowupDatum (X.fromSpecResidueField x).ker).map y ≠ x} := by
  let B := blowupDatum (X.fromSpecResidueField x).ker
  let U : X.Opens := ⟨({x} : Set X)ᶜ, hx.isOpen_compl⟩
  let : IsClosedImmersion (X.fromSpecResidueField x) :=
    isClosed_singleton_iff_isClosedImmersion.mp hx
  have hU : Disjoint (U : Set X) ((X.fromSpecResidueField x).ker.support : Set X) := by
    rw [Scheme.Hom.support_ker, Scheme.range_fromSpecResidueField, hx.closure_eq]
    exact Set.disjoint_left.mpr fun z hz hz' ↦ hz hz'
  let : IsIso (B.map ∣_ U) := B.restrict_isIso_of_disjoint U hU
  intro y hy z hz h
  have he : (B.map ∣_ U) ⟨y, hy⟩ = (B.map ∣_ U) ⟨z, hz⟩ := by
    apply Subtype.ext
    simpa only [morphismRestrict_base_coe] using h
  exact congrArg Subtype.val ((B.map ∣_ U).isOpenEmbedding.injective he)

/-- The original colength is unchanged at every actual blowup point away
from the centre. -/
theorem localColength_pointWeakTransform_of_ne
    {X : Scheme.{u}} [IsLocallyNoetherian X] (J : X.IdealSheafData)
    (x : X) (hx : IsClosed ({x} : Set X)) (r : ℕ)
    (y : (blowupDatum (X.fromSpecResidueField x).ker).Y)
    (hy : (blowupDatum (X.fromSpecResidueField x).ker).map y ≠ x) :
    localColength ((blowupDatum (X.fromSpecResidueField x).ker).weakTransform J r) y =
      localColength J ((blowupDatum (X.fromSpecResidueField x).ker).map y) := by
  let B := blowupDatum (X.fromSpecResidueField x).ker
  let : IsIso (B.map.stalkMap y) := pointBlowup_stalkMap_isIso_of_ne x hx y hy
  have hst : (B.weakTransform J r).stalkIdeal y = (J.comap B.map).stalkIdeal y := by
    rw [pointBlowup_stalkIdeal_weakTransform_of_ne J x hx r y hy,
      IdealSheafData.stalkIdeal_comap]
  calc
    _ = localColength (J.comap B.map) y :=
      congrArg (fun K : Ideal (B.Y.presheaf.stalk y) ↦
        Module.length (B.Y.presheaf.stalk y) (B.Y.presheaf.stalk y ⧸ K)) hst
    _ = _ := localColength_comap_of_isIso_stalkMap J B.map y

/-- Weak quotient support maps into the original quotient support. -/
theorem weakTransform_support_mapsTo {X : Scheme.{u}} [IsLocallyNoetherian X]
    {I : X.IdealSheafData} (B : BlowupDatum I) (J : X.IdealSheafData) (r : ℕ) :
    Set.MapsTo B.map ((B.weakTransform J r).support : Set B.Y) (J.support : Set X) := by
  have hle : J.comap B.map ≤ B.weakTransform J r := fun _ ↦ Ideal.le_colon
  intro y hy
  have h := IdealSheafData.support_antitone hle hy
  rw [IdealSheafData.support_comap] at h
  exact h

/-- The genuine global weak ideal has finite total support. The original
support away from the centre and the finitely many new fibre points are both actual. -/
theorem finite_support_pointWeakTransform
    {X : Scheme.{u}} [IsLocallyNoetherian X] (J : X.IdealSheafData)
    [IsArtinianScheme J.subscheme] (x : X) (hx : IsClosed ({x} : Set X))
    [IsRegularLocalRing (X.presheaf.stalk x)]
    (hd : ringKrullDim (X.presheaf.stalk x) = 2) (r N : ℕ)
    (hJ : J.stalkIdeal x ≤ IsLocalRing.maximalIdeal (X.presheaf.stalk x) ^ r)
    (hnext : ¬ J.stalkIdeal x ≤ IsLocalRing.maximalIdeal (X.presheaf.stalk x) ^ (r + 1))
    (hN : IsLocalRing.maximalIdeal (X.presheaf.stalk x) ^ N ≤ J.stalkIdeal x)
    (hrN : r ≤ N) :
    (((blowupDatum (X.fromSpecResidueField x).ker).weakTransform J r).support :
      Set (blowupDatum (X.fromSpecResidueField x).ker).Y).Finite := by
  let B := blowupDatum (X.fromSpecResidueField x).ker
  let W := B.weakTransform J r
  have haway : ((W.support : Set B.Y) ∩ {y | B.map y ≠ x}).Finite :=
    Set.Finite.of_injOn
      (fun y hy ↦ weakTransform_support_mapsTo B J r hy.1)
      ((pointBlowup_injOn_complement x hx).mono Set.inter_subset_right)
      (finite_support_of_isArtinian_subscheme J)
  have hfibre := finite_pointWeakTransform_support_fibre J x hx hd r N hJ hnext hN hrN
  apply (haway.union hfibre).subset
  intro y hy
  by_cases h : B.map y = x
  · exact Or.inr ⟨hy, h⟩
  · exact Or.inl ⟨hy, h⟩

private theorem localColength_chart_weakTransform_lt_of_span_eq
    {A : Type u} [CommRing A] [IsNoetherianRing A]
    (I J : Ideal A) (a b : A) (hI : Ideal.span {a, b} = I)
    (ha : IsSMulRegular A a) (hb : IsSMulRegular (A ⧸ Ideal.span {a}) b)
    (hmax : I.IsMaximal) (r N : ℕ) (hr : 0 < r)
    (hJ : J ≤ I ^ r) (hnext : ¬ J ≤ I ^ (r + 1))
    (hN : I ^ N ≤ J) (hrN : r ≤ N) (hfin : IsFiniteLength A (A ⧸ J))
    (B : BlowupDatum (affineCenter A I))
    (p : Spec (.of (affineBlowupAlgebra A I a))) :
    localColength (B.weakTransform (affineCenter A J) r)
      ((affineAtlas B).chart (RegularPoint.firstGenerator I a b hI) p) <
        Module.length A (A ⧸ J) := by
  subst I
  let ga : Ideal.span {a, b} := ⟨a, Ideal.subset_span (by simp)⟩
  let f := (affineAtlas B).chart ga
  let : IsOpenImmersion f := (affineAtlas B).openImmersion ga
  change localColength (B.weakTransform (affineCenter A J) r) (f p) <
    Module.length A (A ⧸ J)
  rw [← localColength_comap_of_isIso_stalkMap _ f p,
    chart_weakTransform_eq_affineCenter, localColength_affineCenter]
  exact Localization.Away.weakTransform_local_colength_lt a b ha hb hmax J r N
    hr hJ hnext hN hrN hfin p.asIdeal

private theorem localColength_weakTransform_lt_of_regular_pair
    {A : Type u} [CommRing A] [IsNoetherianRing A]
    (I J : Ideal A) (a b : A) (hI : Ideal.span {a, b} = I)
    (ha : IsSMulRegular A a) (hb : IsSMulRegular (A ⧸ Ideal.span {a}) b)
    (hb' : IsSMulRegular A b) (ha' : IsSMulRegular (A ⧸ Ideal.span {b}) a)
    (hmax : I.IsMaximal) (r N : ℕ) (hr : 0 < r)
    (hJ : J ≤ I ^ r) (hnext : ¬ J ≤ I ^ (r + 1))
    (hN : I ^ N ≤ J) (hrN : r ≤ N) (hfin : IsFiniteLength A (A ⧸ J))
    (B : BlowupDatum (affineCenter A I)) (y : B.Y) :
    localColength (B.weakTransform (affineCenter A J) r) y < Module.length A (A ⧸ J) := by
  rcases pairCharts_cover I a b hI B y with ⟨p, rfl⟩ | ⟨p, rfl⟩
  · exact localColength_chart_weakTransform_lt_of_span_eq I J a b hI
      ha hb hmax r N hr hJ hnext hN hrN hfin B p
  · exact localColength_chart_weakTransform_lt_of_span_eq I J b a
      (Ideal.span_pair_comm.trans hI) hb' ha' hmax r N hr hJ hnext hN hrN hfin B p

/-- The actual global colength decrease also holds in extended natural lengths,
so in particular the new local quotient has finite length. -/
theorem localColength_pointWeakTransform_lt
    {X : Scheme.{u}} [IsLocallyNoetherian X] (J : X.IdealSheafData)
    (x : X) (hx : IsClosed ({x} : Set X)) [IsRegularLocalRing (X.presheaf.stalk x)]
    (hd : ringKrullDim (X.presheaf.stalk x) = 2) (r N : ℕ) (hr : 0 < r)
    (hJ : J.stalkIdeal x ≤ IsLocalRing.maximalIdeal (X.presheaf.stalk x) ^ r)
    (hnext : ¬ J.stalkIdeal x ≤ IsLocalRing.maximalIdeal (X.presheaf.stalk x) ^ (r + 1))
    (hN : IsLocalRing.maximalIdeal (X.presheaf.stalk x) ^ N ≤ J.stalkIdeal x)
    (hrN : r ≤ N)
    (hfin : IsFiniteLength (X.presheaf.stalk x) (X.presheaf.stalk x ⧸ J.stalkIdeal x))
    (y : (blowupDatum (X.fromSpecResidueField x).ker).Y)
    (hy : (blowupDatum (X.fromSpecResidueField x).ker).map y = x) :
    localColength ((blowupDatum (X.fromSpecResidueField x).ker).weakTransform J r) y <
      localColength J x := by
  obtain ⟨z, rfl⟩ := mem_range_pointBlowupComparison_of_map_eq x hx y hy
  let c := RegularPoint.stalkBlowupComparison X x hx
  let : IsIso (c.stalkMap z) := pointBlowupComparison_isIso_stalkMap x hx z
  rw [← localColength_comap_of_isIso_stalkMap _ c z,
    pointBlowupComparison_comap_weakTransform J x hx r]
  let A := X.presheaf.stalk x
  let a := RegularPoint.firstParameter A hd
  let b := RegularPoint.secondParameter A hd
  obtain ⟨_, _, hm, ha, hb, hb', ha'⟩ := RegularPoint.parameters_spec A hd
  exact localColength_weakTransform_lt_of_regular_pair
    (IsLocalRing.maximalIdeal A) (J.stalkIdeal x) a b hm ha hb hb' ha' inferInstance
    r N hr hJ hnext hN hrN hfin _ z

/-- The new genuine weak quotient is again an actual Artinian closed subscheme. -/
theorem pointWeakTransform_subscheme_isArtinian
    {X : Scheme.{u}} [IsLocallyNoetherian X] (J : X.IdealSheafData)
    [IsArtinianScheme J.subscheme] (x : X) (hx : IsClosed ({x} : Set X))
    [IsRegularLocalRing (X.presheaf.stalk x)]
    (hd : ringKrullDim (X.presheaf.stalk x) = 2) (r N : ℕ) (hr : 0 < r)
    (hJ : J.stalkIdeal x ≤ IsLocalRing.maximalIdeal (X.presheaf.stalk x) ^ r)
    (hnext : ¬ J.stalkIdeal x ≤ IsLocalRing.maximalIdeal (X.presheaf.stalk x) ^ (r + 1))
    (hN : IsLocalRing.maximalIdeal (X.presheaf.stalk x) ^ N ≤ J.stalkIdeal x)
    (hrN : r ≤ N) :
    IsArtinianScheme
      ((blowupDatum (X.fromSpecResidueField x).ker).weakTransform J r).subscheme := by
  apply IdealSheafData.isArtinian_subscheme_of_finite_support_of_stalkQuotient_finiteLength
    _ (finite_support_pointWeakTransform J x hx hd r N hJ hnext hN hrN)
  intro y
  apply Module.length_ne_top_iff.mp
  change localColength ((blowupDatum (X.fromSpecResidueField x).ker).weakTransform J r) y ≠ ⊤
  by_cases hy : (blowupDatum (X.fromSpecResidueField x).ker).map y = x
  · exact ne_top_of_lt (localColength_pointWeakTransform_lt J x hx hd r N hr hJ hnext hN hrN
      (stalkQuotient_finiteLength_of_isLocallyArtinian_subscheme J x) y hy)
  · rw [localColength_pointWeakTransform_of_ne J x hx r y hy]
    exact Module.length_ne_top_iff.mpr
      (stalkQuotient_finiteLength_of_isLocallyArtinian_subscheme J _)


private theorem ne_genericPoint_of_stalk_dimension_two
    {X : Scheme.{u}} [IsIntegral X] (x : X)
    (hd : ringKrullDim (X.presheaf.stalk x) = 2) : x ≠ genericPoint X := by
  intro h
  subst x
  change ringKrullDim X.functionField = 2 at hd
  rw [ringKrullDim_eq_zero_of_field] at hd
  norm_num at hd

/-- Source integrality is constructed along the actual point chain. -/
theorem PointBlowupChain.isIntegral {X Y : Scheme.{u}} {f : Y ⟶ X}
    (c : PointBlowupChain f) : IsIntegral X → IsIntegral Y := by
  induction c with
  | refl X => exact id
  | @cons X Y x hx hd g tail ih =>
    intro hX
    let : IsIntegral X := hX
    exact ih (pointBlowup_isIntegral X x hx (ne_genericPoint_of_stalk_dimension_two x hd))

/-- Every actual point-chain map over an integral scheme is dominant. -/
theorem PointBlowupChain.isDominant {X Y : Scheme.{u}} {f : Y ⟶ X}
    (c : PointBlowupChain f) : IsIntegral X → IsDominant f := by
  induction c with
  | refl X => intro _; infer_instance
  | @cons X Y x hx hd g tail ih =>
    intro hX
    let : IsIntegral X := hX
    have hne := ne_genericPoint_of_stalk_dimension_two x hd
    let : IsIntegral (blowupDatum (X.fromSpecResidueField x).ker).Y :=
      pointBlowup_isIntegral X x hx hne
    let : IsDominant (blowupDatum (X.fromSpecResidueField x).ker).map :=
      pointBlowup_isDominant X x hx hne
    let : IsDominant g := ih inferInstance
    infer_instance

/-- The actual finite point-chain map is birational over the original scheme,
with the dense partial isomorphisms composed over its original structure map. -/
theorem PointBlowupChain.birationalOver {X Y : Scheme.{u}} {f : Y ⟶ X}
    (c : PointBlowupChain f) : IsIntegral X → BirationalOver f (𝟙 X) := by
  induction c with
  | refl X => intro _; exact BirationalOver.refl _
  | @cons X Y x hx hd g tail ih =>
    intro hX
    let : IsIntegral X := hX
    let B := blowupDatum (X.fromSpecResidueField x).ker
    have hne := ne_genericPoint_of_stalk_dimension_two x hd
    let : IsIntegral B.Y := pointBlowup_isIntegral X x hx hne
    obtain ⟨p, hp⟩ := ih inferInstance
    have hp' : p.IsOver (g ≫ B.map) B.map := by
      have h := congrArg (fun f : p.source.toScheme ⟶ B.Y ↦ f ≫ B.map) hp
      simpa only [PartialIso.IsOver, Category.assoc, Category.id_comp] using h
    exact (show BirationalOver (g ≫ B.map) B.map from ⟨p, hp'⟩).trans
      (pointBlowup_birationalOver X x hx hne)

/-- A nonzero ideal on the original integral scheme misses its actual generic point. -/
theorem genericPoint_not_mem_idealSupport_of_ne_bot
    {X : Scheme.{u}} [IsIntegral X] (J : X.IdealSheafData) (hJ : J ≠ ⊥) :
    genericPoint X ∉ (J.support : Set X) := by
  let : Field (X.presheaf.stalk (genericPoint X)) := inferInstanceAs (Field X.functionField)
  obtain ⟨a, ha, hane⟩ := (Submodule.ne_bot_iff (J.stalkIdeal (genericPoint X))).mp
    (stalkIdeal_ne_bot_of_isIntegral J hJ (genericPoint X))
  have htop : J.stalkIdeal (genericPoint X) = ⊤ :=
    (J.stalkIdeal (genericPoint X)).eq_top_of_isUnit_mem ha (isUnit_iff_ne_zero.mpr hane)
  intro h
  exact ((J.stalkIdeal_ne_top_iff_mem_support (genericPoint X)).mpr h) htop

/-- The genuine weak ideal remains nonzero. The proof uses an actual preimage
of the original generic point under the original blowdown. -/
theorem pointWeakTransform_ne_bot {X : Scheme.{u}}
    [IsLocallyNoetherian X] [IsIntegral X] (J : X.IdealSheafData) (hJ : J ≠ ⊥)
    (x : X) (hx : IsClosed ({x} : Set X)) (hne : x ≠ genericPoint X) (r : ℕ) :
    (blowupDatum (X.fromSpecResidueField x).ker).weakTransform J r ≠ ⊥ := by
  let B := blowupDatum (X.fromSpecResidueField x).ker
  obtain ⟨y, hy⟩ := B.mem_range_of_not_mem_support (genericPoint_not_mem_pointCentre x hx hne)
  intro hzero
  have hyW : y ∈ (B.weakTransform J r).support := by
    rw [hzero, IdealSheafData.support_bot]
    trivial
  have hyJ := weakTransform_support_mapsTo B J r hyW
  rw [hy] at hyJ
  exact genericPoint_not_mem_idealSupport_of_ne_bot J hJ hyJ

private theorem ringKrullDim_chart_stalk_le_two_of_over_closedPoint
    {A : Type u} [CommRing A] [IsRegularLocalRing A]
    (I : Ideal A) (a b : A) (hI : Ideal.span {a, b} = I)
    (hm : I = IsLocalRing.maximalIdeal A)
    (ha : IsSMulRegular A a) (hb : IsSMulRegular (A ⧸ Ideal.span {a}) b)
    (B : BlowupDatum (affineCenter A I)) (hB : Scheme.RegularStalks B.Y)
    (p : Spec (.of (affineBlowupAlgebra A I a)))
    (hp : B.map ((affineAtlas B).chart (RegularPoint.firstGenerator I a b hI) p) =
      IsLocalRing.closedPoint A) :
    ringKrullDim (B.Y.presheaf.stalk
      ((affineAtlas B).chart (RegularPoint.firstGenerator I a b hI) p)) ≤ 2 := by
  subst I
  let I : Ideal A := Ideal.span {a, b}
  let C := affineBlowupAlgebra A I a
  let e : C := algebraMap A C a
  let ga : I := ⟨a, Ideal.subset_span (by simp)⟩
  let f := (affineAtlas B).chart ga
  let : IsOpenImmersion f := (affineAtlas B).openImmersion ga
  let : I.IsMaximal := by rw [show I = IsLocalRing.maximalIdeal A from hm]; infer_instance
  let := Ideal.Quotient.field I
  let : IsNoetherianRing C := Localization.Away.pairChart_isNoetherian a b ha hb
  let ef : (C ⧸ Ideal.span {e}) ≃+* Polynomial (A ⧸ I) :=
    (Ideal.quotEquivOfEq
      (Localization.Away.map_center_eq_span I a (Ideal.subset_span (by simp))).symm).trans
      (Localization.Away.pairChartFibreEquiv a b ha hb).toRingEquiv
  let : IsPrincipalIdealRing (C ⧸ Ideal.span {e}) :=
    IsPrincipalIdealRing.of_surjective ef.symm.toRingHom ef.symm.surjective
  let : IsRegularLocalRing (B.Y.presheaf.stalk (f p)) := hB (f p)
  let e1 := (asIso (f.stalkMap p)).commRingCatIsoToRingEquiv
  let : IsRegularLocalRing ((Spec (.of C)).presheaf.stalk p) :=
    IsRegularLocalRing.of_ringEquiv e1
  let e2 := (Spec.stalkIso (.of C) p).commRingCatIsoToRingEquiv
  let : p.asIdeal.IsPrime := p.2
  let : IsRegularLocalRing (Localization.AtPrime p.asIdeal) :=
    IsRegularLocalRing.of_ringEquiv e2
  have ht := congrArg (fun g ↦ g p) ((affineAtlas B).triangle ga)
  change B.map (f p) = PrimeSpectrum.comap (algebraMap A C) p at ht
  have hp' : p.asIdeal.comap (algebraMap A C) = IsLocalRing.maximalIdeal A :=
    congrArg PrimeSpectrum.asIdeal (ht.symm.trans hp)
  have heP : e ∈ p.asIdeal := by
    change a ∈ p.asIdeal.comap (algebraMap A C)
    rw [hp', ← hm]
    exact Ideal.subset_span (by simp)
  have hbound := ringKrullDim_atPrime_le_two_of_principal_quotient e p.asIdeal heP
  change ringKrullDim (B.Y.presheaf.stalk (f p)) ≤ 2
  exact ((ringKrullDim_eq_of_ringEquiv e1).trans
    (ringKrullDim_eq_of_ringEquiv e2)).trans_le hbound

/-- Every original local ring on the maximal-ideal blowup above the closed
point has dimension at most two. -/
theorem regularLocal_pointBlowup_stalk_dimension_le_two
    (A : Type u) [CommRing A] [IsRegularLocalRing A] (hd : ringKrullDim A = 2)
    (y : (blowupDatum (affineCenter A (IsLocalRing.maximalIdeal A))).Y)
    (hy : (blowupDatum (affineCenter A (IsLocalRing.maximalIdeal A))).map y =
      IsLocalRing.closedPoint A) :
    ringKrullDim
      ((blowupDatum (affineCenter A (IsLocalRing.maximalIdeal A))).Y.presheaf.stalk y) ≤ 2 := by
  let I := IsLocalRing.maximalIdeal A
  let B := blowupDatum (affineCenter A I)
  let a := RegularPoint.firstParameter A hd
  let b := RegularPoint.secondParameter A hd
  obtain ⟨_, _, hm, ha, hb, hb', ha'⟩ := RegularPoint.parameters_spec A hd
  have hB : Scheme.RegularStalks B.Y := RegularPoint.regularStalks A hd
  rcases pairCharts_cover I a b hm B y with ⟨p, rfl⟩ | ⟨p, rfl⟩
  · exact ringKrullDim_chart_stalk_le_two_of_over_closedPoint I a b hm rfl ha hb B hB p hy
  · exact ringKrullDim_chart_stalk_le_two_of_over_closedPoint I b a
      (Ideal.span_pair_comm.trans hm) rfl hb' ha' B hB p hy

/-- The dimension-at-most-two bound is retained by the original point blowup
on all actual local rings, including every point of the exceptional fibre. -/
theorem pointBlowup_stalk_dimension_le_two
    {X : Scheme.{u}} (hX : Scheme.RegularStalks X)
    (hD : ∀ z : X, ringKrullDim (X.presheaf.stalk z) ≤ 2)
    (x : X) (hx : IsClosed ({x} : Set X)) (hd : ringKrullDim (X.presheaf.stalk x) = 2)
    (y : (blowupDatum (X.fromSpecResidueField x).ker).Y) :
    ringKrullDim ((blowupDatum (X.fromSpecResidueField x).ker).Y.presheaf.stalk y) ≤ 2 := by
  let B := blowupDatum (X.fromSpecResidueField x).ker
  by_cases hy : B.map y = x
  · obtain ⟨z, rfl⟩ := mem_range_pointBlowupComparison_of_map_eq x hx y hy
    let A := X.presheaf.stalk x
    let : IsRegularLocalRing A := hX x
    let L := blowupDatum (affineCenter A (IsLocalRing.maximalIdeal A))
    let c := RegularPoint.stalkBlowupComparison X x hx
    have hsq := congrArg (fun f ↦ f z)
      (RegularPoint.stalkBlowupComparison_isPullback X x hx).w
    change B.map (c z) = X.fromSpecStalk x (L.map z) at hsq
    have hbase : L.map z = IsLocalRing.closedPoint A :=
      (X.fromSpecStalk x).isEmbedding.injective
        ((hsq.symm.trans hy).trans Scheme.fromSpecStalk_closedPoint.symm)
    let : IsIso (c.stalkMap z) := pointBlowupComparison_isIso_stalkMap x hx z
    exact (ringKrullDim_eq_of_ringEquiv
      (asIso (c.stalkMap z)).commRingCatIsoToRingEquiv).trans_le
        (regularLocal_pointBlowup_stalk_dimension_le_two A hd z hbase)
  · let : IsIso (B.map.stalkMap y) := pointBlowup_stalkMap_isIso_of_ne x hx y hy
    exact (ringKrullDim_eq_of_ringEquiv
      (asIso (B.map.stalkMap y)).commRingCatIsoToRingEquiv.symm).trans_le (hD (B.map y))

/-- The dimension bound is retained by every actual finite chain. -/
theorem PointBlowupChain.stalk_dimension_le_two {X Y : Scheme.{u}} {f : Y ⟶ X}
    (c : PointBlowupChain f) : IsLocallyNoetherian X → Scheme.RegularStalks X →
    (∀ x : X, ringKrullDim (X.presheaf.stalk x) ≤ 2) →
    ∀ y : Y, ringKrullDim (Y.presheaf.stalk y) ≤ 2 := by
  induction c with
  | refl X => exact fun _ _ hD ↦ hD
  | @cons X Y x hx hd g tail ih =>
    intro hN hX hD
    let : IsLocallyNoetherian X := hN
    exact ih inferInstance (RegularPoint.regularStalks_pointBlowup X hX x hx hd)
      (pointBlowup_stalk_dimension_le_two hX hD x hx hd)

private theorem nonempty_singletonBasis_map_ringEquiv
    {R S : Type u} [CommRing R] [CommRing S] (e : R ≃+* S) (I : Ideal R) :
    Nonempty (Basis PUnit.{u + 1} R I) →
      Nonempty (Basis PUnit.{u + 1} S (I.map e.toRingHom)) := by
  rintro ⟨b⟩
  obtain ⟨a, ha, hI⟩ := Ideal.ideal_exists_regular_generator I
    (b.repr.trans (Basis.singleton PUnit.{u + 1} R).repr.symm)
  have hreg : IsSMulRegular S (e a) := by
    intro v w hvw
    apply e.symm.injective
    apply ha
    apply e.injective
    simpa only [smul_eq_mul, map_mul, e.apply_symm_apply] using hvw
  have hmap : I.map e.toRingHom = Ideal.span {e a} := by
    rw [hI, Ideal.map_span, Set.image_singleton]
    rfl
  exact ⟨Ideal.regularPrincipalIdealBasis _ (e a) hreg hmap⟩

private theorem nonempty_singletonBasis_map_ringEquiv_iff
    {R S : Type u} [CommRing R] [CommRing S] (e : R ≃+* S) (I : Ideal R) :
    Nonempty (Basis PUnit.{u + 1} R I) ↔
      Nonempty (Basis PUnit.{u + 1} S (I.map e.toRingHom)) := by
  refine ⟨nonempty_singletonBasis_map_ringEquiv e I, fun h ↦ ?_⟩
  have h' := nonempty_singletonBasis_map_ringEquiv e.symm (I.map e.toRingHom) h
  have hc : e.symm.toRingHom.comp e.toRingHom = RingHom.id R := by
    ext r
    exact e.symm_apply_apply r
  have hI : (I.map e.toRingHom).map e.symm.toRingHom = I := by
    rw [Ideal.map_map, hc, Ideal.map_id]
  exact Eq.mp (congrArg (fun K : Ideal R ↦ Nonempty (Basis PUnit.{u + 1} R K)) hI) h'

/-- The original nonfree-ideal-stalk condition is unchanged away from the
centre, through the original blowdown's actual local ring isomorphism. -/
theorem mem_nonfreeIdealStalks_pointWeakTransform_iff_of_ne
    {X : Scheme.{u}} [IsLocallyNoetherian X] (J : X.IdealSheafData)
    (x : X) (hx : IsClosed ({x} : Set X)) (r : ℕ)
    (y : (blowupDatum (X.fromSpecResidueField x).ker).Y)
    (hy : (blowupDatum (X.fromSpecResidueField x).ker).map y ≠ x) :
    y ∈ nonfreeIdealStalks ((blowupDatum (X.fromSpecResidueField x).ker).weakTransform J r) ↔
      (blowupDatum (X.fromSpecResidueField x).ker).map y ∈ nonfreeIdealStalks J := by
  let B := blowupDatum (X.fromSpecResidueField x).ker
  let R := X.presheaf.stalk (B.map y)
  let S := B.Y.presheaf.stalk y
  let : IsIso (B.map.stalkMap y) := pointBlowup_stalkMap_isIso_of_ne x hx y hy
  let e := (asIso (B.map.stalkMap y)).commRingCatIsoToRingEquiv
  have hst := pointBlowup_stalkIdeal_weakTransform_of_ne J x hx r y hy
  have hb : Nonempty (Basis PUnit.{u + 1} S ((B.weakTransform J r).stalkIdeal y)) ↔
      Nonempty (Basis PUnit.{u + 1} R (J.stalkIdeal (B.map y))) :=
    (Eq.to_iff (congrArg (fun K : Ideal S ↦ Nonempty (Basis PUnit.{u + 1} S K)) hst)).trans
      (nonempty_singletonBasis_map_ringEquiv_iff e (J.stalkIdeal (B.map y))).symm
  exact not_congr hb

/-- Every original bad point distinct from the centre has an actual bad
preimage under the same point blowdown. -/
theorem exists_nonfreeIdealStalk_pointWeakTransform_over_ne
    {X : Scheme.{u}} [IsLocallyNoetherian X] (J : X.IdealSheafData)
    (x : X) (hx : IsClosed ({x} : Set X)) (r : ℕ) (z : X)
    (hz : z ∈ nonfreeIdealStalks J) (hzx : z ≠ x) :
    ∃ y : (blowupDatum (X.fromSpecResidueField x).ker).Y,
      (blowupDatum (X.fromSpecResidueField x).ker).map y = z ∧
      y ∈ nonfreeIdealStalks ((blowupDatum (X.fromSpecResidueField x).ker).weakTransform J r) := by
  let B := blowupDatum (X.fromSpecResidueField x).ker
  let : IsClosedImmersion (X.fromSpecResidueField x) :=
    isClosed_singleton_iff_isClosedImmersion.mp hx
  have hzcentre : z ∉ ((X.fromSpecResidueField x).ker.support : Set X) := by
    rw [Scheme.Hom.support_ker, Scheme.range_fromSpecResidueField, hx.closure_eq]
    exact hzx
  obtain ⟨y, hy⟩ := B.mem_range_of_not_mem_support hzcentre
  refine ⟨y, hy, ?_⟩
  exact (mem_nonfreeIdealStalks_pointWeakTransform_iff_of_ne J x hx r y
    (by rwa [hy])).mpr (by rwa [hy])

/-- The actual bad-point colength multiset decreases: the centre entry is
replaced by the finitely many strictly smaller actual fibre entries. -/
theorem nonfreeIdealColengths_pointWeakTransform_lt
    {X : Scheme.{u}} [IsLocallyNoetherian X] (J : X.IdealSheafData)
    [IsArtinianScheme J.subscheme] (x : X) (hx : IsClosed ({x} : Set X))
    (hbad : x ∈ nonfreeIdealStalks J) [IsRegularLocalRing (X.presheaf.stalk x)]
    (hd : ringKrullDim (X.presheaf.stalk x) = 2) (r N : ℕ) (hr : 0 < r)
    (hJ : J.stalkIdeal x ≤ IsLocalRing.maximalIdeal (X.presheaf.stalk x) ^ r)
    (hnext : ¬ J.stalkIdeal x ≤ IsLocalRing.maximalIdeal (X.presheaf.stalk x) ^ (r + 1))
    (hN : IsLocalRing.maximalIdeal (X.presheaf.stalk x) ^ N ≤ J.stalkIdeal x)
    (hrN : r ≤ N) :
    letI : IsArtinianScheme
        ((blowupDatum (X.fromSpecResidueField x).ker).weakTransform J r).subscheme :=
      pointWeakTransform_subscheme_isArtinian J x hx hd r N hr hJ hnext hN hrN
    Multiset.IsDershowitzMannaLT
      (nonfreeIdealColengths ((blowupDatum (X.fromSpecResidueField x).ker).weakTransform J r))
      (nonfreeIdealColengths J) := by
  classical
  let B := blowupDatum (X.fromSpecResidueField x).ker
  let W := B.weakTransform J r
  let : IsArtinianScheme W.subscheme :=
    pointWeakTransform_subscheme_isArtinian J x hx hd r N hr hJ hnext hN hrN
  let S := (finite_nonfreeIdealStalks J).toFinset
  let T := (finite_nonfreeIdealStalks W).toFinset
  let SA := T.filter fun y ↦ B.map y ≠ x
  let SF := T.filter fun y ↦ B.map y = x
  let O := S.erase x
  let wX := fun z : X ↦ (localColength J z).toNat
  let wY := fun y : B.Y ↦ (localColength W y).toNat
  let common := O.val.map wX
  let children := SF.val.map wY
  have hxS : x ∈ S := by simpa only [S, Set.Finite.mem_toFinset] using hbad
  have himage : SA.image B.map = O := by
    apply Finset.ext
    intro z
    constructor
    · intro hz
      obtain ⟨y, hy, hyp⟩ := Finset.mem_image.mp hz
      obtain ⟨hyT, hyx⟩ := Finset.mem_filter.mp hy
      have hybad : y ∈ nonfreeIdealStalks W := by
        simpa only [T, Set.Finite.mem_toFinset] using hyT
      have hzbad :=
        (mem_nonfreeIdealStalks_pointWeakTransform_iff_of_ne J x hx r y hyx).mp hybad
      apply Finset.mem_erase.mpr
      exact ⟨by simpa only [hyp] using hyx,
        by simpa only [S, Set.Finite.mem_toFinset] using hyp ▸ hzbad⟩
    · intro hz
      obtain ⟨hzx, hzS⟩ := Finset.mem_erase.mp hz
      have hzbad : z ∈ nonfreeIdealStalks J := by
        simpa only [S, Set.Finite.mem_toFinset] using hzS
      obtain ⟨y, hyp, hybad⟩ :=
        exists_nonfreeIdealStalk_pointWeakTransform_over_ne J x hx r z hzbad hzx
      apply Finset.mem_image.mpr
      refine ⟨y, Finset.mem_filter.mpr ⟨?_, ?_⟩, hyp⟩
      · simpa only [T, Set.Finite.mem_toFinset] using hybad
      · rwa [hyp]
  have hinj : Set.InjOn B.map (SA : Set B.Y) :=
    (pointBlowup_injOn_complement x hx).mono fun y hy ↦ (Finset.mem_filter.mp hy).2
  have himageVal : O.val = SA.val.map B.map :=
    (congrArg Finset.val himage).symm.trans (Finset.image_val_of_injOn hinj)
  have houtside : SA.val.map wY = O.val.map wX := by
    rw [himageVal, Multiset.map_map]
    apply Multiset.map_congr rfl
    intro y hy
    exact congrArg ENat.toNat
      (localColength_pointWeakTransform_of_ne J x hx r y (Finset.mem_filter.mp hy).2)
  have hpartition : SA.val + SF.val = T.val := by
    simpa only [SA, SF, Finset.filter_val, not_not] using
      Multiset.filter_add_not (p := fun y : B.Y ↦ B.map y ≠ x) T.val
  have hnew : nonfreeIdealColengths W = common + children := by
    change T.val.map wY = common + children
    calc
      _ = (SA.val + SF.val).map wY := congrArg (Multiset.map wY) hpartition.symm
      _ = SA.val.map wY + SF.val.map wY := Multiset.map_add _ _ _
      _ = common + children := congrArg (fun m : Multiset ℕ ↦ m + children) houtside
  have hold : nonfreeIdealColengths J = common + {wX x} := by
    change S.val.map wX = common + {wX x}
    calc
      _ = (x ::ₘ S.val.erase x).map wX :=
        congrArg (Multiset.map wX) (Multiset.cons_erase hxS).symm
      _ = {wX x} + O.val.map wX := by
        simp only [O, Finset.erase_val, Multiset.map_cons, Multiset.singleton_add]
      _ = common + {wX x} := add_comm _ _
  refine ⟨common, children, {wX x}, by simp, hnew, hold, ?_⟩
  intro n hn
  obtain ⟨y, hy, rfl⟩ := Multiset.mem_map.mp hn
  refine ⟨wX x, by simp, ?_⟩
  exact localColength_pointWeakTransform_toNat_lt J x hx hd r N hr hJ hnext hN hrN
    (stalkQuotient_finiteLength_of_isLocallyArtinian_subscheme J x) y
    (Finset.mem_filter.mp hy).2

open Scheme.Modules Scheme.Modules.Invertible Scheme.Hom

private theorem ideal_mul_locallyRankOne {X : Scheme.{u}} (I J : X.IdealSheafData)
    (hI : IsLocallyRankOne X (idealModule I.subschemeι))
    (hJ : IsLocallyRankOne X (idealModule J.subschemeι)) :
    IsLocallyRankOne X (idealModule (I * J).subschemeι) := by
  have ht := tensorSheaf_locallyRankOne X (idealModule I.subschemeι) (idealModule J.subschemeι)
    hI hJ
  have hp := isLocallyRankOne_of_iso X
    (idealProductIso I.subschemeι J.subschemeι hI) ht
  have he : I.subschemeι.ker * J.subschemeι.ker = I * J :=
    congrArg₂ (fun K L : X.IdealSheafData ↦ K * L) I.ker_subschemeι J.ker_subschemeι
  exact Eq.mp (congrArg (fun K : X.IdealSheafData ↦
    IsLocallyRankOne X (idealModule K.subschemeι)) he) hp

private theorem ideal_pow_locallyRankOne {X : Scheme.{u}} (I : X.IdealSheafData) (n : ℕ)
    (hI : IsLocallyRankOne X (idealModule I.subschemeι)) :
    IsLocallyRankOne X (idealModule (I ^ n).subschemeι) := by
  induction n with
  | zero =>
    have he : I ^ 0 = (⊤ : X.IdealSheafData) := by
      rw [pow_zero, IdealSheafData.one_eq_top]
    exact Eq.mpr (congrArg (fun K : X.IdealSheafData ↦
      IsLocallyRankOne X (idealModule K.subschemeι)) he) (idealModule_top_rankOne X)
  | succ n ih =>
    rw [pow_succ]
    exact ideal_mul_locallyRankOne (I ^ n) I ih hI

/-- The already proved canonical Cartier avoidance map, transported through
the original source isomorphism to the native inverse-image ideal subscheme. -/
private theorem ideal_comap_locallyRankOne_of_integral_avoidance
    {X Y : Scheme.{u}} [IsIntegral Y] (I : X.IdealSheafData) (f : Y ⟶ X)
    (hI : IsLocallyRankOne X (idealModule I.subschemeι))
    (havoid : ¬ Set.range f ⊆ Set.range I.subschemeι) :
    IsLocallyRankOne Y (idealModule (I.comap f).subschemeι) := by
  have hPB := Cartier.cartierRestriction_invertible Cartier.integralAvoidanceCartierPullback
    I.subschemeι f hI havoid
  let e := I.comapIso f ≪≫ pullbackSymmetry f I.subschemeι
  have he : e.hom ≫ pullback.snd I.subschemeι f = (I.comap f).subschemeι := by
    simp only [e, Iso.trans_hom, Category.assoc, pullbackSymmetry_hom_comp_snd,
      IdealSheafData.comapIso_hom_fst]
  have hi := isLocallyRankOne_of_iso Y (idealSourceIso e (pullback.snd I.subschemeι f)) hPB
  rw [he] at hi
  exact hi

/-- Principalizing the genuine weak ideal along an actual later point chain
principalizes the original ideal. The exceptional factor is pulled back as an
embedded Cartier ideal by the actual avoidance map. -/
theorem cartierPullback_of_pointWeakTransform
    {X Y : Scheme.{u}} [IsLocallyNoetherian X] [IsIntegral X]
    (J : X.IdealSheafData) (x : X) (hx : IsClosed ({x} : Set X))
    (hne : x ≠ genericPoint X) (r : ℕ) (hJ : J ≤ (X.fromSpecResidueField x).ker ^ r)
    (g : Y ⟶ (blowupDatum (X.fromSpecResidueField x).ker).Y)
    (c : PointBlowupChain g)
    (hW : cartierPullback ((blowupDatum (X.fromSpecResidueField x).ker).weakTransform J r) g) :
    cartierPullback J (g ≫ (blowupDatum (X.fromSpecResidueField x).ker).map) := by
  let B := blowupDatum (X.fromSpecResidueField x).ker
  let E := (X.fromSpecResidueField x).ker.comap B.map
  let W := B.weakTransform J r
  let : IsIntegral B.Y := pointBlowup_isIntegral X x hx hne
  let : IsDominant B.map := pointBlowup_isDominant X x hx hne
  let : IsIntegral Y := c.isIntegral inferInstance
  let : IsDominant g := c.isDominant inferInstance
  have hE : IsLocallyRankOne B.Y (idealModule E.subschemeι) := B.cartier
  have hη : genericPoint B.Y ∉ (E.support : Set B.Y) := by
    change genericPoint B.Y ∉
      (((X.fromSpecResidueField x).ker.comap B.map).support : Set B.Y)
    rw [IdealSheafData.support_comap]
    change B.map (genericPoint B.Y) ∉ ((X.fromSpecResidueField x).ker.support : Set X)
    rw [Scheme.map_genericPoint_of_isDominant B.Y B.map]
    exact genericPoint_not_mem_pointCentre x hx hne
  have havoid : ¬ Set.range g ⊆ Set.range E.subschemeι := by
    intro h
    have hηE := h (show g (genericPoint Y) ∈ Set.range g from Set.mem_range_self _)
    rw [E.range_subschemeι, Scheme.map_genericPoint_of_isDominant Y g] at hηE
    exact hη hηE
  have hEg := ideal_comap_locallyRankOne_of_integral_avoidance E g hE havoid
  have hprod : IsLocallyRankOne Y
      (idealModule ((E.comap g) ^ r * W.comap g).subschemeι) :=
    ideal_mul_locallyRankOne ((E.comap g) ^ r) (W.comap g)
      (ideal_pow_locallyRankOne (E.comap g) r hEg) hW
  have hfac : E ^ r * W = J.comap B.map := B.exceptional_pow_mul_weakTransform J r hJ
  have hfacg : (E.comap g) ^ r * W.comap g = J.comap (g ≫ B.map) := by
    calc
      _ = (E ^ r * W).comap g := by rw [IdealSheafData.comap_mul, IdealSheafData.comap_pow]
      _ = (J.comap B.map).comap g := congrArg (fun K ↦ K.comap g) hfac
      _ = _ := (IdealSheafData.comap_comp J g B.map).symm
  exact Eq.mp (congrArg (fun K : Y.IdealSheafData ↦
    IsLocallyRankOne Y (idealModule K.subschemeι)) hfacg) hprod

/-- A genuine finite-colength ideal on a regular integral surface is
principalized by a finite chain of the original point blowups. -/
theorem exists_pointBlowupChain_cartierPullback
    {X : Scheme.{u}} [IsLocallyNoetherian X] [IsIntegral X]
    (hX : Scheme.RegularStalks X)
    (hD : ∀ x : X, ringKrullDim (X.presheaf.stalk x) ≤ 2)
    (J : X.IdealSheafData) (hJ : J ≠ ⊥) [IsArtinianScheme J.subscheme] :
    ∃ (Y : Scheme.{u}) (f : Y ⟶ X), Nonempty (PointBlowupChain f) ∧ cartierPullback J f := by
  classical
  have hmain : ∀ m : Multiset ℕ,
      ∀ (Z : Scheme.{u}) [IsLocallyNoetherian Z] [IsIntegral Z]
        (K : Z.IdealSheafData) [IsArtinianScheme K.subscheme],
        K ≠ ⊥ → Scheme.RegularStalks Z →
        (∀ z : Z, ringKrullDim (Z.presheaf.stalk z) ≤ 2) →
        nonfreeIdealColengths K = m →
        ∃ (T : Scheme.{u}) (f : T ⟶ Z),
          Nonempty (PointBlowupChain f) ∧ cartierPullback K f := by
    intro m
    induction m using (Multiset.wellFounded_isDershowitzMannaLT (α := ℕ)).induction with
    | h m ih =>
      intro Z _ _ K _ hK hZ hDim hm
      by_cases hempty : nonfreeIdealStalks K = ∅
      · refine ⟨Z, 𝟙 Z, ⟨PointBlowupChain.refl Z⟩, ?_⟩
        change IsLocallyRankOne Z (idealModule (K.comap (𝟙 Z)).subschemeι)
        rw [IdealSheafData.comap_id]
        exact isLocallyRankOne_of_nonfreeIdealStalks_eq_empty K hempty
      · obtain ⟨x, hbad⟩ := Set.nonempty_iff_ne_empty.mpr hempty
        have hxS := nonfreeIdealStalks_subset_support K hbad
        have hx := isClosed_singleton_of_mem_support_of_isArtinian_subscheme K x hxS
        have hne := nonfreeIdealStalk_ne_genericPoint K hK x hbad
        let A := Z.presheaf.stalk x
        let : IsRegularLocalRing A := hZ x
        have hd : ringKrullDim A = 2 := nonfreeIdealStalk_dimension_two hZ K x hbad
          (stalkIdeal_ne_bot_of_isIntegral K hK x) (hDim x)
        have hproper : K.stalkIdeal x ≠ ⊤ := (K.stalkIdeal_ne_top_iff_mem_support x).mpr hxS
        let : IsArtinianRing (A ⧸ K.stalkIdeal x) :=
          stalkQuotient_isArtinian_of_isLocallyArtinian_subscheme K x
        obtain ⟨N, hN⟩ :=
          IsLocalRing.exists_maximalIdeal_pow_le_of_isArtinianRing_quotient (K.stalkIdeal x)
        obtain ⟨a, b, _, _, hab, ha, hb, _, _⟩ := IsRegularLocalRing.exists_regularPair A hd
        have habproper : Ideal.span {a, b} ≠ ⊤ := by
          rw [hab]
          exact (inferInstance : (IsLocalRing.maximalIdeal A).IsMaximal).ne_top
        obtain ⟨r, hr, hrN, hKr, hnext⟩ := Ideal.exists_positive_parameter_order a b ha hb
          habproper (K.stalkIdeal x)
          (by simpa only [hab] using hN)
          (by simpa only [hab] using IsLocalRing.le_maximalIdeal hproper)
        have hKr' : K.stalkIdeal x ≤ IsLocalRing.maximalIdeal A ^ r := by
          simpa only [hab] using hKr
        have hnext' : ¬ K.stalkIdeal x ≤ IsLocalRing.maximalIdeal A ^ (r + 1) := by
          simpa only [hab] using hnext
        let B := blowupDatum (Z.fromSpecResidueField x).ker
        let W := B.weakTransform K r
        let : IsArtinianScheme W.subscheme :=
          pointWeakTransform_subscheme_isArtinian K x hx hd r N hr hKr' hnext' hN hrN
        let : IsIntegral B.Y := pointBlowup_isIntegral Z x hx hne
        have hW : W ≠ ⊥ := pointWeakTransform_ne_bot K hK x hx hne r
        have hB : Scheme.RegularStalks B.Y :=
          RegularPoint.regularStalks_pointBlowup Z hZ x hx hd
        have hBD : ∀ y : B.Y, ringKrullDim (B.Y.presheaf.stalk y) ≤ 2 :=
          pointBlowup_stalk_dimension_le_two hZ hDim x hx hd
        have hlt : Multiset.IsDershowitzMannaLT (nonfreeIdealColengths W) m := by
          rw [← hm]
          exact nonfreeIdealColengths_pointWeakTransform_lt K x hx hbad hd r N hr
            hKr' hnext' hN hrN
        obtain ⟨T, g, ⟨tail⟩, hg⟩ :=
          ih (nonfreeIdealColengths W) hlt B.Y W hW hB hBD rfl
        refine ⟨T, g ≫ B.map, ⟨PointBlowupChain.cons x hx hd g tail⟩, ?_⟩
        exact cartierPullback_of_pointWeakTransform K x hx hne r
          ((le_pointCentre_pow_iff K x hx r).mpr hKr') g tail hg
  exact hmain (nonfreeIdealColengths J) X J hJ hX hD rfl

/-- Finite point principalization retains the actual proper birational map,
integral regular source and the local dimension bound. -/
theorem exists_regular_pointBlowup_principalization
    {X : Scheme.{u}} [IsLocallyNoetherian X] [IsIntegral X]
    (hX : Scheme.RegularStalks X)
    (hD : ∀ x : X, ringKrullDim (X.presheaf.stalk x) ≤ 2)
    (J : X.IdealSheafData) (hJ : J ≠ ⊥) [IsArtinianScheme J.subscheme] :
    ∃ (Y : Scheme.{u}) (f : Y ⟶ X), Nonempty (PointBlowupChain f) ∧ IsProper f ∧
      IsDominant f ∧ BirationalOver f (𝟙 X) ∧ IsIntegral Y ∧ Scheme.RegularStalks Y ∧
      (∀ y : Y, ringKrullDim (Y.presheaf.stalk y) ≤ 2) ∧ cartierPullback J f := by
  obtain ⟨Y, f, ⟨c⟩, hf⟩ := exists_pointBlowupChain_cartierPullback hX hD J hJ
  exact ⟨Y, f, ⟨c⟩, c.isProper inferInstance, c.isDominant inferInstance,
    c.birationalOver inferInstance, c.isIntegral inferInstance, c.regularStalks inferInstance hX,
    c.stalk_dimension_le_two inferInstance hX hD, hf⟩

/-- The native scheme-dimension interface for finite point principalization. -/
theorem exists_regular_pointBlowup_principalization_of_dimension_le_two
    {X : Scheme.{u}} [IsLocallyNoetherian X] [IsIntegral X]
    (hX : Scheme.RegularStalks X) (hd : topologicalKrullDim X ≤ 2)
    (J : X.IdealSheafData) (hJ : J ≠ ⊥) [IsArtinianScheme J.subscheme] :
    ∃ (Y : Scheme.{u}) (f : Y ⟶ X), Nonempty (PointBlowupChain f) ∧ IsProper f ∧
      IsDominant f ∧ BirationalOver f (𝟙 X) ∧ IsIntegral Y ∧ Scheme.RegularStalks Y ∧
      (∀ y : Y, ringKrullDim (Y.presheaf.stalk y) ≤ 2) ∧ cartierPullback J f := by
  apply exists_regular_pointBlowup_principalization hX _ J hJ
  rw [Scheme.topologicalKrullDim_eq_iSup_stalk] at hd
  intro x
  exact (le_iSup (fun z : X ↦ ringKrullDim (X.presheaf.stalk z)) x).trans hd

end AlgebraicGeometry.Scheme.Blowup
