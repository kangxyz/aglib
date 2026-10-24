/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Surfaces.Birational.NormalizedBlowupCover.Nagata
public import Aglib.AlgebraicGeometry.Surfaces.Birational.ChowDomination
public import Aglib.AlgebraicGeometry.ProjectiveSpace.FromSections.FieldSpan
public import Aglib.AlgebraicGeometry.ProjectiveSpace.FromSections.Naturality
public import Aglib.AlgebraicGeometry.Modules.Invertible.FieldMaps
public import Aglib.AlgebraicGeometry.Modules.Locality.Sections
public import Aglib.AlgebraicGeometry.Modules.Pullback.UnitMultiplication
public import Aglib.AlgebraicGeometry.IdealSheaf.Artinian
public import Aglib.AlgebraicGeometry.IdealSheaf.Invertible.StalkKernel
public import Aglib.AlgebraicGeometry.Blowup.AffineLiftingCover
public import Aglib.RingTheory.Polynomial.CoefficientProducts
public import Mathlib.Algebra.Polynomial.OfFn
public import Mathlib.LinearAlgebra.Finsupp.LinearCombination
public import Mathlib.RingTheory.Localization.Integer

/-!
# Finite domination through original projective coordinates

An actual coefficient-ideal frame makes the original projective row locally
principal, by the same-field coefficient-product theorem. The actual row
ideal, its original kernel-lift sections, and their affine generation give
native section frames and a projective morphism. Original generic coordinates
and the closed Chow embedding retain the required structural triangles.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open AlgebraicGeometry.Scheme.Modules AlgebraicGeometry.Scheme.Modules.Invertible
open AlgebraicGeometry.Scheme.Blowup

universe u

attribute [local instance] MvPolynomial.gradedAlgebra

namespace AlgebraicGeometry.Scheme.Birational.FiniteDomination

private abbrev unitModule (X : Scheme.{u}) : X.Modules :=
  SheafOfModules.unit X.ringCatSheaf

private theorem contentIdeal_C_mul {R : Type u} [CommRing R]
    (t : R) (F : Polynomial R) :
    (Polynomial.C t * F).contentIdeal = Ideal.span ({t} : Set R) * F.contentIdeal := by
  apply le_antisymm
  · simpa only [Polynomial.contentIdeal_C] using
      (Polynomial.C t).contentIdeal_mul_le_mul_contentIdeal F
  · apply Ideal.span_singleton_mul_le_iff.mpr
    intro x hx
    rw [Polynomial.contentIdeal_def] at hx
    induction hx using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨n, _, rfl⟩ := Polynomial.mem_coeffs_iff.mp hx
      simpa only [Polynomial.coeff_C_mul] using
        (Polynomial.C t * F).coeff_mem_contentIdeal n
    | zero => simpa only [mul_zero] using (Polynomial.C t * F).contentIdeal.zero_mem
    | add x y _ _ hx hy =>
      simpa only [mul_add] using (Polynomial.C t * F).contentIdeal.add_mem hx hy
    | smul c x _ hx =>
      change t * (c * x) ∈ (Polynomial.C t * F).contentIdeal
      rw [mul_left_comm]
      exact (Polynomial.C t * F).contentIdeal.mul_mem_left c hx

private theorem exists_primitive_factor {R : Type u} [CommRing R] [IsDomain R]
    (F : Polynomial R) (t : R) (ht : t ≠ 0)
    (hF : F.contentIdeal = Ideal.span ({t} : Set R)) :
    ∃ G : Polynomial R, F = Polynomial.C t * G ∧ G.contentIdeal = ⊤ := by
  have hdiv : Polynomial.C t ∣ F := by
    apply (Polynomial.C_dvd_iff_dvd_coeff t F).mpr
    intro n
    apply Ideal.mem_span_singleton.mp
    rw [← hF]
    exact F.coeff_mem_contentIdeal n
  obtain ⟨G, hG⟩ := hdiv
  refine ⟨G, hG, ?_⟩
  have he := congrArg Polynomial.contentIdeal hG
  rw [hF, contentIdeal_C_mul] at he
  apply (Ideal.span_singleton_mul_right_inj (I := G.contentIdeal) (J := ⊤) ht).mp
  simpa only [Ideal.mul_top] using he.symm

private theorem row_generator_of_content_frame
    {R K : Type u} [CommRing R] [IsDomain R] [IsLocalRing R] [IsIntegrallyClosed R]
    [Field K] [Algebra R K] [IsFractionRing R K]
    (p Q F : Polynomial R) (hF : F = p * Q)
    (t : R) (ht : t ≠ 0) (hcontent : F.contentIdeal = Ideal.span ({t} : Set R)) :
    ∃ i : ℕ, p.coeff i ≠ 0 ∧
      p.contentIdeal = Ideal.span ({p.coeff i} : Set R) := by
  obtain ⟨G, hG, hGc⟩ := exists_primitive_factor F t ht hcontent
  let scalarMap := algebraMap R K
  have htK : scalarMap t ≠ 0 := by
    intro hz
    apply ht
    apply IsFractionRing.injective R K
    change scalarMap t = scalarMap 0
    simpa only [map_zero] using hz
  let q : Polynomial K := Polynomial.C (scalarMap t)⁻¹ * Q.map scalarMap
  have hprod : G.map scalarMap = p.map scalarMap * q := by
    calc
      G.map scalarMap = Polynomial.C (scalarMap t)⁻¹ * F.map scalarMap := by
        rw [hG, Polynomial.map_mul, Polynomial.map_C, ← mul_assoc,
          ← Polynomial.C_mul, inv_mul_cancel₀ htK, Polynomial.C_1, one_mul]
      _ = p.map scalarMap * q := by
        rw [hF, Polynomial.map_mul]
        dsimp only [q]
        ring
  obtain ⟨i, hi, hI, _⟩ :=
    Polynomial.exists_coeff_generator_of_contentIdeal_eq_top p q G hprod hGc
  exact ⟨i, hi, hI⟩

section RowPolynomial

variable {B : Type u} [CommRing B] {I : Type u} {n : ℕ}

/-- Encode the original finite coordinate row using its given finite labeling. -/
def rowPolynomial (e : I ≃ Fin n) (a : I → B) : Polynomial B := by
  classical
  exact Polynomial.ofFn n (fun i ↦ a (e.symm i))

private theorem rowPolynomial_coeff (e : I ≃ Fin n) (a : I → B) (i : I) :
    (rowPolynomial e a).coeff (e i) = a i := by
  classical
  simp [rowPolynomial, Polynomial.ofFn_coeff_eq_val_of_lt, (e i).isLt]

private theorem rowPolynomial_contentIdeal (e : I ≃ Fin n) (a : I → B) :
    (rowPolynomial e a).contentIdeal = Ideal.span (Set.range a) := by
  classical
  apply le_antisymm
  · rw [Polynomial.contentIdeal_def, Ideal.span_le]
    intro x hx
    obtain ⟨k, _, rfl⟩ := Polynomial.mem_coeffs_iff.mp hx
    by_cases hk : k < n
    · simp only [rowPolynomial, Polynomial.ofFn_coeff_eq_val_of_lt _ hk]
      exact Ideal.subset_span (Set.mem_range_self _)
    · simp only [rowPolynomial,
        Polynomial.ofFn_coeff_eq_zero_of_ge _ (Nat.le_of_not_gt hk)]
      exact Ideal.zero_mem _
  · apply Ideal.span_le.mpr
    rintro _ ⟨i, rfl⟩
    rw [← rowPolynomial_coeff e a i]
    exact (rowPolynomial e a).coeff_mem_contentIdeal (e i)

end RowPolynomial

section OriginalRow

variable {B : Type u} [CommRing B] {Y : Scheme.{u}} {I : Type u}
  (b : Y ⟶ Spec (.of B)) (a : I → B)

/-- The literal inverse image of the ideal generated by the original row. -/
def rowIdeal : Y.IdealSheafData :=
  (affineCenter B (Ideal.span (Set.range a))).comap b

/-- The actual kernel ideal module of the original inverse-image row ideal. -/
abbrev rowModule : Y.Modules := Hom.idealModule (rowIdeal b a).subschemeι

/-- The original coordinate as a global function through the specified B-map. -/
def rowScalar (i : I) : Γ(Y, ⊤) := affineBaseMap b ⊤ (a i)

private theorem rowScalar_restrict (U : Y.Opens) (i : I) :
    (Y.presheaf.map (homOfLE (show U ≤ ⊤ from le_top)).op).hom (rowScalar b a i) =
      affineBaseMap b U (a i) :=
  RingHom.congr_fun (affineBaseMap_restrict b (show U ≤ ⊤ from le_top)) (a i)

private theorem rowIdeal_kernel (U : Y.affineOpens) :
    RingHom.ker ((rowIdeal b a).subschemeι.app U).hom =
      Ideal.span (Set.range (fun i ↦ affineBaseMap b U (a i))) := by
  rw [(rowIdeal b a).ker_subschemeι_app, rowIdeal, affineCenter_comap_ideal,
    Ideal.map_span]
  congr 1
  ext x
  simp

/-- Each original coordinate factors through the actual row ideal by its kernel lift. -/
def rowSection (i : I) :
    (show Y.Modules from SheafOfModules.unit Y.ringCatSheaf) ⟶ rowModule b a :=
  kernel.lift (Hom.structureModuleMap (rowIdeal b a).subschemeι)
    (unitMul Y (rowScalar b a i)) (by
      apply moduleHom_ext_affine
      intro U
      ext r
      change Γ(Y, U) at r
      change ((rowIdeal b a).subschemeι.app U).hom
        (r * (Y.presheaf.map (homOfLE (show U.1 ≤ ⊤ from le_top)).op).hom
          (rowScalar b a i)) = 0
      rw [rowScalar_restrict, map_mul]
      have hi : affineBaseMap b U (a i) ∈
          RingHom.ker ((rowIdeal b a).subschemeι.app U).hom := by
        rw [rowIdeal_kernel]
        exact Ideal.subset_span (Set.mem_range_self i)
      rw [show ((rowIdeal b a).subschemeι.app U).hom (affineBaseMap b U (a i)) = 0 from hi,
        mul_zero])

/-- The kernel lift retains the original coordinate multiplication map. -/
@[reassoc]
theorem rowSection_inclusion (i : I) :
    rowSection b a i ≫ Hom.idealInclusion (rowIdeal b a).subschemeι =
      unitMul Y (rowScalar b a i) :=
  kernel.lift_ι _ _ _

private theorem rowSection_inclusion_value (U : Y.Opens) (i : I) :
    ((Hom.idealInclusion (rowIdeal b a).subschemeι).val.app (op U)).hom
        (((rowSection b a i).val.app (op U)).hom (1 : Γ(Y, U))) =
      affineBaseMap b U (a i) := by
  have h := congrArg
    (fun f : unitModule Y ⟶ unitModule Y ↦
      (f.val.app (op U)).hom (1 : Γ(Y, U)))
    (rowSection_inclusion b a i)
  change ((Hom.idealInclusion (rowIdeal b a).subschemeι).val.app (op U)).hom
      (((rowSection b a i).val.app (op U)).hom (1 : Γ(Y, U))) =
    (1 : Γ(Y, U)) *
      (Y.presheaf.map (homOfLE (show U ≤ ⊤ from le_top)).op).hom (rowScalar b a i) at h
  simpa only [one_mul, rowScalar_restrict] using h

/-- The original finite row generates its actual image ideal on every affine open. -/
instance rowSection_epi [Finite I] : Epi (Sigma.desc (rowSection b a)) := by
  classical
  let := Fintype.ofFinite I
  constructor
  intro N g k h
  apply moduleHom_ext_affine
  intro U
  let : Module Γ(Y, U.1) ((rowModule b a).val.obj (op U.1)) :=
    ((rowModule b a).val.obj (op U.1)).isModule
  let : Module Γ(Y, U.1) (N.val.obj (op U.1)) :=
    (N.val.obj (op U.1)).isModule
  ext m
  change (rowModule b a).val.obj (op U.1) at m
  let incU : (rowModule b a).val.obj (op U.1) →ₗ[Γ(Y, U.1)] Γ(Y, U.1) :=
    ((Hom.idealInclusion (rowIdeal b a).subschemeι).val.app (op U.1)).hom
  let gU : (rowModule b a).val.obj (op U.1) →ₗ[Γ(Y, U.1)] N.val.obj (op U.1) :=
    (g.val.app (op U.1)).hom
  let kU : (rowModule b a).val.obj (op U.1) →ₗ[Γ(Y, U.1)] N.val.obj (op U.1) :=
    (k.val.app (op U.1)).hom
  change gU m = kU m
  let mI : RingHom.ker ((rowIdeal b a).subschemeι.app U).hom :=
    (Hom.idealSectionsEquiv (rowIdeal b a).subschemeι U).toFun m
  have hmVal : (mI : Γ(Y, U)) = incU m :=
    Hom.idealSectionsEquiv_val (rowIdeal b a).subschemeι U m
  have hmI : (mI : Γ(Y, U)) ∈
      Ideal.span (Set.range (fun i ↦ affineBaseMap b U (a i))) := by
    rw [← rowIdeal_kernel]
    exact mI.property
  obtain ⟨r, hr⟩ := (Submodule.mem_span_range_iff_exists_fun (Γ(Y, U))).mp hmI
  have hinc : Function.Injective incU := by
    intro x y hxy
    apply (Hom.idealSectionsEquiv (rowIdeal b a).subschemeι U).injective
    apply Subtype.ext
    exact (Hom.idealSectionsEquiv_val (rowIdeal b a).subschemeι U x).trans
      (hxy.trans (Hom.idealSectionsEquiv_val (rowIdeal b a).subschemeι U y).symm)
  have hm : m = ∑ i, r i • ((rowSection b a i).val.app (op U.1)).hom
      (1 : Γ(Y, U)) := by
    apply hinc
    calc
      incU m = (mI : Γ(Y, U)) := hmVal.symm
      _ = ∑ i, r i • affineBaseMap b U (a i) := hr.symm
      _ = ∑ i, incU (r i • ((rowSection b a i).val.app (op U.1)).hom
          (1 : Γ(Y, U))) := by
        apply Finset.sum_congr rfl
        intro i _
        have hsval : incU (((rowSection b a i).val.app (op U.1)).hom
            (1 : Γ(Y, U))) = affineBaseMap b U (a i) :=
          rowSection_inclusion_value b a U i
        exact ((incU.map_smul (r i) _).trans
          (congrArg (fun z ↦ r i • z) hsval)).symm
      _ = incU (∑ i, r i • ((rowSection b a i).val.app (op U.1)).hom
          (1 : Γ(Y, U))) := (map_sum incU _ _).symm
  have hi (i : I) :
      gU (((rowSection b a i).val.app (op U.1)).hom (1 : Γ(Y, U))) =
        kU (((rowSection b a i).val.app (op U.1)).hom (1 : Γ(Y, U))) := by
    have he := congrArg
      (fun f ↦ Sigma.ι (fun _ : I ↦ unitModule Y) i ≫ f) h
    simp only [Sigma.ι_comp_desc_assoc] at he
    exact congrArg (fun f : unitModule Y ⟶ N ↦
      (f.val.app (op U.1)).hom (1 : Γ(Y, U))) he
  rw [hm, map_sum, map_sum]
  apply Finset.sum_congr rfl
  intro i _
  exact (gU.map_smul (r i) _).trans
    ((congrArg (fun z ↦ r i • z) (hi i)).trans (kU.map_smul (r i) _).symm)

end OriginalRow

section LocalFrames

variable {B : Type u} [CommRing B] {Y : Scheme.{u}} [IsIntegral Y]
  {I : Type u} {n : ℕ}
  (b : Y ⟶ Spec (.of B)) (a : I → B) (e : I ≃ Fin n)
  (F Q : Polynomial B) (hF : F = rowPolynomial e a * Q)
  (hY : NormalStalks Y)
  (hcontent : IsLocallyRankOne Y
    (Hom.idealModule ((affineCenter B F.contentIdeal).comap b).subschemeι))

include e F Q hF hY hcontent in
/-- The coefficient-ideal frame produces a nonzero generator from the same original row
in every actual local ring. No row-principality hypothesis is supplied. -/
theorem rowIdeal_stalk_generator (y : Y) :
    ∃ r : Y.presheaf.stalk y, r ≠ 0 ∧
      (rowIdeal b a).stalkIdeal y = Ideal.span ({r} : Set (Y.presheaf.stalk y)) := by
  let K : Y.IdealSheafData := (affineCenter B F.contentIdeal).comap b
  obtain ⟨U, hU, hy, t, ht, hgen⟩ :=
    Hom.exists_affine_regular_idealGenerator_of_isLocallyRankOne K.subschemeι hcontent y
  let : Nonempty U := ⟨⟨y, hy⟩⟩
  let R := Y.presheaf.stalk y
  let : IsIntegrallyClosed R := (hY y).2
  let β₀ : B →+* Γ(Y, U) := affineBaseMap b U
  let γ : Γ(Y, U) →+* R := (Y.presheaf.germ U y hy).hom
  let β : B →+* R := γ.comp β₀
  have ht0 : t ≠ 0 := by
    intro hz
    have h10 : (1 : Γ(Y, U)) = 0 := ht (by simp only [hz, zero_smul])
    exact one_ne_zero h10
  have htR : γ t ≠ 0 := fun hz ↦
    ht0 (germ_injective_of_isIntegral Y y hy (by simpa only [map_zero] using hz))
  have hFU : (F.map β₀).contentIdeal = Ideal.span ({t} : Set Γ(Y, U)) := by
    rw [Polynomial.contentIdeal_map_eq_map_contentIdeal]
    change F.contentIdeal.map (affineBaseMap b U) = _
    rw [← affineCenter_comap_ideal F.contentIdeal b ⟨U, hU⟩]
    exact (K.ker_subschemeι_app ⟨U, hU⟩).symm.trans hgen
  have hFR : (F.map β).contentIdeal = Ideal.span ({γ t} : Set R) := by
    change (F.map (γ.comp β₀)).contentIdeal = _
    rw [← Polynomial.map_map, Polynomial.contentIdeal_map_eq_map_contentIdeal, hFU,
      Ideal.map_span, Set.image_singleton]
  have hFRprod : F.map β = (rowPolynomial e a).map β * Q.map β := by
    rw [hF, Polynomial.map_mul]
  obtain ⟨k, hk, hrow⟩ :=
    row_generator_of_content_frame (K := Y.functionField)
      ((rowPolynomial e a).map β) (Q.map β) (F.map β) hFRprod (γ t) htR hFR
  refine ⟨((rowPolynomial e a).map β).coeff k, hk, ?_⟩
  rw [(rowIdeal b a).stalkIdeal_eq_map ⟨U, hU⟩ y hy]
  change (((affineCenter B (Ideal.span (Set.range a))).comap b).ideal ⟨U, hU⟩).map γ = _
  rw [affineCenter_comap_ideal, Ideal.map_map]
  change (Ideal.span (Set.range a)).map β = _
  rw [← rowPolynomial_contentIdeal e a, ← Polynomial.contentIdeal_map_eq_map_contentIdeal]
  exact hrow

include e F Q hF hY hcontent in
/-- Actual stalk-kernel bases make the actual inverse-image row module locally rank one. -/
theorem rowModule_isLocallyRankOne [IsLocallyNoetherian Y] :
    IsLocallyRankOne Y (rowModule b a) := by
  apply Hom.idealModule_isLocallyRankOne_of_stalkKernelBasis (rowIdeal b a).subschemeι
  intro c
  obtain ⟨r, hr, hI⟩ := rowIdeal_stalk_generator b a e F Q hF hY hcontent
    ((rowIdeal b a).subschemeι c)
  have hreg : IsSMulRegular (Y.presheaf.stalk ((rowIdeal b a).subschemeι c)) r := by
    intro x y hxy
    exact mul_left_cancel₀ hr hxy
  refine ⟨Ideal.regularPrincipalIdealBasis _ r hreg ?_⟩
  rw [← (rowIdeal b a).stalkIdeal_subschemeι_eq_ker_stalkMap c]
  exact hI

include e F Q hF hY hcontent in
/-- The actual section frames are produced from the proved row generation and local rank one. -/
def rowSectionFrames [Finite I] [IsLocallyNoetherian Y] :
    ProjectiveSpace.FromSections.SectionFrames (rowModule b a)
      (@ProjectiveSpace.FromSections.generatingSectionsOfFamily I Y (rowModule b a)
        (rowSection b a) (rowSection_epi b a)).s := by
  let σ : (rowModule b a).GeneratingSections :=
    @ProjectiveSpace.FromSections.generatingSectionsOfFamily I Y (rowModule b a)
      (rowSection b a) (rowSection_epi b a)
  let : σ.IsFiniteType :=
    @ProjectiveSpace.FromSections.generatingSectionsOfFamily_isFiniteType I Y
      (rowModule b a) inferInstance (rowSection b a) (rowSection_epi b a)
  exact ProjectiveSpace.FromSections.framesOfGeneratingSections (rowModule b a)
    (rowModule_isLocallyRankOne b a e F Q hF hY hcontent) σ

include e F Q hF hY hcontent in
/-- The original row extends to the actual projective morphism after
coefficient principalization. -/
def projectiveMap [Finite I] [IsLocallyNoetherian Y] : Y ⟶ ProjectiveSpace B I :=
  @ProjectiveSpace.FromSections.mapOfFiniteFamily B inferInstance I Y b (rowModule b a)
    (rowModule_isLocallyRankOne b a e F Q hF hY hcontent) inferInstance
    (rowSection b a) (rowSection_epi b a)

include e F Q hF hY hcontent in
@[reassoc]
theorem projectiveMap_toSpec [Finite I] [IsLocallyNoetherian Y] :
    projectiveMap b a e F Q hF hY hcontent ≫ ProjectiveSpace.toSpec B I = b :=
  @ProjectiveSpace.FromSections.mapOfFiniteFamily_toSpec B inferInstance I Y b
    (rowModule b a) (rowModule_isLocallyRankOne b a e F Q hF hY hcontent) inferInstance
    (rowSection b a) (rowSection_epi b a)

end LocalFrames

section GenericCoordinates

variable {B K : Type u} [CommRing B] [Field K]
  {Y : Scheme.{u}} [IsIntegral Y] [IsLocallyNoetherian Y]
  {I : Type u} {n : ℕ}
  (b : Y ⟶ Spec (.of B)) (a : I → B) (e : I ≃ Fin n)
  (F Q : Polynomial B) (hF : F = rowPolynomial e a * Q)
  (hY : NormalStalks Y)
  (hcontent : IsLocallyRankOne Y
    (Hom.idealModule ((affineCenter B F.contentIdeal).comap b).subschemeι))
  (η : Spec (.of K) ⟶ Y) (ρ : B →+* K)
  (hη : η ≫ b = Spec.map (CommRingCat.ofHom ρ))

omit [IsIntegral Y] [IsLocallyNoetherian Y] in
include hη in
private theorem rowScalar_generic (i : I) :
    η.appTop (rowScalar b a i) = (Scheme.ΓSpecIso (.of K)).inv.hom (ρ (a i)) := by
  have he :
      (Scheme.ΓSpecIso (.of B)).inv ≫ b.appTop ≫ η.appTop =
        CommRingCat.ofHom ρ ≫ (Scheme.ΓSpecIso (.of K)).inv := by
    rw [← Scheme.Hom.comp_appTop, hη]
    exact (Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom ρ)).symm
  have hv := congrArg (fun f : CommRingCat.of B ⟶ Γ(Spec (.of K), ⊤) ↦ f.hom (a i)) he
  have htop :
      b.appLE ⊤ ⊤ (by simp) = b.appTop := by
    simpa only [Scheme.Hom.preimage_top] using
      (Scheme.Hom.appLE_eq_app b (U := ⊤))
  simpa only [rowScalar, affineBaseMap, htop, CommRingCat.hom_comp,
    RingHom.comp_apply, CommRingCat.hom_ofHom, CommRingCat.Hom.hom] using hv

/-- Pull back the actual row-ideal inclusion, retaining its canonical target unit comparison. -/
def genericRowInclusion :
    (Modules.pullback η).obj (rowModule b a) ⟶
      (show (Spec (.of K)).Modules from
        SheafOfModules.unit (Spec (.of K)).ringCatSheaf) :=
  (Modules.pullback η).map (Hom.idealInclusion (rowIdeal b a).subschemeι) ≫
    (pullbackUnitIso η).hom

omit [IsIntegral Y] [IsLocallyNoetherian Y] in
include hη in
private theorem genericRowInclusion_section (i : I) :
    ProjectiveSpace.FromSections.pulledFamily η (rowSection b a) i ≫
        genericRowInclusion b a η =
      ProjectiveSpace.FromSections.FieldSpan.family (fun i ↦ ρ (a i)) i := by
  let PB : Y.Modules ⥤ (Spec (.of K)).Modules := Modules.pullback η
  let ui : PB.obj (unitModule Y) ≅ unitModule (Spec (.of K)) := pullbackUnitIso η
  let inc : rowModule b a ⟶ unitModule Y := Hom.idealInclusion (rowIdeal b a).subschemeι
  let w : unitModule (Spec (.of K)) ⟶ unitModule (Spec (.of K)) :=
    unitMul (Spec (.of K)) (η.appTop (rowScalar b a i))
  let z : unitModule (Spec (.of K)) ⟶ unitModule (Spec (.of K)) :=
    ProjectiveSpace.FromSections.FieldSpan.family (fun i ↦ ρ (a i)) i
  have hw : PB.map (unitMul Y (rowScalar b a i)) ≫ ui.hom = ui.hom ≫ w :=
    unitMul_pullback η (rowScalar b a i)
  have hwz : w = z := by
    exact congrArg (fun t : Γ(Spec (.of K), ⊤) ↦
      (show unitModule (Spec (.of K)) ⟶ unitModule (Spec (.of K)) from
        unitMul (Spec (.of K)) t)) (rowScalar_generic b a η ρ hη i)
  change (ui.inv ≫ PB.map (rowSection b a i)) ≫ (PB.map inc ≫ ui.hom) = z
  calc
    _ = ui.inv ≫ PB.map (rowSection b a i ≫ inc) ≫ ui.hom := by
      simp only [Functor.map_comp, Category.assoc]
    _ = ui.inv ≫ PB.map (unitMul Y (rowScalar b a i)) ≫ ui.hom := by
      exact congrArg (fun f : unitModule Y ⟶ unitModule Y ↦
        ui.inv ≫ PB.map f ≫ ui.hom) (rowSection_inclusion b a i)
    _ = ui.inv ≫ (ui.hom ≫ w) :=
      congrArg (fun f : PB.obj (unitModule Y) ⟶ unitModule (Spec (.of K)) ↦
        ui.inv ≫ f) hw
    _ = w := ui.inv_hom_id_assoc w
    _ = z := hwz

include e F Q hF hY hcontent hη in
private theorem genericRowInclusion_isIso (i₀ : I) (hi₀ : ρ (a i₀) ≠ 0) :
    IsIso (genericRowInclusion b a η) := by
  let hM := rowModule_isLocallyRankOne b a e F Q hF hY hcontent
  apply fieldLineBundleMap_isIso_of_ne_zero K
    ⟨(Modules.pullback η).obj (rowModule b a), pullback_locallyRankOne η _ hM⟩
    ⟨unitModule (Spec (.of K)),
      ProjectiveSpace.FromSections.FieldSpan.unit_rankOne _⟩
  intro hz
  let v : unitModule (Spec (.of K)) ⟶ (Modules.pullback η).obj (rowModule b a) :=
    ProjectiveSpace.FromSections.pulledFamily η (rowSection b a) i₀
  let w : unitModule (Spec (.of K)) ⟶ unitModule (Spec (.of K)) :=
    ProjectiveSpace.FromSections.FieldSpan.family (fun i ↦ ρ (a i)) i₀
  have hs : v ≫ genericRowInclusion b a η = w :=
    genericRowInclusion_section b a η ρ hη i₀
  have hw : w = 0 := by
    calc
      w = v ≫ genericRowInclusion b a η := hs.symm
      _ = v ≫ 0 := congrArg (fun f : (Modules.pullback η).obj (rowModule b a) ⟶
          unitModule (Spec (.of K)) ↦ v ≫ f) hz
      _ = 0 := comp_zero
  have hv := congrArg
    (fun f : unitModule (Spec (.of K)) ⟶ unitModule (Spec (.of K)) ↦
      (f.val.app (op ⊤)).hom (1 : Γ(Spec (.of K), ⊤))) hw
  have hvalue : (Scheme.ΓSpecIso (.of K)).inv.hom (ρ (a i₀)) = 0 := by
    change (1 : Γ(Spec (.of K), ⊤)) *
      ((Spec (.of K)).presheaf.map (homOfLE (show (⊤ : (Spec (.of K)).Opens) ≤ ⊤
        from le_top)).op).hom ((Scheme.ΓSpecIso (.of K)).inv.hom (ρ (a i₀))) = 0 at hv
    simpa using hv
  apply hi₀
  exact (ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso (.of K)).inv).1
    (hvalue.trans (map_zero (Scheme.ΓSpecIso (.of K)).inv.hom).symm)

include e F Q hF hY hcontent hη in
/-- The constructed projective map recovers the supplied original generic chart,
using the original row ratios and the original coefficient homomorphism. -/
theorem projectiveMap_generic [Finite I]
    (i₀ : I) (hi₀ : ρ (a i₀) ≠ 0)
    (φ : ProjectiveSpace.coordinateRing B I i₀ →+* K)
    (hφB : ∀ r, φ (ProjectiveSpace.coordinateRingCoefficient B I i₀ r) = ρ r)
    (hφratio : ∀ i, φ (ProjectiveSpace.coordinateRatio B I i₀ i) =
      ρ (a i) * (ρ (a i₀))⁻¹) :
    η ≫ projectiveMap b a e F Q hF hY hcontent =
      Spec.map (CommRingCat.ofHom φ) ≫
        Proj.awayι (MvPolynomial.homogeneousSubmodule I B) (MvPolynomial.X i₀)
          (MvPolynomial.isHomogeneous_X B i₀) Nat.zero_lt_one := by
  let hM := rowModule_isLocallyRankOne b a e F Q hF hY hcontent
  let hs := rowSection_epi b a
  let : IsIso (genericRowInclusion b a η) :=
    genericRowInclusion_isIso b a e F Q hF hY hcontent η ρ hη i₀ hi₀
  let O : (Spec (.of K)).Modules := unitModule (Spec (.of K))
  let v : (Modules.pullback η).obj (rowModule b a) ≅ O :=
    asIso (genericRowInclusion b a η)
  let t : I → (O ⟶ O) := fun i ↦
    ProjectiveSpace.FromSections.pulledFamily η (rowSection b a) i ≫ v.hom
  let hsη : Epi (Sigma.desc (ProjectiveSpace.FromSections.pulledFamily η (rowSection b a))) :=
    @ProjectiveSpace.FromSections.pulledFamily_epi I Y (Spec (.of K)) η
      (rowModule b a) (rowSection b a) hs
  let ht : Epi (Sigma.desc t) :=
    @ProjectiveSpace.FromSections.family_comp_iso_epi I (Spec (.of K))
      ((Modules.pullback η).obj (rowModule b a)) O
      (ProjectiveSpace.FromSections.pulledFamily η (rowSection b a)) hsη v
  let hf : Epi (Sigma.desc (ProjectiveSpace.FromSections.FieldSpan.family
      (fun i ↦ ρ (a i)))) :=
    ProjectiveSpace.FromSections.FieldSpan.family_epi_of_nonzero _ i₀ hi₀
  let hO := ProjectiveSpace.FromSections.FieldSpan.unit_rankOne (Spec (.of K))
  let htO := isLocallyRankOne_of_iso (Spec (.of K)) v
    (pullback_locallyRankOne η (rowModule b a) hM)
  have hm :
      η ≫ projectiveMap b a e F Q hF hY hcontent =
        @ProjectiveSpace.FromSections.mapOfFiniteFamily B inferInstance I (Spec (.of K))
          (η ≫ b) O hO inferInstance
          (ProjectiveSpace.FromSections.FieldSpan.family (fun i ↦ ρ (a i))) hf := by
    have hpull : η ≫ projectiveMap b a e F Q hF hY hcontent =
        @ProjectiveSpace.FromSections.mapOfFiniteFamily B inferInstance I (Spec (.of K))
          (η ≫ b) O htO inferInstance t ht :=
      @ProjectiveSpace.FromSections.mapOfFiniteFamily_pullback_iso B inferInstance I Y
        (Spec (.of K)) η b (rowModule b a) hM inferInstance (rowSection b a) hs O v
    refine hpull.trans ?_
    exact @ProjectiveSpace.FromSections.mapOfFiniteFamily_iso B inferInstance I
      (Spec (.of K)) (η ≫ b) O O htO hO inferInstance t
      (ProjectiveSpace.FromSections.FieldSpan.family (fun i ↦ ρ (a i))) ht hf (Iso.refl O)
      (fun i ↦ (Category.comp_id _).trans (genericRowInclusion_section b a η ρ hη i))
  rw [hm, hη]
  exact ProjectiveSpace.FromSections.FieldSpan.mapOfFiniteFamily_eq_chart_of_ratios
    ρ (fun i ↦ ρ (a i)) i₀ hi₀ φ hφB hφratio

end GenericCoordinates

private theorem exists_original_chow_factor
    {D Y P Q T S : Scheme.{u}} [IsReduced Y]
    (η : D ⟶ Y) [IsDominant η]
    (j : P ⟶ Q) [IsClosedImmersion j]
    (p : P ⟶ T) (g : T ⟶ S) (q : Q ⟶ S) (b : Y ⟶ S)
    (hbase : j ≫ q = p ≫ g)
    (u : Y ⟶ Q) (hu : u ≫ q = b)
    (α : D ⟶ P) (hgeneric : η ≫ u = α ≫ j) :
    ∃ h : Y ⟶ T, h ≫ g = b ∧ η ≫ h = α ≫ p := by
  obtain ⟨v, hv, hηv⟩ :=
    Scheme.Birational.exists_closedImmersion_factor_of_dominant η u j α hgeneric
  refine ⟨v ≫ p, ?_, ?_⟩
  · rw [Category.assoc, ← hbase, ← Category.assoc, hv, hu]
  · rw [← Category.assoc, hηv]

private theorem exists_cleared_row
    {B K : Type u} [CommRing B] [IsDomain B] [Field K]
    [Algebra B K] [IsFractionRing B K] {I : Type u} [Finite I]
    (r : I → K) (i₀ : I) (hi₀ : r i₀ = 1) :
    ∃ (a : I → B) (c : B), c ≠ 0 ∧ a i₀ = c ∧
      ∀ i, algebraMap B K (a i) = algebraMap B K c * r i := by
  obtain ⟨c, hc⟩ :=
    IsLocalization.exist_integer_multiples_of_finite (nonZeroDivisors B) r
  choose a ha using hc
  have hav (i : I) :
      algebraMap B K (a i) = algebraMap B K (c : B) * r i := by
    simpa only [Algebra.smul_def] using ha i
  refine ⟨a, c, nonZeroDivisors.ne_zero c.property, ?_, hav⟩
  apply IsFractionRing.injective B K
  rw [hav, hi₀, mul_one]

section Producer

open NormalizedBlowupCover

variable (A B : Type u) [CommRing A] [IsDomain A] [IsNoetherianRing A]
  [CommRing B] [IsDomain B] [IsNoetherianRing B]
  [Algebra A B] [Module.Finite A B]

/-- Every original integral proper birational B-model is dominated by an
actual normal B-model finite over an actual normal A-model.

The specified spectral map is the original algebra map; its arbitrary finite
field extension is read through its original function-field homomorphism.
No projective model, row generator, finite diagram, or flattening theorem is
supplied by the caller. -/
theorem exists_finite_domination
    (hinj : Function.Injective (algebraMap A B))
    (s : Spec (.of B) ⟶ Spec (.of A)) [IsDominant s] [IsFinite s]
    (hs : s = Spec.map (CommRingCat.ofHom (algebraMap A B)))
    (hd : ringKrullDim A ≤ 2) (hA : IsNagataRing.{u, 0} A)
    (hfin : (Scheme.functionFieldMap s).Finite)
    {T : Scheme.{u}} [IsIntegral T]
    (g : T ⟶ Spec (.of B)) [IsProper g] [IsDominant g]
    (hg : IsIso (CommRingCat.ofHom (Scheme.functionFieldMap g))) :
    ∃ (X Y : Scheme.{u}) (hX : IsIntegral X) (hY : IsIntegral Y),
      letI := hX
      letI := hY
      ∃ (a : X ⟶ Spec (.of A)) (b : Y ⟶ Spec (.of B))
        (π : Y ⟶ X) (h : Y ⟶ T)
        (ha : IsDominant a) (hb : IsDominant b) (hh : IsDominant h),
        letI := ha
        letI := hb
        letI := hh
        NormalStalks X ∧ NormalStalks Y ∧
          IsProper a ∧ IsProper b ∧ IsProper h ∧ IsFinite π ∧ IsDominant π ∧
          IsIso (CommRingCat.ofHom (Scheme.functionFieldMap a)) ∧
          IsIso (CommRingCat.ofHom (Scheme.functionFieldMap b)) ∧
          IsIso (CommRingCat.ofHom (Scheme.functionFieldMap h)) ∧
          h ≫ g = b ∧ π ≫ a = b ≫ s := by
  classical
  obtain ⟨P, p, m, j, V, hp, _, hj, hjbase, hV, hViso⟩ :=
    Scheme.Chow.exists_projective_modification B g
  let : IsProper p := hp
  let : IsClosedImmersion j := hj
  let L : Type u := (Spec (.of B)).functionField
  let : Field L := inferInstanceAs (Field (Spec (.of B)).functionField)
  let : Algebra B L :=
    AlgebraicGeometry.instAlgebraCarrierFunctionFieldSpec (.of B)
  let : IsFractionRing B L :=
    functionField_isFractionRing_of_affine (.of B)
  let eg : (Spec (.of B)).functionField ≅ T.functionField :=
    Cover.baseFieldIso g hg
  let α : Spec (.of L) ⟶ P :=
    Spec.map eg.inv ≫ Scheme.Birational.modificationGenericInverse p V hV hViso
  have hαp : α ≫ p =
      Spec.map eg.inv ≫ T.fromSpecStalk (genericPoint T) := by
    simp only [α, Category.assoc, Scheme.Birational.modificationGenericInverse_comp]
  have hαg : α ≫ p ≫ g =
      (Spec (.of B)).fromSpecStalk (genericPoint (Spec (.of B))) := by
    rw [← Category.assoc, hαp, Category.assoc,
      Scheme.fromSpecStalk_genericPoint_naturality g, ← Category.assoc]
    have heg : eg.hom = CommRingCat.ofHom (Scheme.functionFieldMap g) :=
      Cover.baseFieldIso_hom g hg
    rw [← heg, ← Spec.map_comp, eg.hom_inv_id]
    exact (congrArg
      (fun f : Spec (Spec (.of B)).functionField ⟶ Spec (Spec (.of B)).functionField ↦
        f ≫ (Spec (.of B)).fromSpecStalk (genericPoint (Spec (.of B))))
      (Spec.map_id (Spec (.of B)).functionField)).trans (Category.id_comp _)
  let ρ : B →+* L := algebraMap B L
  have hηB :
      (Spec (.of B)).fromSpecStalk (genericPoint (Spec (.of B))) =
        Spec.map (CommRingCat.ofHom ρ) := by
    change (Spec (.of B)).fromSpecStalk (genericPoint (Spec (.of B))) =
      Spec.map (StructureSheaf.toStalk (CommRingCat.of B) _)
    exact Spec.fromSpecStalk_eq' _ _
  have hzbase : (α ≫ j) ≫ ProjectiveSpace.toSpec B (ULift (Fin (m + 1))) =
      Spec.map (CommRingCat.ofHom ρ) := by
    rw [Category.assoc, hjbase, hαg, hηB]
  obtain ⟨i₀, φ, hφB, hφ⟩ :=
    ProjectiveSpace.exists_coordinateChart_factorization_over (α ≫ j) hzbase
  let r : ULift (Fin (m + 1)) → L :=
    ProjectiveSpace.chartHomCoordinates i₀ φ
  have hr₀ : r i₀ = 1 := ProjectiveSpace.chartHomCoordinates_self i₀ φ
  obtain ⟨row, c, hc, hrow₀, hrow⟩ := exists_cleared_row (B := B) (K := L) r i₀ hr₀
  let e : ULift (Fin (m + 1)) ≃ Fin (m + 1) := Equiv.ulift
  have hpRow : rowPolynomial e row ≠ 0 := by
    intro hz
    have hz' := congrArg (fun f : Polynomial B ↦ f.coeff (e i₀)) hz
    have hzrow : row i₀ = 0 := by simpa only [rowPolynomial_coeff, Polynomial.coeff_zero] using hz'
    exact hc (hrow₀.symm.trans hzrow)
  obtain ⟨FA, Q, hFA, _, hFAprod⟩ :=
    Polynomial.exists_nonzero_map_eq_mul_of_integral hinj hpRow
  let J : Ideal A := FA.contentIdeal
  have hJ : J ≠ ⊥ := by
    exact fun hz ↦ hFA ((Polynomial.contentIdeal_eq_bot_iff FA).mp hz)
  let X := Base.normalization A J hJ
  let Y := FiniteBase.Y A B J hJ s
  let a₀ : X ⟶ Spec (.of A) := Base.a A J hJ
  let b₀ : Y ⟶ Spec (.of B) := FiniteBase.b A B J hJ s
  let π : Y ⟶ X := FiniteBase.pi A B J hJ s
  let η : Spec (.of L) ⟶ Y := FiniteBase.eta A B J hJ s
  let : IsLocallyNoetherian Y :=
    FiniteBase.Nagata.Y_isLocallyNoetherian A B J hJ s hd hA hfin
  have hYN : NormalStalks Y := FiniteBase.Nagata.Y_normalStalks A B J hJ s hfin
  have hcontentY : IsLocallyRankOne Y
      (Hom.idealModule ((affineCenter B
        (FA.map (algebraMap A B)).contentIdeal).comap b₀).subschemeι) := by
    have he : FiniteBase.imageIdeal A B J hJ s =
        (affineCenter B (FA.map (algebraMap A B)).contentIdeal).comap b₀ := by
      have hbase : (affineCenter A J).comap s =
          affineCenter B (FA.map (algebraMap A B)).contentIdeal := by
        rw [hs, BaseChange.affineCenter_comap,
          Polynomial.contentIdeal_map_eq_map_contentIdeal]
      exact (FiniteBase.imageIdeal_eq_over_B A B J hJ s).trans
        (congrArg (fun K : (Spec (.of B)).IdealSheafData ↦ K.comap b₀) hbase)
    rw [← he]
    exact FiniteBase.imageIdeal_isLocallyRankOne A B J hJ s
  let u : Y ⟶ ProjectiveSpace B (ULift (Fin (m + 1))) :=
    projectiveMap b₀ row e (FA.map (algebraMap A B)) Q hFAprod hYN hcontentY
  have hu : u ≫ ProjectiveSpace.toSpec B (ULift (Fin (m + 1))) = b₀ :=
    projectiveMap_toSpec b₀ row e (FA.map (algebraMap A B)) Q hFAprod hYN hcontentY
  have hηb : η ≫ b₀ = Spec.map (CommRingCat.ofHom ρ) :=
    (FiniteBase.eta_b A B J hJ s).trans hηB
  have hrow₀K : ρ (row i₀) ≠ 0 := by
    rw [hrow₀]
    exact fun hz ↦ hc (IsFractionRing.injective B L (by simpa only [map_zero] using hz))
  have huη : η ≫ u = α ≫ j := by
    refine (projectiveMap_generic b₀ row e (FA.map (algebraMap A B)) Q hFAprod
      hYN hcontentY η ρ hηb i₀ hrow₀K φ ?_ ?_).trans hφ
    · intro z
      exact RingHom.congr_fun hφB z
    · intro i
      change r i = ρ (row i) * (ρ (row i₀))⁻¹
      rw [hrow i, hrow i₀, hr₀, mul_one]
      have hcK : algebraMap B L c ≠ 0 :=
        (map_ne_zero_iff _ (IsFractionRing.injective B L)).mpr hc
      rw [mul_comm (algebraMap B L c) (r i), mul_assoc, mul_inv_cancel₀ hcK, mul_one]
  obtain ⟨h, hbg, hηh⟩ :=
    exists_original_chow_factor η j p g
      (ProjectiveSpace.toSpec B (ULift (Fin (m + 1)))) b₀ hjbase u hu α huη
  have : IsDominant (α ≫ p) := by
    rw [hαp]
    infer_instance
  have : IsDominant (η ≫ h) := by rw [hηh]; infer_instance
  have : IsDominant h := IsDominant.of_comp η h
  have : IsProper b₀ := FiniteBase.Nagata.b_isProper A B J hJ s hd hA hfin
  have : IsProper (h ≫ g) := by rw [hbg]; infer_instance
  have hhproper : IsProper h := IsProper.of_comp h g
  have hhfield : IsIso (CommRingCat.ofHom (Scheme.functionFieldMap h)) := by
    have hcongr {c d : Y ⟶ Spec (.of B)} [IsDominant c] [IsDominant d]
        (w : c = d) : Scheme.functionFieldMap c = Scheme.functionFieldMap d := by
      subst d
      rfl
    have hcomp : (Scheme.functionFieldMap h).comp (Scheme.functionFieldMap g) =
        Scheme.functionFieldMap b₀ :=
      (Scheme.functionFieldMap_comp h g).symm.trans (hcongr hbg)
    have hbBij : Function.Bijective (Scheme.functionFieldMap b₀) :=
      (ConcreteCategory.isIso_iff_bijective _).mp
        (FiniteBase.b_fieldMap_isIso A B J hJ s)
    apply (ConcreteCategory.isIso_iff_bijective _).mpr
    refine ⟨(Scheme.functionFieldMap h).injective, ?_⟩
    intro z
    obtain ⟨x, hx⟩ := hbBij.2 z
    exact ⟨Scheme.functionFieldMap g x, (RingHom.congr_fun hcomp x).trans hx⟩
  refine ⟨X, Y, inferInstance, inferInstance, a₀, b₀, π, h,
    inferInstance, inferInstance, inferInstance, ?_⟩
  exact ⟨Base.normalization_normalStalks A J hJ, hYN,
    Base.a_isProper A J hJ hd hA, inferInstance, hhproper,
    FiniteBase.Nagata.pi_isFinite A B J hJ s hd hA hfin,
    inferInstance,
    Base.a_fieldMap_isIso A J hJ, FiniteBase.b_fieldMap_isIso A B J hJ s,
    hhfield, hbg, FiniteBase.square A B J hJ s⟩

end Producer

end AlgebraicGeometry.Scheme.Birational.FiniteDomination
