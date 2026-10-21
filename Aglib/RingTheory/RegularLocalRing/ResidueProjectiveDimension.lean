/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.Algebra.Category.ModuleCat.MinimalFiniteFreeResolution
public import Aglib.Algebra.Homology.Koszul.LinearPart
public import Aglib.Algebra.Homology.Koszul.Top
public import Aglib.RingTheory.LocalRing.ResidueProjectiveDimensionBound
public import Mathlib.RingTheory.KrullDimension.Regular
public import Mathlib.RingTheory.LocalRing.Module
public import Mathlib.RingTheory.RegularLocalRing.Defs

/-!
# Regularity from finite projective dimension of the residue field

A Noetherian local ring whose residue field has finite projective dimension is
regular in Mathlib's embedding-dimension sense. The Koszul complex on lifts of
a cotangent basis maps into a finite minimal free resolution. The linear part
of its differential makes this comparison injective modulo the maximal ideal,
giving the cotangent-dimension lower bound. The finite projective-dimension
upper bound by Krull dimension then gives regularity.

A projective residue field forces a local ring to be a field even without
Noetherianity. A direct proof for projective dimension at most one is also
retained through the projective maximal ideal.
-/

@[expose] public section

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits IsLocalRing

namespace IsLocalRing

/-- A local ring whose residue field is projective is a field. -/
theorem isField_of_residueField_hasProjectiveDimensionLE_zero
    (R : Type u) [CommRing R] [IsLocalRing R]
    [HasProjectiveDimensionLE (ModuleCat.of R (ResidueField R)) 0] : IsField R := by
  have : Projective (ModuleCat.of R (ResidueField R)) :=
    projective_iff_hasProjectiveDimensionLT_one.mpr inferInstance
  have : Module.Projective R (ResidueField R) :=
    (IsProjective.iff_projective (ResidueField R)).mpr inferInstance
  have : Module.Free R (ResidueField R) := Module.free_of_flat_of_isLocalRing
  apply isField_iff_maximalIdeal_eq.mpr
  rw [← Ideal.annihilator_quotient (I := maximalIdeal R)]
  exact Module.annihilator_eq_bot.mpr (inferInstanceAs (FaithfulSMul R (ResidueField R)))

end IsLocalRing

set_option backward.isDefEq.respectTransparency false in
private theorem exists_chainMap_to_projectiveResolution
    {R : Type u} [CommRing R] (K : ChainComplex (ModuleCat.{u} R) ℕ)
    [∀ i, Projective (K.X i)] (M : ModuleCat.{u} R)
    (ε : K.X 0 ⟶ M) (hε : K.d 1 0 ≫ ε = 0) (Q : ProjectiveResolution M) :
    ∃ α : K ⟶ Q.complex, α.f 0 ≫ Q.π.f 0 = ε := by
  let a₀ := Projective.factorThru ε (Q.π.f 0)
  have ha₀ : a₀ ≫ Q.π.f 0 = ε := Projective.factorThru_comp _ _
  let a₁ := Q.exact₀.liftFromProjective (K.d 1 0 ≫ a₀)
    (by rw [Category.assoc, ha₀, hε])
  have ha₁ : a₁ ≫ Q.complex.d 1 0 = K.d 1 0 ≫ a₀ :=
    Q.exact₀.liftFromProjective_comp _ _
  let α := ChainComplex.mkHom K Q.complex a₀ a₁ ha₁ (fun i ⟨a, a', ha⟩ =>
    ⟨(Q.exact_succ i).liftFromProjective (K.d (i + 2) (i + 1) ≫ a') (by
      rw [Category.assoc, ha, ← Category.assoc, K.d_comp_d, zero_comp]),
      (Q.exact_succ i).liftFromProjective_comp _ _⟩)
  exact ⟨α, ha₀⟩

private theorem split_injective_of_reflects_maximalIdeal
    {R : Type u} [CommRing R] [IsLocalRing R]
    {M N : ModuleCat.{u} R} [Module.Finite R M] [Module.Finite R N] [Module.Free R N]
    (f : M →ₗ[R] N)
    (h : ∀ x, f x ∈ maximalIdeal R • (⊤ : Submodule R N) →
      x ∈ maximalIdeal R • (⊤ : Submodule R M)) :
    ∃ g : N →ₗ[R] M, g.comp f = LinearMap.id := by
  apply (IsLocalRing.split_injective_iff_lTensor_residueField_injective f).mpr
  rw [← LinearMap.ker_eq_bot]
  apply bot_unique
  intro z hz
  obtain ⟨x, rfl⟩ := TensorProduct.mk_surjective R M (ResidueField R)
    Ideal.Quotient.mk_surjective z
  have hx : f x ∈ maximalIdeal R • (⊤ : Submodule R N) := by
    rw [← LinearMap.ker_tensorProductMk]
    change (1 : ResidueField R) ⊗ₜ[R] f x = 0
    simpa using hz
  have hx' := h x hx
  rw [← LinearMap.ker_tensorProductMk] at hx'
  exact hx'

private theorem chainMap_reflects_maximalIdeal
    {R : Type u} [CommRing R] [IsLocalRing R]
    (K F : ChainComplex (ModuleCat.{u} R) ℕ)
    [∀ i, Module.Finite R (K.X i)] [∀ i, Module.Finite R (F.X i)]
    [∀ i, Module.Free R (F.X i)] (α : K ⟶ F)
    (hminimal : ∀ i, LinearMap.range (F.d (i + 1) i).hom ≤
      maximalIdeal R • (⊤ : Submodule R (F.X i)))
    (hlinear : ∀ i (z : K.X (i + 1)),
      K.d (i + 1) i z ∈ maximalIdeal R ^ 2 • (⊤ : Submodule R (K.X i)) →
      z ∈ maximalIdeal R • (⊤ : Submodule R (K.X (i + 1))))
    (hzero : ∀ z : K.X 0, α.f 0 z ∈ maximalIdeal R • (⊤ : Submodule R (F.X 0)) →
      z ∈ maximalIdeal R • (⊤ : Submodule R (K.X 0))) :
    ∀ i (z : K.X i), α.f i z ∈ maximalIdeal R • (⊤ : Submodule R (F.X i)) →
      z ∈ maximalIdeal R • (⊤ : Submodule R (K.X i)) := by
  intro i
  induction i with
  | zero => exact hzero
  | succ i ih =>
    intro z hz
    obtain ⟨g, hg⟩ := split_injective_of_reflects_maximalIdeal (α.f i).hom ih
    apply hlinear i z
    have hdiff : (maximalIdeal R • (⊤ : Submodule R (F.X (i + 1)))).map
        (F.d (i + 1) i).hom ≤ maximalIdeal R ^ 2 • (⊤ : Submodule R (F.X i)) := by
      rw [Submodule.map_smul'', Submodule.map_top, pow_two, Submodule.mul_smul]
      exact smul_mono_right (maximalIdeal R) (hminimal i)
    have hcomm : α.f i (K.d (i + 1) i z) = F.d (i + 1) i (α.f (i + 1) z) :=
      (ConcreteCategory.congr_hom (α.comm (i + 1) i) z).symm
    have himage : α.f i (K.d (i + 1) i z) ∈
        maximalIdeal R ^ 2 • (⊤ : Submodule R (F.X i)) := by
      rw [hcomm]
      exact hdiff (Submodule.mem_map_of_mem hz)
    have hgmem := Submodule.smul_top_le_comap_smul_top (maximalIdeal R ^ 2) g himage
    change g ((α.f i).hom ((K.d (i + 1) i).hom z)) ∈
      maximalIdeal R ^ 2 • (⊤ : Submodule R (K.X i)) at hgmem
    rw [← LinearMap.comp_apply g (α.f i).hom, hg] at hgmem
    exact hgmem

private theorem exists_regular_generator_of_free_ideal
    {R : Type u} [CommRing R] [Nontrivial R] (I : Ideal R) [Module.Free R I]
    (hI : I ≠ ⊥) : ∃ x : R, I = Ideal.span {x} ∧ IsSMulRegular R x := by
  classical
  have : Nontrivial I := Submodule.nontrivial_iff_ne_bot.mpr hI
  let b := Module.Free.chooseBasis R I
  obtain ⟨i⟩ := b.index_nonempty
  have heq (j) : j = i := by
    by_contra hji
    have hcomm : (b j : R) • b i = (b i : R) • b j :=
      Subtype.ext (mul_comm _ _)
    have hz : (b j : R) = 0 := by
      simpa [hji, Ne.symm hji] using congrArg (fun y : I => b.repr y i) hcomm
    exact b.ne_zero j (Subtype.ext hz)
  have hrepr (y : I) : (b.repr y i) • b i = y := by
    apply b.repr.injective
    ext j
    rw [heq j]
    simp
  refine ⟨b i, le_antisymm ?_ ((Ideal.span_singleton_le_iff_mem I).mpr (b i).property), ?_⟩
  · intro y hy
    refine Ideal.mem_span_singleton.mpr ⟨b.repr ⟨y, hy⟩ i, ?_⟩
    simpa [mul_comm] using (congrArg Subtype.val (hrepr ⟨y, hy⟩)).symm
  · apply IsSMulRegular.of_right_eq_zero_of_smul
    intro a ha
    have hz : a • b i = 0 := Subtype.ext (by simpa [mul_comm] using ha)
    simpa using congrArg (fun y : I => b.repr y i) hz

namespace IsRegularLocalRing

/-- The zero-projective-dimension case of the residue-field regularity criterion. -/
theorem of_residueField_hasProjectiveDimensionLE_zero
    (R : Type u) [CommRing R] [IsLocalRing R]
    [HasProjectiveDimensionLE (ModuleCat.of R (ResidueField R)) 0] :
    IsRegularLocalRing R := by
  let := (isField_of_residueField_hasProjectiveDimensionLE_zero R).toField
  infer_instance

/-- A Noetherian local ring whose residue field has projective dimension at
most one is regular local. -/
theorem of_residueField_hasProjectiveDimensionLE_one
    (R : Type u) [CommRing R] [IsLocalRing R] [IsNoetherianRing R]
    [HasProjectiveDimensionLE (ModuleCat.of R (ResidueField R)) 1] :
    IsRegularLocalRing R := by
  let m := maximalIdeal R
  let S := m.mkQ.shortComplexKer
  have hS : S.ShortExact := LinearMap.shortExact_shortComplexKer m.mkQ_surjective
  have hres : HasProjectiveDimensionLT S.X₃ (0 + 2) := by
    change HasProjectiveDimensionLE (ModuleCat.of R (ResidueField R)) 1
    infer_instance
  have : HasProjectiveDimensionLE S.X₁ 0 :=
    (hS.hasProjectiveDimensionLT_X₃_iff 0 inferInstance).mp hres
  have : Projective S.X₁ := projective_iff_hasProjectiveDimensionLT_one.mpr inferInstance
  have : Module.Projective R (LinearMap.ker m.mkQ) :=
    (IsProjective.iff_projective (LinearMap.ker m.mkQ)).mpr inferInstance
  have : Module.Projective R m := Module.Projective.of_equiv
    (LinearEquiv.ofEq _ _ (Submodule.ker_mkQ m))
  have : Module.Free R m := Module.free_of_flat_of_isLocalRing
  by_cases hm : m = ⊥
  · let := (isField_iff_maximalIdeal_eq.mpr hm).toField
    infer_instance
  obtain ⟨x, hx, hreg⟩ := exists_regular_generator_of_free_ideal m hm
  have hxm : x ∈ maximalIdeal R := by
    change x ∈ m
    rw [hx]
    exact Ideal.subset_span (Set.mem_singleton x)
  have hproper : Ideal.span {x} ≠ ⊤ := by
    rw [← hx]
    exact (maximalIdeal.isMaximal R).ne_top
  have : Nontrivial (R ⧸ Ideal.span {x}) := Ideal.Quotient.nontrivial_iff.mpr hproper
  have hdim : (1 : WithBot ℕ∞) ≤ ringKrullDim R := by
    rw [← ringKrullDim_quotient_span_singleton_succ_eq_ringKrullDim hreg hxm]
    simpa [add_comm] using add_le_add_right
      (ringKrullDim_nonneg_of_nontrivial (R := R ⧸ Ideal.span {x})) 1
  apply of_spanFinrank_maximalIdeal_le
  apply le_trans (b := (1 : WithBot ℕ∞)) ?_ hdim
  have hspan : m.spanFinrank ≤ 1 := by
    rw [hx]
    simpa using Submodule.spanFinrank_span_le_ncard_of_finite (Set.finite_singleton x)
  exact_mod_cast hspan

end IsRegularLocalRing

set_option backward.isDefEq.respectTransparency false in
private theorem cotangent_family_length_le_bound
    {R : Type u} [CommRing R] [IsLocalRing R] [IsNoetherianRing R]
    {e : ℕ} (f : Fin e → maximalIdeal R)
    (hlin : LinearIndependent (ResidueField R)
      (fun j => (maximalIdeal R).toCotangent (f j)))
    (n : ℕ) [HasProjectiveDimensionLE (ModuleCat.of R (ResidueField R)) n] :
    e ≤ n := by
  let s : List R := List.ofFn (fun j => (f j : R))
  let K := ChainComplex.Koszul.chainComplex s
  obtain ⟨Q, hfinite, hfree, hbound, hminimal⟩ :=
    ModuleCat.exists_minimal_finite_free_resolution
      (ModuleCat.of R (ResidueField R)) n
  have (i : ℕ) : Module.Finite R (Q.complex.X i) := hfinite i
  have (i : ℕ) : Module.Free R (Q.complex.X i) := hfree i
  let ε : K.X 0 ⟶ ModuleCat.of R (ResidueField R) :=
    (ChainComplex.Koszul.zeroComponentIso s).hom ≫
      ModuleCat.ofHom (maximalIdeal R).mkQ
  have hε : K.d 1 0 ≫ ε = 0 := by
    change K.d 1 0 ≫ ((ChainComplex.Koszul.zeroComponentIso s).hom ≫
      ModuleCat.ofHom (maximalIdeal R).mkQ) = 0
    rw [← Category.assoc]
    apply (ChainComplex.Koszul.boundaryIdeal_le_iff s (maximalIdeal R)).mp
    rw [ChainComplex.Koszul.boundaryIdeal_eq_ofList]
    apply Ideal.span_le.mpr
    intro x hx
    obtain ⟨j, rfl⟩ := List.mem_ofFn.mp hx
    exact (f j).property
  obtain ⟨α, hα⟩ := exists_chainMap_to_projectiveResolution K
    (ModuleCat.of R (ResidueField R)) ε hε Q
  have hkill : maximalIdeal R • (⊤ : Submodule R (Q.complex.X 0)) ≤
      LinearMap.ker (Q.π.f 0).hom := by
    apply Submodule.smul_le.mpr
    intro r hr y _
    change (Q.π.f 0).hom (r • y) = 0
    rw [map_smul]
    have hrk : r ∈ Module.annihilator R (ResidueField R) := by
      change r ∈ Module.annihilator R (R ⧸ maximalIdeal R)
      rwa [Ideal.annihilator_quotient]
    exact Module.mem_annihilator.mp hrk _
  have hzero (z : K.X 0)
      (hz : α.f 0 z ∈ maximalIdeal R • (⊤ : Submodule R (Q.complex.X 0))) :
      z ∈ maximalIdeal R • (⊤ : Submodule R (K.X 0)) := by
    have hεz : ε z = 0 := by
      rw [← hα]
      exact hkill hz
    have hzR : (ChainComplex.Koszul.zeroComponentIso s).hom z ∈ maximalIdeal R :=
      (Submodule.Quotient.mk_eq_zero _).mp hεz
    have hzR' : (ChainComplex.Koszul.zeroComponentIso s).hom z ∈
        maximalIdeal R • (⊤ : Submodule R R) := by
      simpa [smul_eq_mul] using hzR
    have hzinv := Submodule.smul_top_le_comap_smul_top (maximalIdeal R)
      (ChainComplex.Koszul.zeroComponentIso s).inv.hom hzR'
    simpa using hzinv
  have hreflect := chainMap_reflects_maximalIdeal K Q.complex α hminimal
    (ChainComplex.Koszul.mem_maximalIdeal_smul_top_of_d_mem_sq f hlin) hzero
  by_contra hle
  have hlt : n < s.length := by simpa [s] using Nat.lt_of_not_ge hle
  let z : K.X s.length := (ChainComplex.Koszul.topComponentIso s).inv (1 : R)
  have hαz : α.f s.length z = 0 := by
    have : Subsingleton (Q.complex.X s.length) :=
      ModuleCat.isZero_iff_subsingleton.mp (hbound s.length hlt)
    exact Subsingleton.elim _ _
  have hzm : z ∈ maximalIdeal R • (⊤ : Submodule R (K.X s.length)) :=
    hreflect s.length z (by rw [hαz]; exact Submodule.zero_mem _)
  have hzR := Submodule.smul_top_le_comap_smul_top (maximalIdeal R)
    (ChainComplex.Koszul.topComponentIso s).hom.hom hzm
  simp [z, smul_eq_mul] at hzR

namespace IsLocalRing

private theorem finrank_cotangentSpace_le_of_residueField_hasProjectiveDimensionLE
    (R : Type u) [CommRing R] [IsLocalRing R] [IsNoetherianRing R]
    (n : ℕ) [HasProjectiveDimensionLE (ModuleCat.of R (ResidueField R)) n] :
    Module.finrank (ResidueField R) (CotangentSpace R) ≤ n := by
  let b := Module.finBasis (ResidueField R) (CotangentSpace R)
  choose f hf using fun j => (maximalIdeal R).toCotangent_surjective (b j)
  have hlin : LinearIndependent (ResidueField R)
      (fun j => (maximalIdeal R).toCotangent (f j)) := by
    simpa only [hf] using b.linearIndependent
  exact cotangent_family_length_le_bound f hlin n

/-- The cotangent-space dimension is at most the projective dimension of
the residue field, including infinite projective dimension. -/
@[stacks 00OA]
theorem finrank_cotangentSpace_le_residueField_projectiveDimension
    (R : Type u) [CommRing R] [IsLocalRing R] [IsNoetherianRing R] :
    (Module.finrank (ResidueField R) (CotangentSpace R) : WithBot ℕ∞) ≤
      projectiveDimension (ModuleCat.of R (ResidueField R)) := by
  rw [projectiveDimension_ge_iff]
  intro hlt
  cases hd : Module.finrank (ResidueField R) (CotangentSpace R) with
  | zero =>
    have : HasProjectiveDimensionLT (ModuleCat.of R (ResidueField R)) 0 := by
      simpa only [hd] using hlt
    have hz : IsZero (ModuleCat.of R (ResidueField R)) :=
      (hasProjectiveDimensionLT_zero_iff_isZero _).mp inferInstance
    have : Subsingleton (ResidueField R) := ModuleCat.isZero_iff_subsingleton.mp hz
    exact (zero_ne_one : (0 : ResidueField R) ≠ 1) (Subsingleton.elim _ _)
  | succ d =>
    have : HasProjectiveDimensionLE (ModuleCat.of R (ResidueField R)) d := by
      simpa only [hd] using hlt
    have hbound := finrank_cotangentSpace_le_of_residueField_hasProjectiveDimensionLE R d
    omega

end IsLocalRing

namespace IsRegularLocalRing

/-- A Noetherian local ring whose residue field has finite projective
dimension is regular local in the embedding-dimension sense. -/
@[stacks 00OC "(1) implies (3)"]
theorem of_residueField_hasProjectiveDimensionLE
    (R : Type u) [CommRing R] [IsLocalRing R] [IsNoetherianRing R]
    (n : ℕ) [HasProjectiveDimensionLE (ModuleCat.of R (ResidueField R)) n] :
    IsRegularLocalRing R := by
  apply of_spanFinrank_maximalIdeal_le
  rw [spanFinrank_maximalIdeal_eq_finrank_cotangentSpace]
  exact (finrank_cotangentSpace_le_residueField_projectiveDimension R).trans
    (ModuleCat.residueField_projectiveDimension_le_ringKrullDim R n)

end IsRegularLocalRing
