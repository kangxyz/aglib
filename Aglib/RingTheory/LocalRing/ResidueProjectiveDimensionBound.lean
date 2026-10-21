/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.RingTheory.Regular.QuotientProjectiveDimension
public import Aglib.Algebra.Category.ModuleCat.MinimalFiniteFreeResolution
public import Mathlib.RingTheory.Regular.Free
public import Mathlib.RingTheory.Regular.LinearMap
public import Mathlib.RingTheory.KrullDimension.NonZeroDivisors

/-!
# Finite projective dimension over Noetherian local rings

A finite module of finite projective dimension can be reduced modulo an
element regular on the ring and the module without increasing its projective
dimension over the quotient ring. Together with the minimal-cover argument
when the ring has nonzero socle, dimension induction bounds the actual
projective dimension of every finite module of finite projective dimension
by the ring's Krull dimension. The residue-field case is Stacks 00OB.
-/

@[expose] public section

noncomputable section

universe u

open CategoryTheory IsLocalRing
open scoped Pointwise TensorProduct nonZeroDivisors

namespace ModuleCat

variable {R : Type u} [CommRing R]

private def quotSMulShortComplex (x : R) (T : ShortComplex (ModuleCat.{u} R)) :
    ShortComplex (ModuleCat.{u} (R ⧸ Ideal.span {x})) :=
  ShortComplex.moduleCatMk
    ((QuotSMulTop.map x T.f.hom).extendScalarsOfSurjective Ideal.Quotient.mk_surjective)
    ((QuotSMulTop.map x T.g.hom).extendScalarsOfSurjective Ideal.Quotient.mk_surjective)
    (by
      apply LinearMap.restrictScalars_injective R
      change (QuotSMulTop.map x T.g.hom).comp (QuotSMulTop.map x T.f.hom) = 0
      rw [← QuotSMulTop.map_comp]
      have hcomp : T.g.hom.comp T.f.hom = 0 := by
        ext y
        exact T.moduleCat_zero_apply y
      rw [hcomp, map_zero])

private theorem quotSMul_map_injective (x : R) (T : ShortComplex (ModuleCat.{u} R))
    (hT : T.ShortExact) (hreg : IsSMulRegular T.X₃ x) :
    Function.Injective (QuotSMulTop.map x T.f.hom) := by
  apply LinearMap.ker_eq_bot.mp
  apply (Submodule.eq_bot_iff _).mpr
  intro y hy
  change QuotSMulTop.map x T.f.hom y = 0 at hy
  change y = 0
  induction y using Submodule.Quotient.induction_on with | _ y =>
  change (Submodule.Quotient.mk (T.f y) : QuotSMulTop x T.X₂) = 0 at hy
  have hy' : T.f y ∈ x • (⊤ : Submodule R T.X₂) :=
    (Submodule.Quotient.mk_eq_zero _).mp hy
  obtain ⟨z, _, hz⟩ := (Submodule.mem_smul_pointwise_iff_exists _ _ _).mp hy'
  have hzker : T.g z = 0 := hreg.right_eq_zero_of_smul (by
    rw [← map_smul, hz]
    exact T.moduleCat_zero_apply y)
  obtain ⟨w, hw⟩ := (T.moduleCat_exact_iff.mp hT.exact) z hzker
  have hyw : y = x • w := hT.moduleCat_injective_f (by
    rw [map_smul, hw]
    exact hz.symm)
  apply (Submodule.Quotient.mk_eq_zero _).mpr
  rw [hyw]
  exact Submodule.smul_mem_pointwise_smul w x ⊤ trivial

private theorem quotSMulShortComplex_shortExact (x : R)
    (T : ShortComplex (ModuleCat.{u} R)) (hT : T.ShortExact)
    (hreg : IsSMulRegular T.X₃ x) : (quotSMulShortComplex x T).ShortExact where
  exact := by
    apply (ShortComplex.ShortExact.moduleCat_exact_iff_function_exact _).mpr
    change Function.Exact (QuotSMulTop.map x T.f.hom) (QuotSMulTop.map x T.g.hom)
    exact QuotSMulTop.map_exact x
      ((ShortComplex.ShortExact.moduleCat_exact_iff_function_exact T).mp hT.exact)
      hT.moduleCat_surjective_g
  mono_f := by
    apply (ModuleCat.mono_iff_injective _).mpr
    exact quotSMul_map_injective x T hT hreg
  epi_g := by
    apply (ModuleCat.epi_iff_surjective _).mpr
    exact QuotSMulTop.map_surjective x hT.moduleCat_surjective_g

/-- Reducing modulo an element regular on both ring and module preserves any
finite projective-dimension bound over the actual principal quotient ring. -/
theorem hasProjectiveDimensionLE_quotSMulTop_of_isSMulRegular
    [IsLocalRing R] [IsNoetherianRing R] (x : R) (hx : IsSMulRegular R x)
    (M : ModuleCat.{u} R) [Module.Finite R M] (hM : IsSMulRegular M x)
    (n : ℕ) [HasProjectiveDimensionLE M n] :
    HasProjectiveDimensionLE (ModuleCat.of (R ⧸ Ideal.span {x}) (QuotSMulTop x M)) n := by
  induction n generalizing M with
  | zero =>
    have : Projective M := (projective_iff_hasProjectiveDimensionLE_zero M).mpr inferInstance
    have : Module.Free R M := Module.free_of_flat_of_isLocalRing
    exact (projective_iff_hasProjectiveDimensionLE_zero _).mp inferInstance
  | succ n ih =>
    obtain ⟨P, _, _, _, _, p, hp⟩ := Module.exists_finite_presentation R M
    let T := p.shortComplexKer
    have hT : T.ShortExact := LinearMap.shortExact_shortComplexKer hp
    have : Module.Finite R T.X₁ := inferInstanceAs (Module.Finite R (LinearMap.ker p))
    have hP : IsSMulRegular P x :=
      ((TensorProduct.rid R P).isSMulRegular_congr x).mp (hx.lTensor P)
    have hK : IsSMulRegular T.X₁ x := IsSMulRegular.submodule (LinearMap.ker p) x hP
    have : HasProjectiveDimensionLE T.X₁ n :=
      (hT.hasProjectiveDimensionLT_X₃_iff n inferInstance).mp inferInstance
    let TQ := quotSMulShortComplex x T
    have hTQ : TQ.ShortExact := quotSMulShortComplex_shortExact x T hT hM
    have hPQ : Projective TQ.X₂ := by
      change Projective (ModuleCat.of (R ⧸ Ideal.span {x}) (QuotSMulTop x P))
      infer_instance
    have hKQ : HasProjectiveDimensionLE TQ.X₁ n := ih T.X₁ hK
    exact (hTQ.hasProjectiveDimensionLT_X₃_iff n hPQ).mpr hKQ

private theorem exists_nonzero_socle_of_not_exists_regular
    [IsLocalRing R] [IsNoetherianRing R]
    (h : ¬ ∃ x ∈ maximalIdeal R, IsSMulRegular R x) :
    ∃ r : R, r ≠ 0 ∧ ∀ x ∈ maximalIdeal R, x * r = 0 := by
  have hn : ¬ Subsingleton (ResidueField R →ₗ[R] R) := by
    intro hh
    obtain ⟨x, hx, hreg⟩ := IsSMulRegular.subsingleton_linearMap_iff.mp hh
    have hxm : x ∈ maximalIdeal R := by
      change x ∈ Module.annihilator R (R ⧸ maximalIdeal R) at hx
      rwa [Ideal.annihilator_quotient] at hx
    exact h ⟨x, hxm, hreg⟩
  have : Nontrivial (ResidueField R →ₗ[R] R) := not_subsingleton_iff_nontrivial.mp hn
  obtain ⟨g, hg⟩ := exists_ne (0 : ResidueField R →ₗ[R] R)
  obtain ⟨a, ha⟩ := DFunLike.ne_iff.mp hg
  refine ⟨g a, ha, ?_⟩
  intro x hx
  change x • g a = 0
  rw [← g.map_smul]
  have hxann : x ∈ Module.annihilator R (ResidueField R) := by
    change x ∈ Module.annihilator R (R ⧸ maximalIdeal R)
    rwa [Ideal.annihilator_quotient]
  rw [Module.mem_annihilator.mp hxann a, map_zero]

private theorem projective_of_finite_dimension_of_nonzero_socle
    [IsLocalRing R] [IsNoetherianRing R] (r : R) (hr : r ≠ 0)
    (hann : ∀ x ∈ maximalIdeal R, x * r = 0)
    (M : ModuleCat.{u} R) [Module.Finite R M]
    (n : ℕ) [HasProjectiveDimensionLE M n] : Projective M := by
  induction n generalizing M with
  | zero => exact (projective_iff_hasProjectiveDimensionLE_zero M).mpr inferInstance
  | succ n ih =>
    obtain ⟨P, _, _, p, hp, hminimal⟩ := exists_minimal_finite_free_cover M
    let T := p.hom.shortComplexKer
    have hT : T.ShortExact := LinearMap.shortExact_shortComplexKer hp
    have : Module.Finite R T.X₁ :=
      inferInstanceAs (Module.Finite R (LinearMap.ker p.hom))
    have : HasProjectiveDimensionLE T.X₁ n :=
      (hT.hasProjectiveDimensionLT_X₃_iff n inferInstance).mp inferInstance
    have : Projective T.X₁ := ih T.X₁
    have : Module.Projective R T.X₁ := ModuleCat.projective_of_module_projective T.X₁
    have : Module.Free R T.X₁ := Module.free_of_flat_of_isLocalRing
    have hzero : Subsingleton T.X₁ := by
      by_contra hn
      have : Nontrivial T.X₁ := not_subsingleton_iff_nontrivial.mp hn
      have hle : maximalIdeal R • (⊤ : Submodule R P) ≤
          LinearMap.ker (LinearMap.lsmul R P r) := by
        apply Submodule.smul_le.mpr
        intro x hx y _
        change r • (x • y) = 0
        rw [smul_smul, mul_comm r x, hann x hx, zero_smul]
      have hrann : r ∈ Module.annihilator R T.X₁ := by
        apply Module.mem_annihilator.mpr
        intro y
        apply Subtype.val_injective
        exact hle (hminimal y.property)
      rw [Module.annihilator_eq_bot.mpr (inferInstanceAs (FaithfulSMul R T.X₁)),
        Submodule.mem_bot] at hrann
      exact hr hrann
    have hpbij : Function.Bijective p.hom :=
      ⟨LinearMap.ker_eq_bot.mp (Submodule.subsingleton_iff_eq_bot.mp hzero), hp⟩
    have : Module.Free R M := Module.Free.of_equiv (LinearEquiv.ofBijective p.hom hpbij)
    infer_instance

private theorem hasProjectiveDimensionLE_of_krullDim_le (d : ℕ)
    (R : Type u) [CommRing R] [IsLocalRing R] [IsNoetherianRing R]
    (M : ModuleCat.{u} R) [Module.Finite R M]
    (n : ℕ) [HasProjectiveDimensionLE M n]
    (hd : ringKrullDim R ≤ (d : ℕ)) : HasProjectiveDimensionLE M d := by
  induction d generalizing R n with
  | zero =>
    have hn : ¬ ∃ x ∈ maximalIdeal R, IsSMulRegular R x := by
      rintro ⟨x, hx, hreg⟩
      have hproper : Ideal.span {x} ≠ ⊤ := ne_top_of_le_ne_top
        (maximalIdeal.isMaximal R).ne_top ((Ideal.span_singleton_le_iff_mem _).mpr hx)
      have : Nontrivial (R ⧸ Ideal.span {x}) := Ideal.Quotient.nontrivial_iff.mpr hproper
      have hxnd : x ∈ R⁰ := mem_nonZeroDivisors_iff_left.mpr fun a ha =>
        hreg (by simpa only [smul_eq_mul, mul_zero] using ha)
      have hdrop := ringKrullDim_quotient_succ_le_of_nonZeroDivisor hxnd
      have hpos : (1 : WithBot ℕ∞) ≤ ringKrullDim R := by
        calc
          (1 : WithBot ℕ∞) ≤ ringKrullDim (R ⧸ Ideal.span {x}) + 1 := by
            simpa only [add_zero, zero_add, add_comm] using add_le_add_right
              (ringKrullDim_nonneg_of_nontrivial (R := R ⧸ Ideal.span {x})) 1
          _ ≤ ringKrullDim R := hdrop
      have := hpos.trans hd
      norm_num at this
    obtain ⟨r, hr, hann⟩ := exists_nonzero_socle_of_not_exists_regular hn
    have : Projective M := projective_of_finite_dimension_of_nonzero_socle r hr hann M n
    exact (projective_iff_hasProjectiveDimensionLE_zero M).mp inferInstance
  | succ d ih =>
    by_cases hregular : ∃ x ∈ maximalIdeal R, IsSMulRegular R x
    · obtain ⟨x, hx, hxreg⟩ := hregular
      cases n with
      | zero =>
        exact hasProjectiveDimensionLT_of_ge M 1 (d + 2) (by omega)
      | succ n =>
        let Q := R ⧸ Ideal.span {x}
        have hproper : Ideal.span {x} ≠ ⊤ := ne_top_of_le_ne_top
          (maximalIdeal.isMaximal R).ne_top ((Ideal.span_singleton_le_iff_mem _).mpr hx)
        have : Nontrivial Q := Ideal.Quotient.nontrivial_iff.mpr hproper
        have : IsLocalRing Q := IsLocalRing.of_surjective'
          (Ideal.Quotient.mk (Ideal.span {x})) Ideal.Quotient.mk_surjective
        have : IsNoetherianRing Q := isNoetherianRing_of_surjective R Q
          (Ideal.Quotient.mk (Ideal.span {x})) Ideal.Quotient.mk_surjective
        have hxnd : x ∈ R⁰ := mem_nonZeroDivisors_iff_left.mpr fun a ha =>
          hxreg (by simpa only [smul_eq_mul, mul_zero] using ha)
        have hdQ : ringKrullDim Q ≤ (d : ℕ) := by
          apply ENat.WithBot.add_le_add_one_right_iff.mp
          simpa only [Nat.cast_add, Nat.cast_one] using
            (ringKrullDim_quotient_succ_le_of_nonZeroDivisor hxnd).trans hd
        obtain ⟨P, _, _, _, _, p, hp⟩ := Module.exists_finite_presentation R M
        let T := p.shortComplexKer
        have hT : T.ShortExact := LinearMap.shortExact_shortComplexKer hp
        have : Module.Finite R T.X₁ := inferInstanceAs (Module.Finite R (LinearMap.ker p))
        have : HasProjectiveDimensionLE T.X₁ n :=
          (hT.hasProjectiveDimensionLT_X₃_iff n inferInstance).mp inferInstance
        have hP : IsSMulRegular P x :=
          ((TensorProduct.rid R P).isSMulRegular_congr x).mp (hxreg.lTensor P)
        have hK : IsSMulRegular T.X₁ x := IsSMulRegular.submodule (LinearMap.ker p) x hP
        let N := ModuleCat.of Q (QuotSMulTop x T.X₁)
        have : Module.Finite Q N :=
          Module.Finite.of_restrictScalars_finite R Q (QuotSMulTop x T.X₁)
        have : HasProjectiveDimensionLE N n :=
          hasProjectiveDimensionLE_quotSMulTop_of_isSMulRegular x hxreg T.X₁ hK n
        have : HasProjectiveDimensionLE N d := ih Q N n hdQ
        let F := ModuleCat.restrictScalars (Ideal.Quotient.mk (Ideal.span {x}))
        have : HasProjectiveDimensionLE (F.obj N) (d + 1) :=
          hasProjectiveDimensionLE_restrictScalars_quotient x hx hxreg N d
        let e : F.obj N ≃ₗ[R] QuotSMulTop x T.X₁ :=
          { toFun := id
            invFun := id
            left_inv := fun _ => rfl
            right_inv := fun _ => rfl
            map_add' := fun _ _ => rfl
            map_smul' := fun a m =>
              IsScalarTower.algebraMap_smul (M := QuotSMulTop x T.X₁) Q a m }
        have hquot : projectiveDimension (ModuleCat.of R (QuotSMulTop x T.X₁)) ≤
            (d + 1 : ℕ) := by
          rw [← projectiveDimension_eq_of_linearEquiv
            (M := F.obj N) (N := ModuleCat.of R (QuotSMulTop x T.X₁)) e]
          exact (projectiveDimension_le_iff _ _).mpr inferInstance
        rw [projectiveDimension_quotSMulTop_eq_succ_of_isSMulRegular T.X₁ x hK hx] at hquot
        have hKdim : projectiveDimension T.X₁ ≤ (d : ℕ) := by
          apply (ENat.WithBot.add_le_add_natCast_right_iff (c := 1)).mp
          simpa only [Nat.cast_add, Nat.cast_one] using hquot
        have hKd : HasProjectiveDimensionLE T.X₁ d :=
          (projectiveDimension_le_iff _ _).mp hKdim
        exact (hT.hasProjectiveDimensionLT_X₃_iff d inferInstance).mpr hKd
    · obtain ⟨r, hr, hann⟩ := exists_nonzero_socle_of_not_exists_regular hregular
      have : Projective M := projective_of_finite_dimension_of_nonzero_socle r hr hann M n
      exact hasProjectiveDimensionLT_of_ge M 1 (d + 2) (by omega)

/-- The actual projective dimension of a finite module of finite projective
dimension is at most the Krull dimension of its Noetherian local ring. The
supplied finite bound need not itself be at most the Krull dimension. -/
theorem projectiveDimension_le_ringKrullDim_of_finite
    [IsLocalRing R] [IsNoetherianRing R] (M : ModuleCat.{u} R) [Module.Finite R M]
    (n : ℕ) [HasProjectiveDimensionLE M n] : projectiveDimension M ≤ ringKrullDim R := by
  generalize hd : ringKrullDim R = d
  induction d with
  | bot =>
    have := ringKrullDim_nonneg_of_nontrivial (R := R)
    rw [hd] at this
    simp at this
  | coe d =>
    induction d with
    | top => exact le_top
    | coe d =>
      exact (projectiveDimension_le_iff M d).mpr
        (hasProjectiveDimensionLE_of_krullDim_le d R M n
          (by simpa only [WithBot.coe_natCast] using hd.le))

/-- Stacks 00OB: finite projective dimension of the actual residue field
bounds its actual projective dimension by the ring's Krull dimension. -/
theorem residueField_projectiveDimension_le_ringKrullDim
    (R : Type u) [CommRing R] [IsLocalRing R] [IsNoetherianRing R]
    (n : ℕ) [HasProjectiveDimensionLE (ModuleCat.of R (ResidueField R)) n] :
    projectiveDimension (ModuleCat.of R (ResidueField R)) ≤ ringKrullDim R :=
  projectiveDimension_le_ringKrullDim_of_finite _ n

end ModuleCat
