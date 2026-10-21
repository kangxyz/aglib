/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Mathlib.Algebra.Category.ModuleCat.ProjectiveDimension
public import Mathlib.Algebra.Homology.Augment
public import Mathlib.CategoryTheory.Abelian.Projective.Resolution
public import Mathlib.RingTheory.LocalRing.Module

/-!
# Minimal finite free covers over local rings

Lifting a residue-field basis gives a finite free cover whose kernel is
contained in the maximal ideal times its source. This is the first step in
the construction of finite minimal free resolutions and is also useful for
projective-dimension bounds in depth zero.
-/

@[expose] public section

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits IsLocalRing TensorProduct

namespace ModuleCat

/-- A finite module over a local ring has a finite free cover whose kernel
is contained in the maximal ideal times the source. -/
theorem exists_minimal_finite_free_cover
    {R : Type u} [CommRing R] [IsLocalRing R]
    (M : ModuleCat.{u} R) [Module.Finite R M] :
    ∃ (P : ModuleCat.{u} R) (_ : Module.Free R P) (_ : Module.Finite R P)
      (p : P ⟶ M), Function.Surjective p.hom ∧
        LinearMap.ker p.hom ≤ maximalIdeal R • (⊤ : Submodule R P) := by
  classical
  let k := ResidueField R
  let b := Module.Free.chooseBasis k (k ⊗[R] M)
  let ι := Module.Free.ChooseBasisIndex k (k ⊗[R] M)
  have : Finite ι := Module.Finite.finite_basis b
  let : Fintype ι := Fintype.ofFinite ι
  obtain ⟨v, hv⟩ := (TensorProduct.mk_surjective R M k Ideal.Quotient.mk_surjective).comp_left b
  let p := Finsupp.linearCombination R v
  have hp : Function.Surjective p := by
    rw [← LinearMap.range_eq_top, Finsupp.range_linearCombination]
    exact IsLocalRing.span_eq_top_of_tmul_eq_basis v b (congr_fun hv)
  have hbase : Function.Bijective (p.baseChange k) := by
    have hsurj : Function.Surjective (p.baseChange k) := p.lTensor_surjective k hp
    refine ⟨?_, hsurj⟩
    rw [← LinearMap.ker_eq_bot (M := k ⊗[R] (ι →₀ R)) (f := p.baseChange k),
      ← Submodule.finrank_eq_zero (R := k) (M := k ⊗[R] (ι →₀ R)),
      ← Nat.add_right_inj (n := Module.finrank k (LinearMap.range (p.baseChange k))),
      LinearMap.finrank_range_add_finrank_ker (V := k ⊗[R] (ι →₀ R)),
      LinearMap.range_eq_top.mpr hsurj, finrank_top]
    simp only [Module.finrank_tensorProduct, Module.finrank_self,
      Module.finrank_finsupp_self, one_mul, add_zero]
    rw [Module.finrank_eq_card_basis b]
  refine ⟨ModuleCat.of R (ι →₀ R), inferInstance, inferInstance, ModuleCat.ofHom p, hp, ?_⟩
  intro y hy
  rw [← LinearMap.ker_tensorProductMk]
  change (1 : k) ⊗ₜ[R] y = 0
  apply hbase.injective
  simpa using congrArg (fun z : M => (1 : k) ⊗ₜ[R] z) hy

set_option backward.isDefEq.respectTransparency false in
private def prependComplex
    {R : Type u} [CommRing R] {M P : ModuleCat.{u} R} (p : P ⟶ M)
    (Q : ProjectiveResolution (ModuleCat.of R (LinearMap.ker p.hom))) :
    ChainComplex (ModuleCat.{u} R) ℕ :=
  Q.complex.augment
    (Q.π.f 0 ≫ ModuleCat.ofHom (LinearMap.ker p.hom).subtype)
    (by rw [← Category.assoc, Q.complex_d_comp_π_f_zero, zero_comp])

set_option backward.isDefEq.respectTransparency false in
private def prependResolution
    {R : Type u} [CommRing R] {M P : ModuleCat.{u} R} (p : P ⟶ M)
    (hp : Function.Surjective p.hom) [Projective P]
    (Q : ProjectiveResolution (ModuleCat.of R (LinearMap.ker p.hom))) :
    ProjectiveResolution M := by
  let K := prependComplex p Q
  have hw : K.d 1 0 ≫ p = 0 := by
    apply ModuleCat.hom_ext
    ext y
    exact (Q.π.f 0 y).property
  let π : K ⟶ (ChainComplex.single₀ (ModuleCat.{u} R)).obj M :=
    (ChainComplex.toSingle₀Equiv _ _).symm ⟨p, hw⟩
  have hzero : (ShortComplex.mk (K.d 1 0) p hw).Exact := by
    rw [ShortComplex.moduleCat_exact_iff]
    intro x hx
    obtain ⟨y, hy⟩ := (ModuleCat.epi_iff_surjective (Q.π.f 0)).mp inferInstance
      (⟨x, hx⟩ : LinearMap.ker p.hom)
    exact ⟨y, congrArg Subtype.val hy⟩
  have hexact (i : ℕ) : K.ExactAt (i + 1) := by
    rw [HomologicalComplex.exactAt_iff' _ (i + 2) (i + 1) i (by simp) (by simp)]
    cases i with
    | zero =>
      rw [ShortComplex.moduleCat_exact_iff]
      intro x hx
      have hx' : Q.π.f 0 x = 0 := by
        apply Subtype.ext
        exact hx
      exact (ShortComplex.moduleCat_exact_iff _).mp Q.exact₀ x hx'
    | succ i =>
      exact Q.exact_succ i
  refine
    { complex := K
      projective := fun i => ?_
      π := π
      quasiIso := ⟨fun i => ?_⟩ }
  · cases i with
    | zero => exact inferInstanceAs (Projective P)
    | succ i => exact Q.projective i
  · cases i with
    | zero =>
      rw [ChainComplex.quasiIsoAt₀_iff, ShortComplex.quasiIso_iff_of_zeros']
      · exact ⟨hzero, (ModuleCat.epi_iff_surjective p).mpr hp⟩
      · exact K.shape 0 0 (by simp)
      · rfl
      · rfl
    | succ i =>
      rw [quasiIsoAt_iff_exactAt' π (i + 1)
        (ChainComplex.exactAt_succ_single_obj _ _)]
      exact hexact i

/-- A finite module of projective dimension at most `n` over a Noetherian
local ring has a finite free projective resolution, zero above `n`, with every
differential taking values in the maximal ideal times its target. -/
theorem exists_minimal_finite_free_resolution
    {R : Type u} [CommRing R] [IsLocalRing R] [IsNoetherianRing R]
    (M : ModuleCat.{u} R) [Module.Finite R M] (n : ℕ) [HasProjectiveDimensionLE M n] :
    ∃ Q : ProjectiveResolution M,
      (∀ i, Module.Finite R (Q.complex.X i)) ∧
      (∀ i, Module.Free R (Q.complex.X i)) ∧
      (∀ i, n < i → CategoryTheory.Limits.IsZero (Q.complex.X i)) ∧
      ∀ i, LinearMap.range (Q.complex.d (i + 1) i).hom ≤
        maximalIdeal R • (⊤ : Submodule R (Q.complex.X i)) := by
  induction n generalizing M with
  | zero =>
    have : Projective M := projective_iff_hasProjectiveDimensionLT_one.mpr inferInstance
    have : Module.Free R M := Module.free_of_flat_of_isLocalRing
    let Q := ProjectiveResolution.self M
    have hz (i : ℕ) : CategoryTheory.Limits.IsZero (Q.complex.X (i + 1)) :=
      HomologicalComplex.isZero_single_obj_X _ _ _ _ (by simp)
    refine ⟨Q, ?_, ?_, ?_, ?_⟩
    · intro i
      cases i with
      | zero => exact inferInstanceAs (Module.Finite R M)
      | succ i =>
        have : Subsingleton (Q.complex.X (i + 1)) := ModuleCat.isZero_iff_subsingleton.mp (hz i)
        infer_instance
    · intro i
      cases i with
      | zero => exact inferInstanceAs (Module.Free R M)
      | succ i =>
        have : Subsingleton (Q.complex.X (i + 1)) := ModuleCat.isZero_iff_subsingleton.mp (hz i)
        infer_instance
    · intro i hi
      cases i with
      | zero => omega
      | succ i => exact hz i
    · intro i
      rw [(hz i).eq_zero_of_src (Q.complex.d (i + 1) i)]
      simp
  | succ n ih =>
    obtain ⟨P, hfree, hfinite, p, hp, hminimal⟩ := exists_minimal_finite_free_cover M
    let S := p.hom.shortComplexKer
    have hS : S.ShortExact := LinearMap.shortExact_shortComplexKer hp
    have : HasProjectiveDimensionLE S.X₁ n :=
      (hS.hasProjectiveDimensionLT_X₃_iff n inferInstance).mp inferInstance
    have : Module.Finite R S.X₁ := inferInstanceAs (Module.Finite R (LinearMap.ker p.hom))
    obtain ⟨Q, hQfinite, hQfree, hQzero, hQminimal⟩ := ih S.X₁
    let T := prependResolution p hp Q
    refine ⟨T, ?_, ?_, ?_, ?_⟩
    · intro i
      cases i with
      | zero => exact hfinite
      | succ i => exact hQfinite i
    · intro i
      cases i with
      | zero => exact hfree
      | succ i => exact hQfree i
    · intro i hi
      cases i with
      | zero => omega
      | succ i => exact hQzero i (by omega)
    · intro i
      cases i with
      | zero =>
        rintro _ ⟨y, rfl⟩
        exact hminimal (Q.π.f 0 y).property
      | succ i => exact hQminimal i

end ModuleCat
