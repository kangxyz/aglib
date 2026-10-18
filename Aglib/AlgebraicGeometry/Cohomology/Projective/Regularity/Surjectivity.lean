/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Cohomology.Projective.Regularity.KoszulExact
public import Aglib.AlgebraicGeometry.Cohomology.Projective.Regularity.Monotone
public import Aglib.AlgebraicGeometry.Modules.Generators.GlobalSections

/-!
# Multiplication by the coordinates is surjective on global sections of regular twists

If a quasicoherent module `F` on projective `n`-space is `m`-regular, then for every `r ≥ m`
every global section of `O(1 + r) ⊗ F` is a sum `∑ᵢ Xᵢ sᵢ` of coordinate multiples of global
sections of `O(r) ⊗ F` (Nitsure, arXiv:math/0504590v1, Lemma 2.1 (a), p. 10; Stacks, Tag 08A7,
Lemma 33.35.11, states it for coherent sheaves over a field). The base is an arbitrary
commutative ring. The surjectivity is stated for the coordinate map
`Γ(∐ᵢ O(r) ⊗ F) → Γ(O(1 + r) ⊗ F)` (`IsProjectiveRegular.surjective_coordinateMul`) and,
with global sections as morphisms out of the unit, as `s = ∑ᵢ tᵢ ≫ Xᵢ`
(`IsProjectiveRegular.exists_eq_sum_coordinateMul`). Since every `Xᵢ` is a global section of
`O(1)`, this implies Nitsure's form, surjectivity of the multiplication
`H⁰(O(1)) ⊗ H⁰(O(r) ⊗ F) → H⁰(O(1 + r) ⊗ F)`; that tensor-product map is not formalized here.

The proof is the Koszul argument. The Koszul complex of the coordinates at twist `r + 1` is exact
(`epi_koszul_kernelLift`, `epi_koszulDifferential_zero`). Its cycles `Z_p = ker (K_p → K_{p-1})`
fit into short exact sequences `0 → Z_{p+1} → K_{p+1} → Z_p → 0`, and
`H^p(K_{p+1}(r + 1)) = ⨁ H^p(O(r - p) ⊗ F)` vanishes by `r`-regularity. A downward induction from
above the dimension, where the cohomology of the quasicoherent cycles vanishes, gives
`H^1(Z_1) = 0`; the long exact sequence then makes `K_1 → K_0` surjective on global sections.
Both sources prove the statement by hyperplane sections over an infinite field instead.
-/

@[expose] public section

noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory Opposite
open AlgebraicGeometry.ProjectiveSpace
open AlgebraicGeometry.Scheme.Modules
open AlgebraicGeometry.Scheme.Modules.QuasiCoherent

universe u

namespace AlgebraicGeometry.Scheme.Cohomology

variable (R : Type u) [CommRing R] (ι : Type u)

section Koszul

variable [LinearOrder ι] [Fintype ι] (F : (ProjectiveSpace R ι).Modules)

omit [LinearOrder ι] in
/-- The Koszul terms of a module with quasicoherent twists are quasicoherent. -/
theorem koszulTerm_isQuasicoherent
    (hF : ∀ c : ℤ, ((moduleTensorLeftFunctor (ProjectiveSpace R ι)
      (twistingSheaf R ι c)).obj F).IsQuasicoherent) (t : ℤ) (p : ℕ) :
    (koszulTerm R ι F t p).IsQuasicoherent :=
  (SheafOfModules.isQuasicoherent (ProjectiveSpace R ι).ringCatSheaf).prop_coproduct
    (fun _ => hF _)

/-- The Koszul cycles `ker (K_{p+1} → K_p)` of a module with quasicoherent twists are
quasicoherent. -/
theorem koszulCycles_isQuasicoherent
    (hF : ∀ c : ℤ, ((moduleTensorLeftFunctor (ProjectiveSpace R ι)
      (twistingSheaf R ι c)).obj F).IsQuasicoherent) (t : ℤ) (p : ℕ) :
    (kernel (koszulDifferential R ι F t p)).IsQuasicoherent := by
  let := koszulTerm_isQuasicoherent R ι F hF t (p + 1)
  let := koszulTerm_isQuasicoherent R ι F hF t p
  exact quasicoherent_kernel _

/-- For a `(t - 1)`-regular module with quasicoherent twists, `H^{p+1}` of the Koszul cycles
`ker (K_{p+1}(t) → K_p(t))` vanishes; the proof is a downward induction on `p` from above the
dimension `n`. -/
theorem koszulCycles_cohomology_subsingleton (n : ℕ) (e : ι ≃ Fin (n + 1))
    (hF : ∀ c : ℤ, ((moduleTensorLeftFunctor (ProjectiveSpace R ι)
      (twistingSheaf R ι c)).obj F).IsQuasicoherent) (t : ℤ)
    (hreg : IsProjectiveRegular R ι F (t - 1)) :
    ∀ (d p : ℕ), n ≤ p + d → Subsingleton (Sheaf.H.{u + 1} (moduleAddSheaf (ProjectiveSpace R ι)
      (kernel (koszulDifferential R ι F t p))) (p + 1)) := by
  intro d
  induction d with
  | zero =>
    intro p hp
    let := koszulCycles_isQuasicoherent R ι F hF t p
    exact projectiveCohomology_subsingleton_of_gt R ι n e _ (p + 1) (by omega)
  | succ d ih =>
    intro p hp
    let g := kernel.lift (koszulDifferential R ι F t p) (koszulDifferential R ι F t (p + 1))
      (koszulDifferential_comp R ι F t p)
    let := epi_koszul_kernelLift R ι F t p
    have hS : (ShortComplex.kernelSequence g).ShortExact :=
      { exact := ShortComplex.kernelSequence_exact g, epi_g := inferInstanceAs (Epi g) }
    apply moduleCohomology_subsingleton_X₃ _ hS (p + 1)
    · change Subsingleton (Sheaf.H.{u + 1} (moduleAddSheaf (ProjectiveSpace R ι)
        ((𝟭 _).obj (koszulTerm R ι F t (p + 1 + 1)))) (p + 1))
      apply moduleCohomology_subsingleton_coproduct
      intro _
      exact twistCohomology_subsingleton_congr R ι (by push_cast; ring) (hreg (p + 1) (by omega))
    · have e1 : kernel (koszulDifferential R ι F t (p + 1)) ≅ kernel g :=
        kernelIsoOfEq (kernel.lift_ι _ _ _).symm ≪≫ kernelCompMono g (kernel.ι _)
      exact moduleCohomology_subsingleton_of_iso e1 _ (ih (p + 1) (by omega))

-- The sections of the additive sheaf of a module agree with the module sections only after
-- unfolding the forgetful functor.
set_option backward.isDefEq.respectTransparency false in
/-- For a `(t - 1)`-regular module with quasicoherent twists, the last Koszul differential
`K_1(t) → K_0(t)` is surjective on global sections. -/
theorem koszulDifferential_zero_surjective (n : ℕ) (e : ι ≃ Fin (n + 1))
    (hF : ∀ c : ℤ, ((moduleTensorLeftFunctor (ProjectiveSpace R ι)
      (twistingSheaf R ι c)).obj F).IsQuasicoherent) (t : ℤ)
    (hreg : IsProjectiveRegular R ι F (t - 1)) :
    Function.Surjective ((koszulDifferential R ι F t 0).val.app (op ⊤)) := by
  let := epi_koszulDifferential_zero R ι F t
  have hS : (ShortComplex.kernelSequence (koszulDifferential R ι F t 0)).ShortExact :=
    { exact := ShortComplex.kernelSequence_exact _,
      epi_g := inferInstanceAs (Epi (koszulDifferential R ι F t 0)) }
  have h1 := koszulCycles_cohomology_subsingleton R ι F n e hF t hreg n 0 (by omega)
  intro y
  obtain ⟨x, hx⟩ := Sheaf.H.longSequence_equiv₀_exact₃
    (moduleCoefficientSequence_shortExact (ProjectiveSpace R ι) _ hS) Limits.isTerminalTop y
    (@Subsingleton.elim _ h1 _ _)
  exact ⟨x, hx⟩

omit [LinearOrder ι] in
/-- The sum of the coordinate multiplications `⨁ᵢ O(c) ⊗ F → O(c') ⊗ F` is surjective on global
sections. -/
def CoordinateMulSurjective (c c' : ℤ) (h : ((1 : ℕ) : ℤ) + c = c') : Prop :=
  Function.Surjective ((Sigma.desc fun i : ι => koszulMul R ι F i c c' h).val.app (op ⊤))

/-- Surjectivity of the coordinate multiplications depends only on the values of the degrees. -/
theorem CoordinateMulSurjective.congr {c₁ c₁' c₂ c₂' : ℤ} (h₁ : ((1 : ℕ) : ℤ) + c₁ = c₁')
    (h₂ : ((1 : ℕ) : ℤ) + c₂ = c₂') (hc : c₁ = c₂) (hc' : c₁' = c₂')
    (h : CoordinateMulSurjective R ι F c₁ c₁' h₁) : CoordinateMulSurjective R ι F c₂ c₂' h₂ := by
  subst hc hc'
  exact h

/-- The singleton index sets. -/
abbrev koszulSingleton (i : ι) : KoszulIndex ι (0 + 1) := ⟨{i}, Finset.card_singleton i⟩

/-- The reindexing `⨁ᵢ O(t - 1) ⊗ F → K_1(t)` along `i ↦ {i}`. -/
def koszulSingletonMap (t : ℤ) :
    (∐ fun _ : ι => (moduleTensorLeftFunctor (ProjectiveSpace R ι)
      (twistingSheaf R ι (t - ((0 + 1 : ℕ) : ℤ)))).obj F) ⟶ koszulTerm R ι F t (0 + 1) :=
  Sigma.desc fun i => Sigma.ι (fun _ : KoszulIndex ι (0 + 1) => (moduleTensorLeftFunctor
    (ProjectiveSpace R ι) (twistingSheaf R ι (t - ((0 + 1 : ℕ) : ℤ)))).obj F) (koszulSingleton ι i)

/-- The fold map `K_0(t) → O(t) ⊗ F` out of the coproduct over the single empty index set. -/
def koszulFold (t : ℤ) :
    koszulTerm R ι F t 0 ⟶ (moduleTensorLeftFunctor (ProjectiveSpace R ι)
      (twistingSheaf R ι (t - ((0 : ℕ) : ℤ)))).obj F :=
  Sigma.desc fun _ => 𝟙 _

/-- The empty index set. -/
abbrev koszulEmpty : KoszulIndex ι 0 := ⟨∅, Finset.card_empty⟩

omit [LinearOrder ι] in
theorem ι_koszulFold (t : ℤ) (J : KoszulIndex ι 0) :
    Sigma.ι (fun _ : KoszulIndex ι 0 => (moduleTensorLeftFunctor (ProjectiveSpace R ι)
      (twistingSheaf R ι (t - ((0 : ℕ) : ℤ)))).obj F) J ≫ koszulFold R ι F t = 𝟙 _ := by
  rw [koszulFold, Sigma.ι_comp_desc]

omit [Fintype ι] in
theorem koszulSign_singleton (i : ι) : koszulSign i {i} = 1 := by
  have h : ({i} : Finset ι).filter (· < i) = ∅ :=
    Finset.filter_eq_empty_iff.mpr fun x hx => by
      rw [Finset.mem_singleton.mp hx]
      exact lt_irrefl i
  unfold koszulSign
  rw [h, Finset.card_empty, pow_zero]

/-- The sum of the coordinate multiplications is the reindexed last Koszul differential followed
by the fold map. -/
theorem sigmaDesc_koszulMul_eq (t : ℤ) :
    (Sigma.desc fun i : ι => koszulMul R ι F i (t - ((0 + 1 : ℕ) : ℤ)) (t - ((0 : ℕ) : ℤ))
        (koszulDeg_contraction t 0)) =
      koszulSingletonMap R ι F t ≫ koszulDifferential R ι F t 0 ≫ koszulFold R ι F t := by
  apply Sigma.hom_ext
  intro i
  rw [Sigma.ι_comp_desc, koszulSingletonMap, Sigma.ι_comp_desc_assoc, koszulDifferential,
    Preadditive.sum_comp, Preadditive.comp_sum, Finset.sum_eq_single i]
  · rw [← Category.assoc, ι_koszulContraction_of_mem R ι F t 0 i (koszulSingleton ι i)
      (koszulIndexErase (koszulSingleton ι i) i (Finset.mem_singleton_self i))
      (Finset.mem_singleton_self i) rfl, koszulSign_singleton, one_smul, Category.assoc,
      ι_koszulFold, Category.comp_id]
  · intro j _ hji
    rw [← Category.assoc, ι_koszulContraction_of_notMem R ι F t 0 j (koszulSingleton ι i)
      (fun hm => hji (Finset.mem_singleton.mp hm)), zero_comp]
  · intro h
    exact absurd (Finset.mem_univ i) h

omit [LinearOrder ι] [Fintype ι] in
theorem koszulIndex_one_eq_singleton (J : KoszulIndex ι (0 + 1)) :
    ∃ i, J = koszulSingleton ι i := by
  obtain ⟨i, hi⟩ := Finset.card_eq_one.mp J.2
  exact ⟨i, Subtype.ext hi⟩

/-- A section of the reindexing `⨁ᵢ O(t - 1) ⊗ F → K_1(t)`, choosing the element of each
singleton. -/
def koszulSingletonSection (t : ℤ) :
    koszulTerm R ι F t (0 + 1) ⟶ (∐ fun _ : ι => (moduleTensorLeftFunctor
      (ProjectiveSpace R ι) (twistingSheaf R ι (t - ((0 + 1 : ℕ) : ℤ)))).obj F) :=
  Sigma.desc fun J => Sigma.ι (fun _ : ι => (moduleTensorLeftFunctor (ProjectiveSpace R ι)
    (twistingSheaf R ι (t - ((0 + 1 : ℕ) : ℤ)))).obj F) (koszulIndex_one_eq_singleton ι J).choose

theorem koszulSingletonSection_comp (t : ℤ) :
    koszulSingletonSection R ι F t ≫ koszulSingletonMap R ι F t = 𝟙 _ := by
  apply Sigma.hom_ext
  intro J
  rw [koszulSingletonSection, Sigma.ι_comp_desc_assoc, koszulSingletonMap, Sigma.ι_comp_desc,
    Category.comp_id]
  exact congrArg (Sigma.ι _) (koszulIndex_one_eq_singleton ι J).choose_spec.symm

/-- For a `(t - 1)`-regular module with quasicoherent twists, the coordinate multiplications
`⨁ᵢ O(t - 1) ⊗ F → O(t) ⊗ F` are jointly surjective on global sections. -/
theorem coordinateMulSurjective_koszul (n : ℕ) (e : ι ≃ Fin (n + 1))
    (hF : ∀ c : ℤ, ((moduleTensorLeftFunctor (ProjectiveSpace R ι)
      (twistingSheaf R ι c)).obj F).IsQuasicoherent) (t : ℤ)
    (hreg : IsProjectiveRegular R ι F (t - 1)) :
    CoordinateMulSurjective R ι F (t - ((0 + 1 : ℕ) : ℤ)) (t - ((0 : ℕ) : ℤ))
      (koszulDeg_contraction t 0) := by
  have hd := koszulDifferential_zero_surjective R ι F n e hF t hreg
  let β := koszulSingletonSection R ι F t
  have hβ : β ≫ koszulSingletonMap R ι F t = 𝟙 _ := koszulSingletonSection_comp R ι F t
  intro y
  obtain ⟨x, hx⟩ := hd ((Sigma.ι (fun _ : KoszulIndex ι 0 => (moduleTensorLeftFunctor
    (ProjectiveSpace R ι) (twistingSheaf R ι (t - ((0 : ℕ) : ℤ)))).obj F)
      (koszulEmpty ι)).val.app (op ⊤) y)
  refine ⟨β.val.app (op ⊤) x, ?_⟩
  have hβx : (koszulSingletonMap R ι F t).val.app (op ⊤) (β.val.app (op ⊤) x) = x := by
    change (β ≫ koszulSingletonMap R ι F t).val.app (op ⊤) x = x
    rw [hβ]
    rfl
  change (Sigma.desc fun i : ι => koszulMul R ι F i (t - ((0 + 1 : ℕ) : ℤ)) (t - ((0 : ℕ) : ℤ))
    (koszulDeg_contraction t 0)).val.app (op ⊤) (β.val.app (op ⊤) x) = y
  rw [sigmaDesc_koszulMul_eq]
  change (koszulFold R ι F t).val.app (op ⊤) ((koszulDifferential R ι F t 0).val.app (op ⊤)
    ((koszulSingletonMap R ι F t).val.app (op ⊤) (β.val.app (op ⊤) x))) = y
  rw [hβx, hx]
  change (Sigma.ι _ (koszulEmpty ι) ≫ koszulFold R ι F t).val.app (op ⊤) y = y
  rw [ι_koszulFold]
  rfl

end Koszul

/-- **Nitsure, Lemma 2.1 (a)** (arXiv:math/0504590v1, p. 10; Stacks, Tag 08A7,
Lemma 33.35.11): if a quasicoherent module `F` is `m`-regular, then for every `r ≥ m` the sum of
the coordinate multiplications `Γ(∐ᵢ O(r) ⊗ F) → Γ(O(1 + r) ⊗ F)` is surjective. The base is an
arbitrary commutative ring, and `ι` is labelled by `Fin (n + 1)`. -/
theorem IsProjectiveRegular.surjective_coordinateMul (n : ℕ) (e : ι ≃ Fin (n + 1))
    {F : (ProjectiveSpace R ι).Modules} [F.IsQuasicoherent]
    {m r : ℤ} (h : IsProjectiveRegular R ι F m) (hr : m ≤ r) :
    Function.Surjective ((Sigma.desc fun i : ι =>
      (twistingTensorMultiply R ι ((1 : ℕ) : ℤ) r (coordinateSection R ι i)).app F).val.app
        (op ⊤)) := by
  let : LinearOrder ι := LinearOrder.lift' e e.injective
  let : Fintype ι := Fintype.ofEquiv _ e.symm
  have hreg : IsProjectiveRegular R ι F (r + 1 - 1) := by
    rw [add_sub_cancel_right]
    exact IsProjectiveRegular.of_le R ι n e hr h
  have hk := coordinateMulSurjective_koszul R ι F n e (twistingTensor_isQuasicoherent R ι F)
    (r + 1) hreg
  have hc := CoordinateMulSurjective.congr R ι F (koszulDeg_contraction (r + 1) 0)
    (rfl : ((1 : ℕ) : ℤ) + r = ((1 : ℕ) : ℤ) + r) (by push_cast; ring) (by push_cast; ring) hk
  unfold CoordinateMulSurjective at hc
  simpa only [koszulMul, twistingTensorMultiplyTo_rfl] using hc

/-- **Nitsure, Lemma 2.1 (a)** for affine-locally finite-type modules (arXiv:math/0504590v1,
p. 10; Stacks, Tag 08A7, Lemma 33.35.11). The base is an arbitrary commutative ring. -/
theorem IsProjectiveRegular.surjective_coordinateMul_of_coherent (n : ℕ)
    (e : ι ≃ Fin (n + 1)) {F : (ProjectiveSpace R ι).Modules}
    (hF : affineLocallyFiniteType (ProjectiveSpace R ι) F)
    {m r : ℤ} (h : IsProjectiveRegular R ι F m) (hr : m ≤ r) :
    Function.Surjective ((Sigma.desc fun i : ι =>
      (twistingTensorMultiply R ι ((1 : ℕ) : ℤ) r (coordinateSection R ι i)).app F).val.app
        (op ⊤)) := by
  have : F.IsQuasicoherent := quasicoherent_of_affineCharts _ (fun A j _ => (hF A j).1)
  exact IsProjectiveRegular.surjective_coordinateMul R ι n e h hr

/-- **Nitsure, Lemma 2.1 (a)** with global sections as morphisms out of the unit
(arXiv:math/0504590v1, p. 10): if a quasicoherent module `F` is `m`-regular and `r ≥ m`, then
every global section `s : 𝟙_ ⟶ O(1 + r) ⊗ F` is a sum `∑ᵢ tᵢ ≫ Xᵢ` of coordinate multiples of
global sections `tᵢ : 𝟙_ ⟶ O(r) ⊗ F`. -/
theorem IsProjectiveRegular.exists_eq_sum_coordinateMul [Fintype ι] (n : ℕ)
    (e : ι ≃ Fin (n + 1)) {F : (ProjectiveSpace R ι).Modules} [F.IsQuasicoherent]
    {m r : ℤ} (h : IsProjectiveRegular R ι F m) (hr : m ≤ r)
    (s : 𝟙_ (ProjectiveSpace R ι).Modules ⟶ (moduleTensorLeftFunctor (ProjectiveSpace R ι)
      (twistingSheaf R ι (((1 : ℕ) : ℤ) + r))).obj F) :
    ∃ t : ι → (𝟙_ (ProjectiveSpace R ι).Modules ⟶ (moduleTensorLeftFunctor (ProjectiveSpace R ι)
        (twistingSheaf R ι r)).obj F),
      s = ∑ i, t i ≫
        (twistingTensorMultiply R ι ((1 : ℕ) : ℤ) r (coordinateSection R ι i)).app F := by
  obtain ⟨a, ha⟩ := exists_unitHom_factor_of_surjective _
    (IsProjectiveRegular.surjective_coordinateMul R ι n e h hr) s
  obtain ⟨t, ht⟩ := exists_eq_sum_sigma_ι a
  refine ⟨t, ?_⟩
  rw [← ha, ht, Preadditive.sum_comp]
  exact Finset.sum_congr rfl fun i _ => by rw [Category.assoc, Sigma.ι_comp_desc]

end AlgebraicGeometry.Scheme.Cohomology
