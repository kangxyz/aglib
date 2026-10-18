/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Cohomology.Projective.Regularity.CoordinateGeneration
public import Aglib.AlgebraicGeometry.ProjectiveSpace.Tensor.Monoidal.FreeDegree

/-!
# The Koszul complex of the coordinates

For a module `F` on projective space with finitely many linearly ordered coordinates and a
twist `t`, the `p`-th Koszul term is `⨁_{|J| = p} O(t - p) ⊗ F`, indexed by the `p`-element
sets `J` of coordinates. The contraction with the coordinate `i` sends the summand `J ∋ i` to
the summand `J \ {i}` by `(-1)^{#{j ∈ J | j < i}} Xᵢ`; the differential is the sum of the
contractions. Contractions anticommute, since coordinate multiplications commute
(`twistingTensorMultiplyTo_comm`) and the signs differ by one transposition, so `d ∘ d = 0`.

This complex is behind the Koszul proof of Nitsure, arXiv:math/0504590v1, Lemma 2.1 (a)
(`Regularity/Surjectivity`), and through (a) behind (c) (`Regularity/GlobalGeneration`).
Lemma 2.1 (b) is proved by the syzygy route of `Regularity/Monotone` instead. Nitsure and
Stacks, Tags 08A6–08A7, prove (a) and (b) by hyperplane sections over an infinite field.
-/

@[expose] public section

noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry.Scheme.Modules

universe u

namespace AlgebraicGeometry.ProjectiveSpace

section Sign

variable {ι : Type*} [LinearOrder ι]

/-- The Koszul sign `(-1)^{#{j ∈ J | j < i}}`. -/
def koszulSign (i : ι) (J : Finset ι) : ℤ := (-1) ^ (J.filter (· < i)).card

theorem koszulSign_erase_of_lt {i j : ι} {J : Finset ι} (hi : i ∈ J) (h : i < j) :
    koszulSign j (J.erase i) = -koszulSign j J := by
  unfold koszulSign
  have hm : i ∈ J.filter (· < j) := Finset.mem_filter.mpr ⟨hi, h⟩
  rw [Finset.filter_erase, Finset.card_erase_of_mem hm]
  obtain ⟨c, hc⟩ : ∃ c, (J.filter (· < j)).card = c + 1 :=
    ⟨_, (Nat.succ_pred_eq_of_pos (Finset.card_pos.mpr ⟨i, hm⟩)).symm⟩
  rw [hc, Nat.add_sub_cancel, pow_succ]
  ring

theorem koszulSign_erase_of_not_lt {i j : ι} {J : Finset ι} (h : ¬i < j) :
    koszulSign j (J.erase i) = koszulSign j J := by
  unfold koszulSign
  rw [Finset.filter_erase, Finset.erase_eq_of_notMem (s := J.filter (· < j)) (a := i)
    (fun hm => h (Finset.mem_filter.mp hm).2)]

/-- Removing two coordinates in either order changes the product of signs by `-1`. -/
theorem koszulSign_mul_erase {i j : ι} {J : Finset ι} (hi : i ∈ J) (hj : j ∈ J) (hij : i ≠ j) :
    koszulSign i J * koszulSign j (J.erase i) = -(koszulSign j J * koszulSign i (J.erase j)) := by
  rcases lt_or_gt_of_ne hij with h | h
  · rw [koszulSign_erase_of_lt hi h, koszulSign_erase_of_not_lt (not_lt.mpr h.le)]
    ring
  · rw [koszulSign_erase_of_not_lt (not_lt.mpr h.le), koszulSign_erase_of_lt hj h]
    ring

theorem koszulSign_insert_self (i : ι) (J : Finset ι) :
    koszulSign i (insert i J) = koszulSign i J := by
  unfold koszulSign
  rw [Finset.filter_insert, ite_eq_right (lt_irrefl i)]

theorem koszulSign_erase_self (i : ι) (J : Finset ι) :
    koszulSign i (J.erase i) = koszulSign i J :=
  koszulSign_erase_of_not_lt (lt_irrefl i)

theorem koszulSign_insert_of_lt {i j : ι} {J : Finset ι} (hi : i ∉ J) (h : i < j) :
    koszulSign j (insert i J) = -koszulSign j J := by
  unfold koszulSign
  rw [Finset.filter_insert, ite_eq_left h,
    Finset.card_insert_of_notMem (fun hm => hi (Finset.mem_filter.mp hm).1), pow_succ]
  ring

theorem koszulSign_insert_of_not_lt {i j : ι} {J : Finset ι} (h : ¬i < j) :
    koszulSign j (insert i J) = koszulSign j J := by
  unfold koszulSign
  rw [Finset.filter_insert, ite_eq_right h]

theorem koszulSign_mul_self (i : ι) (J : Finset ι) : koszulSign i J * koszulSign i J = 1 := by
  unfold koszulSign
  rw [← pow_add, ← two_mul, pow_mul]
  norm_num

/-- Inserting `i` and removing `j ≠ i` in either order: the products of signs cancel. -/
theorem koszulSign_insert_erase_add {i j : ι} {J : Finset ι} (hi : i ∉ J) (hj : j ∈ J)
    (hij : i ≠ j) :
    koszulSign i J * koszulSign j (insert i J) + koszulSign j J * koszulSign i (J.erase j) =
      0 := by
  rcases lt_or_gt_of_ne hij with h | h
  · rw [koszulSign_insert_of_lt hi h, koszulSign_erase_of_not_lt (not_lt.mpr h.le)]
    ring
  · rw [koszulSign_insert_of_not_lt (not_lt.mpr h.le), koszulSign_erase_of_lt hj h]
    ring

end Sign

/-- A double sum of an antisymmetric family with vanishing diagonal is zero. -/
theorem sum_sum_eq_zero_of_antisymm {M : Type*} [AddCommGroup M] {α : Type*} [Fintype α]
    (a : α → α → M) (h : ∀ i j, i ≠ j → a i j = -a j i) (h0 : ∀ i, a i i = 0) :
    ∑ i, ∑ j, a i j = 0 := by
  rw [← Fintype.sum_prod_type']
  refine Finset.sum_involution (fun x _ => x.swap) ?_ ?_ (fun _ _ => Finset.mem_univ _)
    (fun x _ => x.swap_swap)
  · rintro ⟨i, j⟩ _
    by_cases hij : i = j
    · subst hij
      simp [h0]
    · simp [h i j hij]
  · rintro ⟨i, j⟩ _ hne heq
    simp only [Prod.swap_prod_mk, Prod.mk.injEq] at heq
    obtain ⟨rfl, -⟩ := heq
    exact hne (h0 _)

/-! ### Degree identities

Every degree equation in the Koszul definitions and statements below is one of these named
lemmas, and every index set built from another is `koszulIndexErase` or `koszulIndexInsert`.
All occurrences of a coordinate multiplication, a transport or a summand inclusion then carry the
same proof terms, so the kernel compares them syntactically; distinct inline proofs inside
composites of module-sheaf morphisms make it unfold the compositions instead. -/

/-- Contraction lowers the Koszul degree: `1 + (t - (p + 1)) = t - p`. -/
theorem koszulDeg_contraction (t : ℤ) (p : ℕ) :
    ((1 : ℕ) : ℤ) + (t - ((p + 1 : ℕ) : ℤ)) = t - (p : ℤ) := by
  push_cast; ring

/-- Coordinate multiplication raises the twist: `1 + (t - p) = t + 1 - p`. -/
theorem koszulDeg_shift (t : ℤ) (p : ℕ) :
    ((1 : ℕ) : ℤ) + (t - (p : ℤ)) = t + 1 - (p : ℤ) := by
  push_cast; ring

/-- The wedge keeps the twist of a summand: `t - p = t + 1 - (p + 1)`. -/
theorem koszulDeg_wedge (t : ℤ) (p : ℕ) : t - (p : ℤ) = t + 1 - ((p + 1 : ℕ) : ℤ) := by
  push_cast; ring

variable (R : Type u) [CommRing R] (ι : Type u) [LinearOrder ι] [Fintype ι]

/-- Indices of the `p`-th Koszul term: the `p`-element sets of coordinates. -/
abbrev KoszulIndex (p : ℕ) : Type u := {J : Finset ι // J.card = p}

omit [Fintype ι] in
variable {ι} in
/-- Removing a member from a `(p + 1)`-element set of coordinates. -/
abbrev koszulIndexErase {p : ℕ} (J : KoszulIndex ι (p + 1)) (i : ι) (h : i ∈ J.1) :
    KoszulIndex ι p :=
  ⟨J.1.erase i, by rw [Finset.card_erase_of_mem h, J.2, Nat.add_sub_cancel]⟩

omit [Fintype ι] in
variable {ι} in
/-- Adding a non-member to a `p`-element set of coordinates. -/
abbrev koszulIndexInsert {p : ℕ} (J : KoszulIndex ι p) (i : ι) (h : i ∉ J.1) :
    KoszulIndex ι (p + 1) :=
  ⟨insert i J.1, by rw [Finset.card_insert_of_notMem h, J.2]⟩

variable (F : (ProjectiveSpace R ι).Modules)

/-- The `p`-th Koszul term `⨁_{|J| = p} O(t - p) ⊗ F`. -/
abbrev koszulTerm (t : ℤ) (p : ℕ) : (ProjectiveSpace R ι).Modules :=
  ∐ fun _ : KoszulIndex ι p =>
    (moduleTensorLeftFunctor (ProjectiveSpace R ι) (twistingSheaf R ι (t - p))).obj F

/-- Multiplication by the coordinate `Xᵢ` from `O(c) ⊗ F` to `O(c') ⊗ F`, for `1 + c = c'`. -/
abbrev koszulMul (i : ι) (c c' : ℤ) (h : ((1 : ℕ) : ℤ) + c = c') :
    (moduleTensorLeftFunctor (ProjectiveSpace R ι) (twistingSheaf R ι c)).obj F ⟶
      (moduleTensorLeftFunctor (ProjectiveSpace R ι) (twistingSheaf R ι c')).obj F :=
  (twistingTensorMultiplyTo R ((1 : ℕ) : ℤ) c c' h (coordinateSection R ι i)).app F

omit [LinearOrder ι] [Fintype ι] in
/-- Coordinate multiplications commute. -/
theorem koszulMul_comm (i j : ι) (a b b' c : ℤ) (h₁ : ((1 : ℕ) : ℤ) + a = b)
    (h₂ : ((1 : ℕ) : ℤ) + b = c) (h₃ : ((1 : ℕ) : ℤ) + a = b') (h₄ : ((1 : ℕ) : ℤ) + b' = c) :
    koszulMul R ι F i a b h₁ ≫ koszulMul R ι F j b c h₂ =
      koszulMul R ι F j a b' h₃ ≫ koszulMul R ι F i b' c h₄ := by
  have h := NatTrans.congr_app (twistingTensorMultiplyTo_comm R ((1 : ℕ) : ℤ) ((1 : ℕ) : ℤ)
    a b c b' h₁ h₂ h₃ h₄ (coordinateSection R ι i) (coordinateSection R ι j)) F
  simpa only [NatTrans.comp_app] using h

/-- The contraction with the coordinate `i`: on the summand `J ∋ i` it is
`(-1)^{#{j ∈ J | j < i}} Xᵢ` into the summand `J \ {i}`; it vanishes on the other summands. -/
def koszulContraction (t : ℤ) (p : ℕ) (i : ι) :
    koszulTerm R ι F t (p + 1) ⟶ koszulTerm R ι F t p :=
  Sigma.desc fun J => if h : i ∈ J.1 then
    koszulSign i J.1 • (koszulMul R ι F i (t - ((p + 1 : ℕ) : ℤ)) (t - (p : ℤ))
      (koszulDeg_contraction t p) ≫
      Sigma.ι (fun _ : KoszulIndex ι p => (moduleTensorLeftFunctor (ProjectiveSpace R ι)
        (twistingSheaf R ι (t - (p : ℤ)))).obj F) (koszulIndexErase J i h))
  else 0

/-- The Koszul differential, the sum of the contractions. -/
def koszulDifferential (t : ℤ) (p : ℕ) : koszulTerm R ι F t (p + 1) ⟶ koszulTerm R ι F t p :=
  ∑ i, koszulContraction R ι F t p i

/-- Contracting twice with the same coordinate vanishes. -/
theorem koszulContraction_comp_self (t : ℤ) (p : ℕ) (i : ι) :
    koszulContraction R ι F t (p + 1) i ≫ koszulContraction R ι F t p i = 0 := by
  apply Sigma.hom_ext
  intro J
  rw [comp_zero]
  simp only [koszulContraction, Sigma.ι_comp_desc_assoc]
  split_ifs with h
  · rw [Preadditive.zsmul_comp, Category.assoc, Sigma.ι_comp_desc,
      dite_eq_right (Finset.notMem_erase i J.1), comp_zero, smul_zero]
  · rw [zero_comp]

/-- Contractions with distinct coordinates anticommute. -/
theorem koszulContraction_anticomm (t : ℤ) (p : ℕ) {i j : ι} (hij : i ≠ j) :
    koszulContraction R ι F t (p + 1) i ≫ koszulContraction R ι F t p j =
      -(koszulContraction R ι F t (p + 1) j ≫ koszulContraction R ι F t p i) := by
  apply Sigma.hom_ext
  intro J
  rw [Preadditive.comp_neg]
  simp only [koszulContraction, Sigma.ι_comp_desc_assoc]
  by_cases hi : i ∈ J.1 <;> by_cases hj : j ∈ J.1
  · rw [dite_eq_left hi, dite_eq_left hj]
    simp only [Preadditive.zsmul_comp, Category.assoc, Sigma.ι_comp_desc]
    rw [dite_eq_left (Finset.mem_erase.mpr ⟨hij.symm, hj⟩),
      dite_eq_left (Finset.mem_erase.mpr ⟨hij, hi⟩)]
    simp only [Preadditive.comp_zsmul, smul_smul, ← Category.assoc]
    rw [koszulMul_comm R ι F i j (t - ((p + 1 + 1 : ℕ) : ℤ)) (t - ((p + 1 : ℕ) : ℤ))
      (t - ((p + 1 : ℕ) : ℤ)) (t - (p : ℤ)) (koszulDeg_contraction t (p + 1))
      (koszulDeg_contraction t p) (koszulDeg_contraction t (p + 1)) (koszulDeg_contraction t p)]
    have hidx : koszulIndexErase (koszulIndexErase J i hi) j
        (Finset.mem_erase.mpr ⟨hij.symm, hj⟩) =
        koszulIndexErase (koszulIndexErase J j hj) i (Finset.mem_erase.mpr ⟨hij, hi⟩) :=
      Subtype.ext Finset.erase_right_comm
    rw [hidx, koszulSign_mul_erase hi hj hij, neg_smul]
  · rw [dite_eq_left hi, dite_eq_right hj, zero_comp, neg_zero, Preadditive.zsmul_comp,
      Category.assoc, Sigma.ι_comp_desc,
      dite_eq_right (fun hm => hj (Finset.mem_of_mem_erase hm)), comp_zero, smul_zero]
  · rw [dite_eq_right hi, dite_eq_left hj, zero_comp, Preadditive.zsmul_comp,
      Category.assoc, Sigma.ι_comp_desc,
      dite_eq_right (fun hm => hi (Finset.mem_of_mem_erase hm)), comp_zero, smul_zero, neg_zero]
  · rw [dite_eq_right hi, dite_eq_right hj, zero_comp, zero_comp, neg_zero]

/-- The Koszul differentials compose to zero. -/
theorem koszulDifferential_comp (t : ℤ) (p : ℕ) :
    koszulDifferential R ι F t (p + 1) ≫ koszulDifferential R ι F t p = 0 := by
  simp only [koszulDifferential, Preadditive.sum_comp, Preadditive.comp_sum]
  exact sum_sum_eq_zero_of_antisymm _
    (fun i j hij => koszulContraction_anticomm R ι F t p hij.symm)
    (fun i => koszulContraction_comp_self R ι F t p i)

/-- On a summand containing `i`, the contraction with `i` is the signed coordinate multiplication
into the summand `J'` with `J' = J \ {i}`. -/
theorem ι_koszulContraction_of_mem (t : ℤ) (p : ℕ) (i : ι) (J : KoszulIndex ι (p + 1))
    (J' : KoszulIndex ι p) (h : i ∈ J.1) (hJ' : J'.1 = J.1.erase i) :
    Sigma.ι (fun _ : KoszulIndex ι (p + 1) => (moduleTensorLeftFunctor (ProjectiveSpace R ι)
        (twistingSheaf R ι (t - ((p + 1 : ℕ) : ℤ)))).obj F) J ≫
        koszulContraction R ι F t p i =
      koszulSign i J.1 • (koszulMul R ι F i (t - ((p + 1 : ℕ) : ℤ)) (t - (p : ℤ))
        (koszulDeg_contraction t p) ≫
        Sigma.ι (fun _ : KoszulIndex ι p => (moduleTensorLeftFunctor (ProjectiveSpace R ι)
          (twistingSheaf R ι (t - (p : ℤ)))).obj F) J') := by
  obtain rfl : J' = koszulIndexErase J i h := Subtype.ext hJ'
  rw [koszulContraction, Sigma.ι_comp_desc, dite_eq_left h]

/-- On a summand not containing `i`, the contraction with `i` vanishes. -/
theorem ι_koszulContraction_of_notMem (t : ℤ) (p : ℕ) (i : ι) (J : KoszulIndex ι (p + 1))
    (h : i ∉ J.1) :
    Sigma.ι (fun _ : KoszulIndex ι (p + 1) => (moduleTensorLeftFunctor (ProjectiveSpace R ι)
        (twistingSheaf R ι (t - ((p + 1 : ℕ) : ℤ)))).obj F) J ≫
        koszulContraction R ι F t p i = 0 := by
  rw [koszulContraction, Sigma.ι_comp_desc, dite_eq_right h]

omit [LinearOrder ι] [Fintype ι] in
/-- The twist of a summand is kept by the wedge: `O(t - p) ⊗ F = O(t + 1 - (p + 1)) ⊗ F`. The
transport is this named proof, so that the definition of `koszulWedge` and the statements about
it carry the same term (a proof built with `congrArg` inside the definition would be abstracted
into an auxiliary lemma, and the kernel would then unfold the compositions to compare). -/
theorem koszulWedgeEq (t : ℤ) (p : ℕ) :
    (moduleTensorLeftFunctor (ProjectiveSpace R ι) (twistingSheaf R ι (t - (p : ℤ)))).obj F =
      (moduleTensorLeftFunctor (ProjectiveSpace R ι)
        (twistingSheaf R ι (t + 1 - ((p + 1 : ℕ) : ℤ)))).obj F :=
  congrArg (fun d : ℤ => (moduleTensorLeftFunctor (ProjectiveSpace R ι)
    (twistingSheaf R ι d)).obj F) (koszulDeg_wedge t p)

/-- Wedge with the coordinate `i`: the summand `J ∌ i` of the `p`-th term at twist `t` maps to the
summand `J ∪ {i}` of the `(p + 1)`-st term at twist `t + 1` with the sign
`(-1)^{#{j ∈ J | j < i}}`; the twist degrees `t - p` and `t + 1 - (p + 1)` agree. -/
def koszulWedge (t : ℤ) (p : ℕ) (i : ι) :
    koszulTerm R ι F t p ⟶ koszulTerm R ι F (t + 1) (p + 1) :=
  Sigma.desc fun J => if h : i ∈ J.1 then 0 else
    koszulSign i J.1 • (eqToHom (koszulWedgeEq R ι F t p) ≫
      Sigma.ι (fun _ : KoszulIndex ι (p + 1) => (moduleTensorLeftFunctor (ProjectiveSpace R ι)
        (twistingSheaf R ι (t + 1 - ((p + 1 : ℕ) : ℤ)))).obj F) (koszulIndexInsert J i h))

theorem ι_koszulWedge_of_notMem (t : ℤ) (p : ℕ) (i : ι) (J : KoszulIndex ι p)
    (J' : KoszulIndex ι (p + 1)) (h : i ∉ J.1) (hJ' : J'.1 = insert i J.1) :
    Sigma.ι (fun _ : KoszulIndex ι p => (moduleTensorLeftFunctor (ProjectiveSpace R ι)
        (twistingSheaf R ι (t - (p : ℤ)))).obj F) J ≫ koszulWedge R ι F t p i =
      koszulSign i J.1 • (eqToHom (koszulWedgeEq R ι F t p) ≫
        Sigma.ι (fun _ : KoszulIndex ι (p + 1) => (moduleTensorLeftFunctor (ProjectiveSpace R ι)
          (twistingSheaf R ι (t + 1 - ((p + 1 : ℕ) : ℤ)))).obj F) J') := by
  obtain rfl : J' = koszulIndexInsert J i h := Subtype.ext hJ'
  rw [koszulWedge, Sigma.ι_comp_desc, dite_eq_right h]

theorem ι_koszulWedge_of_mem (t : ℤ) (p : ℕ) (i : ι) (J : KoszulIndex ι p) (h : i ∈ J.1) :
    Sigma.ι (fun _ : KoszulIndex ι p => (moduleTensorLeftFunctor (ProjectiveSpace R ι)
        (twistingSheaf R ι (t - (p : ℤ)))).obj F) J ≫ koszulWedge R ι F t p i = 0 := by
  rw [koszulWedge, Sigma.ι_comp_desc, dite_eq_left h]

/-- Multiplication by the coordinate `i` on every summand, from twist `t` to twist `t + 1`. -/
def koszulCoordinateMul (t : ℤ) (p : ℕ) (i : ι) :
    koszulTerm R ι F t p ⟶ koszulTerm R ι F (t + 1) p :=
  Sigma.desc fun J => koszulMul R ι F i (t - (p : ℤ)) (t + 1 - (p : ℤ)) (koszulDeg_shift t p) ≫
    Sigma.ι (fun _ : KoszulIndex ι p => (moduleTensorLeftFunctor (ProjectiveSpace R ι)
      (twistingSheaf R ι (t + 1 - (p : ℤ)))).obj F) J

omit [LinearOrder ι] [Fintype ι] in
/-- A transport of the twist degree followed by coordinate multiplication. -/
theorem eqToHom_comp_koszulMul (i : ι) {a b : ℤ} (hab : a = b)
    (h : (moduleTensorLeftFunctor (ProjectiveSpace R ι) (twistingSheaf R ι a)).obj F =
      (moduleTensorLeftFunctor (ProjectiveSpace R ι) (twistingSheaf R ι b)).obj F) (c : ℤ)
    (h₁ : ((1 : ℕ) : ℤ) + b = c) (h₂ : ((1 : ℕ) : ℤ) + a = c) :
    eqToHom h ≫ koszulMul R ι F i b c h₁ = koszulMul R ι F i a c h₂ := by
  subst hab
  rw [eqToHom_refl, Category.id_comp]

omit [LinearOrder ι] [Fintype ι] in
/-- Coordinate multiplication followed by a transport of the twist degree. -/
theorem koszulMul_comp_eqToHom (i : ι) (a : ℤ) {b c : ℤ} (hbc : b = c)
    (h : (moduleTensorLeftFunctor (ProjectiveSpace R ι) (twistingSheaf R ι b)).obj F =
      (moduleTensorLeftFunctor (ProjectiveSpace R ι) (twistingSheaf R ι c)).obj F)
    (h₁ : ((1 : ℕ) : ℤ) + a = b) (h₂ : ((1 : ℕ) : ℤ) + a = c) :
    koszulMul R ι F i a b h₁ ≫ eqToHom h = koszulMul R ι F i a c h₂ := by
  subst hbc
  rw [eqToHom_refl, Category.comp_id]

/-- Wedge with `i ∉ J`, then contraction with `j ∈ J`. -/
theorem ι_koszulWedge_contraction_of_ne (t : ℤ) (p : ℕ) {i j : ι} (J : KoszulIndex ι (p + 1))
    (A : KoszulIndex ι (p + 1)) (hi : i ∉ J.1) (hj : j ∈ J.1) (hA : A.1 = (insert i J.1).erase j) :
    Sigma.ι (fun _ : KoszulIndex ι (p + 1) => (moduleTensorLeftFunctor (ProjectiveSpace R ι)
        (twistingSheaf R ι (t - ((p + 1 : ℕ) : ℤ)))).obj F) J ≫
        koszulWedge R ι F t (p + 1) i ≫ koszulContraction R ι F (t + 1) (p + 1) j =
      (koszulSign i J.1 * koszulSign j (insert i J.1)) •
        (koszulMul R ι F j (t - ((p + 1 : ℕ) : ℤ)) (t + 1 - ((p + 1 : ℕ) : ℤ))
          (koszulDeg_shift t (p + 1)) ≫
        Sigma.ι (fun _ : KoszulIndex ι (p + 1) => (moduleTensorLeftFunctor (ProjectiveSpace R ι)
          (twistingSheaf R ι (t + 1 - ((p + 1 : ℕ) : ℤ)))).obj F) A) := by
  rw [← Category.assoc, ι_koszulWedge_of_notMem R ι F t (p + 1) i J
      (koszulIndexInsert J i hi) hi rfl,
    Preadditive.zsmul_comp, Category.assoc,
    ι_koszulContraction_of_mem R ι F (t + 1) (p + 1) j _ A (Finset.mem_insert_of_mem hj) hA,
    Preadditive.comp_zsmul, smul_smul, ← Category.assoc,
    eqToHom_comp_koszulMul R ι F j (koszulDeg_wedge t (p + 1)) (koszulWedgeEq R ι F t (p + 1))
      (t + 1 - ((p + 1 : ℕ) : ℤ))
      (koszulDeg_contraction (t + 1) (p + 1)) (koszulDeg_shift t (p + 1))]

/-- Contraction with `j ∈ J`, then wedge with `i ∉ J`. -/
theorem ι_koszulContraction_wedge_of_ne (t : ℤ) (p : ℕ) {i j : ι} (J : KoszulIndex ι (p + 1))
    (A : KoszulIndex ι (p + 1)) (hi : i ∉ J.1) (hj : j ∈ J.1) (hA : A.1 = insert i (J.1.erase j)) :
    Sigma.ι (fun _ : KoszulIndex ι (p + 1) => (moduleTensorLeftFunctor (ProjectiveSpace R ι)
        (twistingSheaf R ι (t - ((p + 1 : ℕ) : ℤ)))).obj F) J ≫
        koszulContraction R ι F t p j ≫ koszulWedge R ι F t p i =
      (koszulSign j J.1 * koszulSign i (J.1.erase j)) •
        (koszulMul R ι F j (t - ((p + 1 : ℕ) : ℤ)) (t + 1 - ((p + 1 : ℕ) : ℤ))
          (koszulDeg_shift t (p + 1)) ≫
        Sigma.ι (fun _ : KoszulIndex ι (p + 1) => (moduleTensorLeftFunctor (ProjectiveSpace R ι)
          (twistingSheaf R ι (t + 1 - ((p + 1 : ℕ) : ℤ)))).obj F) A) := by
  rw [← Category.assoc, ι_koszulContraction_of_mem R ι F t p j J
      (koszulIndexErase J j hj) hj rfl,
    Preadditive.zsmul_comp, Category.assoc,
    ι_koszulWedge_of_notMem R ι F t p i _ A (fun hm => hi (Finset.mem_of_mem_erase hm)) hA,
    Preadditive.comp_zsmul, smul_smul, ← Category.assoc,
    koszulMul_comp_eqToHom R ι F j (t - ((p + 1 : ℕ) : ℤ)) (koszulDeg_wedge t p)
      (koszulWedgeEq R ι F t p)
      (koszulDeg_contraction t p) (koszulDeg_shift t (p + 1))]

/-- Wedge and contraction with distinct coordinates anticommute. -/
theorem koszulWedge_contraction_add_of_ne (t : ℤ) (p : ℕ) {i j : ι} (hij : i ≠ j) :
    koszulWedge R ι F t (p + 1) i ≫ koszulContraction R ι F (t + 1) (p + 1) j +
      koszulContraction R ι F t p j ≫ koszulWedge R ι F t p i = 0 := by
  apply Sigma.hom_ext
  intro J
  rw [comp_zero, Preadditive.comp_add]
  by_cases hi : i ∈ J.1
  · rw [← Category.assoc, ι_koszulWedge_of_mem R ι F t (p + 1) i J hi, zero_comp, zero_add]
    by_cases hj : j ∈ J.1
    · rw [← Category.assoc, ι_koszulContraction_of_mem R ι F t p j J
          (koszulIndexErase J j hj) hj rfl,
        Preadditive.zsmul_comp, Category.assoc,
        ι_koszulWedge_of_mem R ι F t p i _ (Finset.mem_erase.mpr ⟨hij, hi⟩), comp_zero, smul_zero]
    · rw [← Category.assoc, ι_koszulContraction_of_notMem R ι F t p j J hj, zero_comp]
  · by_cases hj : j ∈ J.1
    · let A : KoszulIndex ι (p + 1) := ⟨(insert i J.1).erase j, by
        rw [Finset.card_erase_of_mem (Finset.mem_insert_of_mem hj),
          Finset.card_insert_of_notMem hi, J.2, Nat.add_sub_cancel]⟩
      rw [ι_koszulWedge_contraction_of_ne R ι F t p J A hi hj rfl,
        ι_koszulContraction_wedge_of_ne R ι F t p J A hi hj (Finset.erase_insert_of_ne hij),
        ← add_smul, koszulSign_insert_erase_add hi hj hij, zero_smul]
    · rw [← Category.assoc, ι_koszulWedge_of_notMem R ι F t (p + 1) i J
          (koszulIndexInsert J i hi) hi rfl,
        Preadditive.zsmul_comp, Category.assoc,
        ι_koszulContraction_of_notMem R ι F (t + 1) (p + 1) j _
          (fun hm => (Finset.mem_insert.mp hm).elim (fun h => hij h.symm) hj),
        comp_zero, smul_zero, zero_add, ← Category.assoc,
        ι_koszulContraction_of_notMem R ι F t p j J hj, zero_comp]

/-- The anticommutator of wedge and contraction with `i` on a summand containing `i`. -/
theorem ι_koszulWedge_contraction_add_self_of_mem (t : ℤ) (p : ℕ) (i : ι)
    (J : KoszulIndex ι (p + 1)) (hi : i ∈ J.1) :
    Sigma.ι (fun _ : KoszulIndex ι (p + 1) => (moduleTensorLeftFunctor (ProjectiveSpace R ι)
        (twistingSheaf R ι (t - ((p + 1 : ℕ) : ℤ)))).obj F) J ≫
        koszulContraction R ι F t p i ≫ koszulWedge R ι F t p i =
      koszulMul R ι F i (t - ((p + 1 : ℕ) : ℤ)) (t + 1 - ((p + 1 : ℕ) : ℤ))
          (koszulDeg_shift t (p + 1)) ≫
        Sigma.ι (fun _ : KoszulIndex ι (p + 1) => (moduleTensorLeftFunctor (ProjectiveSpace R ι)
          (twistingSheaf R ι (t + 1 - ((p + 1 : ℕ) : ℤ)))).obj F) J := by
  rw [← Category.assoc, ι_koszulContraction_of_mem R ι F t p i J
      (koszulIndexErase J i hi) hi rfl,
    Preadditive.zsmul_comp, Category.assoc,
    ι_koszulWedge_of_notMem R ι F t p i _ J (Finset.notMem_erase i J.1)
      (Finset.insert_erase hi).symm,
    Preadditive.comp_zsmul, smul_smul, ← Category.assoc,
    koszulMul_comp_eqToHom R ι F i (t - ((p + 1 : ℕ) : ℤ)) (koszulDeg_wedge t p)
      (koszulWedgeEq R ι F t p)
      (koszulDeg_contraction t p) (koszulDeg_shift t (p + 1))]
  rw [show koszulSign i (J.1.erase i) = koszulSign i J.1 from koszulSign_erase_self i J.1,
    koszulSign_mul_self, one_smul]

/-- The anticommutator of wedge and contraction with `i` on a summand not containing `i`. -/
theorem ι_koszulWedge_contraction_add_self_of_notMem (t : ℤ) (p : ℕ) (i : ι)
    (J : KoszulIndex ι (p + 1)) (hi : i ∉ J.1) :
    Sigma.ι (fun _ : KoszulIndex ι (p + 1) => (moduleTensorLeftFunctor (ProjectiveSpace R ι)
        (twistingSheaf R ι (t - ((p + 1 : ℕ) : ℤ)))).obj F) J ≫
        koszulWedge R ι F t (p + 1) i ≫ koszulContraction R ι F (t + 1) (p + 1) i =
      koszulMul R ι F i (t - ((p + 1 : ℕ) : ℤ)) (t + 1 - ((p + 1 : ℕ) : ℤ))
          (koszulDeg_shift t (p + 1)) ≫
        Sigma.ι (fun _ : KoszulIndex ι (p + 1) => (moduleTensorLeftFunctor (ProjectiveSpace R ι)
          (twistingSheaf R ι (t + 1 - ((p + 1 : ℕ) : ℤ)))).obj F) J := by
  rw [← Category.assoc, ι_koszulWedge_of_notMem R ι F t (p + 1) i J
      (koszulIndexInsert J i hi) hi rfl,
    Preadditive.zsmul_comp, Category.assoc,
    ι_koszulContraction_of_mem R ι F (t + 1) (p + 1) i _ J (Finset.mem_insert_self i J.1)
      (Finset.erase_insert hi).symm,
    Preadditive.comp_zsmul, smul_smul, ← Category.assoc,
    eqToHom_comp_koszulMul R ι F i (koszulDeg_wedge t (p + 1)) (koszulWedgeEq R ι F t (p + 1))
      (t + 1 - ((p + 1 : ℕ) : ℤ))
      (koszulDeg_contraction (t + 1) (p + 1)) (koszulDeg_shift t (p + 1))]
  rw [show koszulSign i (insert i J.1) = koszulSign i J.1 from koszulSign_insert_self i J.1,
    koszulSign_mul_self, one_smul]

/-- Wedge and contraction with the same coordinate: their anticommutator is multiplication by
that coordinate. -/
theorem koszulWedge_contraction_add_self (t : ℤ) (p : ℕ) (i : ι) :
    koszulWedge R ι F t (p + 1) i ≫ koszulContraction R ι F (t + 1) (p + 1) i +
      koszulContraction R ι F t p i ≫ koszulWedge R ι F t p i =
        koszulCoordinateMul R ι F t (p + 1) i := by
  apply Sigma.hom_ext
  intro J
  rw [Preadditive.comp_add, koszulCoordinateMul, Sigma.ι_comp_desc]
  by_cases hi : i ∈ J.1
  · rw [← Category.assoc, ι_koszulWedge_of_mem R ι F t (p + 1) i J hi, zero_comp, zero_add,
      ι_koszulWedge_contraction_add_self_of_mem R ι F t p i J hi]
  · rw [ι_koszulWedge_contraction_add_self_of_notMem R ι F t p i J hi, ← Category.assoc,
      ι_koszulContraction_of_notMem R ι F t p i J hi, zero_comp, add_zero]

/-- The wedges form a null-homotopy of coordinate multiplication on the Koszul complex: in every
positive degree, `h ∘ d + d ∘ h = Xᵢ`. -/
theorem koszul_homotopy (t : ℤ) (p : ℕ) (i : ι) :
    koszulWedge R ι F t (p + 1) i ≫ koszulDifferential R ι F (t + 1) (p + 1) +
      koszulDifferential R ι F t p ≫ koszulWedge R ι F t p i =
        koszulCoordinateMul R ι F t (p + 1) i := by
  simp only [koszulDifferential, Preadditive.comp_sum, Preadditive.sum_comp,
    ← Finset.sum_add_distrib]
  rw [Finset.sum_eq_single i]
  · exact koszulWedge_contraction_add_self R ι F t p i
  · intro j _ hji
    exact koszulWedge_contraction_add_of_ne R ι F t p (Ne.symm hji)
  · intro h
    exact absurd (Finset.mem_univ i) h

end AlgebraicGeometry.ProjectiveSpace
