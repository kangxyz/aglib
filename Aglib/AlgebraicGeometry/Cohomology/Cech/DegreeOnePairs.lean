/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Cohomology.Cech.PairCocycles
public import Aglib.AlgebraicGeometry.Cohomology.Cech.FieldBaseChange
public import Aglib.CategoryTheory.Sites.SheafCohomology.Cech.ExactSequences

/-!
# Degree-one Čech homology of the structure sheaf as pair cohomology

Let `F` be a field, `X : FScheme F` and `U : ι → X.left.Opens`. The Čech complex
`structureCechComplex X U` (Mathlib's `cechComplexFunctor`, with the sections of the structure
sheaf as `F`-modules) has in degree `n` the product, over the tuples `σ : Fin (n + 1) → ι`, of
the sections over the categorical product `∏ᶜ fun k => U (σ k)`.

* `cechToPairs`: a degree-one cochain gives the pair cochain whose `(j, l)` entry is the
  `![j, l]` component restricted to `U j ⊓ U l`; this is an additive bijection
  (`cechPairsEquiv`).
* `cech_d_one_eq_zero_iff`: a degree-one cochain is a cycle if and only if its pair cochain is
  a pair cocycle (`Scheme.pairCocycles`).
* `cechToPairs_d_zero`: the pair cochain of a degree-zero coboundary is the pair coboundary
  (`Scheme.pairCoboundary`) of the restricted components.
* `pairCohomologyEquivCech : PairCohomology U ≃+ (structureCechComplex X U).homology 1`, and its
  compatibility with the structural scalars (`pairCohomologyEquivCech_smul`).

The differentials are read off with `CategoryTheory.Cech.cech_d_comp_π`. No covering,
finiteness or affineness hypothesis is used.
-/

@[expose] public section

noncomputable section


open CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite
open AlgebraicGeometry.Scheme.OverField
open AlgebraicGeometry.Scheme.Modules.Invertible (sectionRestrict sectionRestrict_comp
  sectionRestrict_refl)

universe u

namespace AlgebraicGeometry.Scheme.Cohomology

variable {F : Type u} [Field F] (X : FScheme F) {ι : Type u} (U : ι → X.left.Opens)

section Opens

theorem cechTuple_le {n : ℕ} (σ : Fin (n + 1) → ι) (k : Fin (n + 1)) :
    (∏ᶜ fun k => U (σ k)) ≤ U (σ k) :=
  leOfHom (Pi.π (fun k => U (σ k)) k)

theorem le_cechTuple {n : ℕ} (σ : Fin (n + 1) → ι) {V : X.left.Opens}
    (h : ∀ k, V ≤ U (σ k)) : V ≤ ∏ᶜ fun k => U (σ k) :=
  leOfHom (Pi.lift fun k => homOfLE (h k))

theorem inf_le_cechPair (j l : ι) : U j ⊓ U l ≤ ∏ᶜ fun k => U (![j, l] k) :=
  le_cechTuple X U ![j, l] (by
    intro k
    fin_cases k
    exacts [inf_le_left, inf_le_right])

theorem cechPair_le_inf (σ : Fin 2 → ι) : (∏ᶜ fun k => U (σ k)) ≤ U (σ 0) ⊓ U (σ 1) :=
  le_inf (cechTuple_le X U σ 0) (cechTuple_le X U σ 1)

theorem le_cechSingle (j : ι) : U j ≤ ∏ᶜ fun k => U (![j] k) :=
  le_cechTuple X U ![j] (by
    intro k
    fin_cases k
    exact le_rfl)

theorem cechTuple_le_face {n : ℕ} (σ : Fin (n + 2) → ι) (t : Fin (n + 2)) :
    (∏ᶜ fun k => U (σ k)) ≤ ∏ᶜ fun k => U (σ (t.succAbove k)) :=
  le_cechTuple X U _ fun k => cechTuple_le X U σ (t.succAbove k)

end Opens

/-- The factors of the degree-`n` Čech cochains. -/
abbrev cechFactor (n : ℕ) (σ : Fin (n + 1) → ι) : ModuleCat.{u} F :=
  (structureSectionsPresheaf X).obj (op (∏ᶜ fun k => U (σ k)))

/-- The `σ` component of a Čech cochain, restricted to an open `V` of the intersection. -/
def cechRestrict {n : ℕ} (x : (structureCechComplex X U).X n) (σ : Fin (n + 1) → ι)
    (V : X.left.Opens) (hV : V ≤ ∏ᶜ fun k => U (σ k)) : Γ(X.left, V) :=
  sectionRestrict X.left hV ((Pi.π (cechFactor X U n) σ).hom x)

variable {X U}

theorem cechRestrict_restrict {n : ℕ} (x : (structureCechComplex X U).X n)
    (σ : Fin (n + 1) → ι) {V W : X.left.Opens} (hW : W ≤ ∏ᶜ fun k => U (σ k)) (hVW : V ≤ W) :
    sectionRestrict X.left hVW (cechRestrict X U x σ W hW) =
      cechRestrict X U x σ V (hVW.trans hW) :=
  sectionRestrict_comp _ _ _ _

theorem cechRestrict_congr {n : ℕ} (x : (structureCechComplex X U).X n)
    {σ τ : Fin (n + 1) → ι} (e : σ = τ) (V : X.left.Opens) (hσ : V ≤ ∏ᶜ fun k => U (σ k))
    (hτ : V ≤ ∏ᶜ fun k => U (τ k)) : cechRestrict X U x σ V hσ = cechRestrict X U x τ V hτ := by
  subst e
  rfl

theorem cechRestrict_self {n : ℕ} (x : (structureCechComplex X U).X n) (σ : Fin (n + 1) → ι) :
    cechRestrict X U x σ _ le_rfl = (Pi.π (cechFactor X U n) σ).hom x :=
  sectionRestrict_refl _ _ _

-- The Čech factors `ModuleCat.of F Γ(X, W)` match the section rings only after unfolding.
set_option backward.isDefEq.respectTransparency false in
theorem cechRestrict_add {n : ℕ} (x y : (structureCechComplex X U).X n) (σ : Fin (n + 1) → ι)
    (V : X.left.Opens) (hV : V ≤ ∏ᶜ fun k => U (σ k)) :
    cechRestrict X U (x + y) σ V hV = cechRestrict X U x σ V hV + cechRestrict X U y σ V hV := by
  rw [cechRestrict, cechRestrict, cechRestrict, map_add, map_add]

-- The Čech factors `ModuleCat.of F Γ(X, W)` match the section rings only after unfolding.
set_option backward.isDefEq.respectTransparency false in
theorem cechRestrict_zero {n : ℕ} (σ : Fin (n + 1) → ι) (V : X.left.Opens)
    (hV : V ≤ ∏ᶜ fun k => U (σ k)) :
    cechRestrict X U (0 : (structureCechComplex X U).X n) σ V hV = 0 := by
  rw [cechRestrict, map_zero, map_zero]

/-- Cochains are determined by their components. -/
theorem cech_ext {n : ℕ} {x y : (structureCechComplex X U).X n}
    (h : ∀ σ, (Pi.π (cechFactor X U n) σ).hom x = (Pi.π (cechFactor X U n) σ).hom y) :
    x = y := by
  apply (ConcreteCategory.bijective_of_isIso (ModuleCat.piIsoPi (cechFactor X U n)).hom).injective
  funext σ
  have hx := ModuleCat.piIsoPi_hom_ker_subtype_apply (cechFactor X U n) σ x
  have hy := ModuleCat.piIsoPi_hom_ker_subtype_apply (cechFactor X U n) σ y
  exact hx.trans ((h σ).trans hy.symm)

theorem π_piIsoPi_inv {n : ℕ} (f : ∀ σ : Fin (n + 1) → ι, cechFactor X U n σ)
    (σ : Fin (n + 1) → ι) :
    (Pi.π (cechFactor X U n) σ).hom ((ModuleCat.piIsoPi (cechFactor X U n)).inv f) = f σ :=
  ModuleCat.piIsoPi_inv_kernel_ι_apply (cechFactor X U n) σ f

-- The Čech factors `ModuleCat.of F Γ(X, W)` match the section rings only after unfolding.
set_option backward.isDefEq.respectTransparency false in
/-- The component formula of a Čech differential, restricted to an open of the intersection. -/
theorem cechRestrict_d {n : ℕ} (x : (structureCechComplex X U).X n) (σ : Fin (n + 2) → ι)
    (V : X.left.Opens) (hV : V ≤ ∏ᶜ fun k => U (σ k)) :
    cechRestrict X U ((structureCechComplex X U).d n (n + 1) x) σ V hV =
      ∑ t : Fin (n + 2), (-1 : ℤ) ^ (t : ℕ) •
        cechRestrict X U x (fun k => σ (t.succAbove k)) V
          (hV.trans (cechTuple_le_face X U σ t)) := by
  have e := congrArg (fun φ => sectionRestrict X.left hV (φ.hom x))
    (CategoryTheory.Cech.cech_d_comp_π U (structureSectionsPresheaf X) n σ)
  simp only [ModuleCat.hom_comp, LinearMap.comp_apply, ModuleCat.hom_sum, LinearMap.sum_apply,
    ModuleCat.hom_zsmul, LinearMap.smul_apply, map_sum, map_zsmul] at e
  refine e.trans (Finset.sum_congr rfl fun t _ => ?_)
  congr 1
  exact sectionRestrict_comp _ _ _ _

/-- Degree-one Čech cochains as pair cochains on the pairwise intersections. -/
def cechToPairs (x : (structureCechComplex X U).X 1) : ∀ j l : ι, Γ(X.left, U j ⊓ U l) :=
  fun j l => cechRestrict X U x ![j, l] _ (inf_le_cechPair X U j l)

/-- Pair cochains as degree-one Čech cochains. -/
def cechOfPairs (b : ∀ j l : ι, Γ(X.left, U j ⊓ U l)) : (structureCechComplex X U).X 1 :=
  (ModuleCat.piIsoPi (cechFactor X U 1)).inv
    fun σ => sectionRestrict X.left (cechPair_le_inf X U σ) (b (σ 0) (σ 1))

-- The Čech factors `ModuleCat.of F Γ(X, W)` match the section rings only after unfolding.
set_option backward.isDefEq.respectTransparency false in
theorem cechToPairs_cechOfPairs (b : ∀ j l : ι, Γ(X.left, U j ⊓ U l)) :
    cechToPairs (cechOfPairs b) = b := by
  funext j l
  rw [cechToPairs, cechRestrict, cechOfPairs, π_piIsoPi_inv, sectionRestrict_comp]
  exact sectionRestrict_refl _ _ _

theorem cechToPairs_restrict (x : (structureCechComplex X U).X 1) (j l : ι) {V : X.left.Opens}
    (hV : V ≤ U j ⊓ U l) :
    sectionRestrict X.left hV (cechToPairs x j l) =
      cechRestrict X U x ![j, l] V (hV.trans (inf_le_cechPair X U j l)) :=
  cechRestrict_restrict _ _ _ _

-- The Čech factors `ModuleCat.of F Γ(X, W)` match the section rings only after unfolding.
set_option backward.isDefEq.respectTransparency false in
theorem cechOfPairs_cechToPairs (x : (structureCechComplex X U).X 1) :
    cechOfPairs (cechToPairs x) = x := by
  apply cech_ext
  intro σ
  rw [cechOfPairs, π_piIsoPi_inv, cechToPairs_restrict, ← cechRestrict_self]
  apply cechRestrict_congr
  funext k
  fin_cases k <;> rfl

theorem cechToPairs_add (x y : (structureCechComplex X U).X 1) :
    cechToPairs (x + y) = cechToPairs x + cechToPairs y := by
  funext j l
  exact cechRestrict_add x y _ _ _

variable (X U) in
/-- Degree-one Čech cochains are pair cochains. -/
def cechPairsEquiv : (structureCechComplex X U).X 1 ≃+ (∀ j l : ι, Γ(X.left, U j ⊓ U l)) where
  toFun := cechToPairs
  invFun := cechOfPairs
  left_inv := cechOfPairs_cechToPairs
  right_inv := cechToPairs_cechOfPairs
  map_add' := cechToPairs_add

theorem le_cechPair_of {V : X.left.Opens} {j l : ι} (hj : V ≤ U j) (hl : V ≤ U l) :
    V ≤ ∏ᶜ fun k => U (![j, l] k) :=
  (le_inf hj hl).trans (inf_le_cechPair X U j l)

/-- The degree-one differential on components: `x₁₂ - x₀₂ + x₀₁`. -/
theorem cechRestrict_d_one (x : (structureCechComplex X U).X 1) (σ : Fin 3 → ι)
    (V : X.left.Opens) (hV : V ≤ ∏ᶜ fun k => U (σ k)) :
    cechRestrict X U ((structureCechComplex X U).d 1 2 x) σ V hV =
      cechRestrict X U x ![σ 1, σ 2] V
          (le_cechPair_of (hV.trans (cechTuple_le X U σ 1)) (hV.trans (cechTuple_le X U σ 2))) -
        cechRestrict X U x ![σ 0, σ 2] V
          (le_cechPair_of (hV.trans (cechTuple_le X U σ 0)) (hV.trans (cechTuple_le X U σ 2))) +
        cechRestrict X U x ![σ 0, σ 1] V
          (le_cechPair_of (hV.trans (cechTuple_le X U σ 0)) (hV.trans (cechTuple_le X U σ 1))) := by
  refine (cechRestrict_d (n := 1) x σ V hV).trans ?_
  rw [Fin.sum_univ_three,
    cechRestrict_congr x (show (fun k => σ ((0 : Fin 3).succAbove k)) = ![σ 1, σ 2] by
      funext k; fin_cases k <;> rfl) V _
      (le_cechPair_of (hV.trans (cechTuple_le X U σ 1)) (hV.trans (cechTuple_le X U σ 2))),
    cechRestrict_congr x (show (fun k => σ ((1 : Fin 3).succAbove k)) = ![σ 0, σ 2] by
      funext k; fin_cases k <;> rfl) V _
      (le_cechPair_of (hV.trans (cechTuple_le X U σ 0)) (hV.trans (cechTuple_le X U σ 2))),
    cechRestrict_congr x (show (fun k => σ ((2 : Fin 3).succAbove k)) = ![σ 0, σ 1] by
      funext k; fin_cases k <;> rfl) V _
      (le_cechPair_of (hV.trans (cechTuple_le X U σ 0)) (hV.trans (cechTuple_le X U σ 1)))]
  simp only [Fin.val_zero, Fin.val_one, Fin.val_two, pow_zero, pow_one, neg_one_sq, one_zsmul,
    neg_one_zsmul, sub_eq_add_neg]

/-- The degree-zero differential on components: `y₁ - y₀`. -/
theorem cechRestrict_d_zero (y : (structureCechComplex X U).X 0) (σ : Fin 2 → ι)
    (V : X.left.Opens) (hV : V ≤ ∏ᶜ fun k => U (σ k)) :
    cechRestrict X U ((structureCechComplex X U).d 0 1 y) σ V hV =
      cechRestrict X U y ![σ 1] V (le_cechTuple X U _ (by
          intro k; fin_cases k; exact hV.trans (cechTuple_le X U σ 1))) -
        cechRestrict X U y ![σ 0] V (le_cechTuple X U _ (by
          intro k; fin_cases k; exact hV.trans (cechTuple_le X U σ 0))) := by
  refine (cechRestrict_d (n := 0) y σ V hV).trans ?_
  rw [Fin.sum_univ_two,
    cechRestrict_congr y (show (fun k => σ ((0 : Fin 2).succAbove k)) = ![σ 1] by
      funext k; fin_cases k; rfl) V _ (le_cechTuple X U _ (by
        intro k; fin_cases k; exact hV.trans (cechTuple_le X U σ 1))),
    cechRestrict_congr y (show (fun k => σ ((1 : Fin 2).succAbove k)) = ![σ 0] by
      funext k; fin_cases k; rfl) V _ (le_cechTuple X U _ (by
        intro k; fin_cases k; exact hV.trans (cechTuple_le X U σ 0)))]
  simp only [Fin.val_zero, Fin.val_one, pow_zero, pow_one, one_zsmul, neg_one_zsmul,
    sub_eq_add_neg]

-- The Čech factors `ModuleCat.of F Γ(X, W)` match the section rings only after unfolding.
set_option backward.isDefEq.respectTransparency false in
/-- A degree-one cochain is a cycle exactly when its pair cochain is a pair cocycle. -/
theorem cech_d_one_eq_zero_iff (x : (structureCechComplex X U).X 1) :
    (structureCechComplex X U).d 1 2 x = 0 ↔ cechToPairs x ∈ pairCocycles U := by
  rw [mem_pairCocycles_iff]
  constructor
  · intro hx j l m V hj hl hm
    have hV : V ≤ ∏ᶜ fun k => U (![j, l, m] k) := le_cechTuple X U _ (by
      intro k
      fin_cases k
      exacts [hj, hl, hm])
    have e := cechRestrict_d_one x ![j, l, m] V hV
    rw [hx, cechRestrict_zero] at e
    change 0 = cechRestrict X U x ![l, m] V _ - cechRestrict X U x ![j, m] V _ +
      cechRestrict X U x ![j, l] V _ at e
    rw [cechToPairs_restrict, cechToPairs_restrict, cechToPairs_restrict]
    linear_combination -e
  · intro hx
    apply cech_ext
    intro σ
    rw [map_zero, ← cechRestrict_self, cechRestrict_d_one]
    have hc := hx (σ 0) (σ 1) (σ 2) (∏ᶜ fun k => U (σ k)) (cechTuple_le X U σ 0)
      (cechTuple_le X U σ 1) (cechTuple_le X U σ 2)
    rw [cechToPairs_restrict, cechToPairs_restrict, cechToPairs_restrict] at hc
    linear_combination hc

/-- Degree-zero Čech cochains restricted to the members of the family. -/
def cechToSingles (y : (structureCechComplex X U).X 0) : ∀ j : ι, Γ(X.left, U j) :=
  fun j => cechRestrict X U y ![j] _ (le_cechSingle X U j)

/-- Sections on the members of the family as degree-zero Čech cochains. -/
def cechOfSingles (a : ∀ j : ι, Γ(X.left, U j)) : (structureCechComplex X U).X 0 :=
  (ModuleCat.piIsoPi (cechFactor X U 0)).inv
    fun σ => sectionRestrict X.left (cechTuple_le X U σ 0) (a (σ 0))

-- The Čech factors `ModuleCat.of F Γ(X, W)` match the section rings only after unfolding.
set_option backward.isDefEq.respectTransparency false in
theorem cechToSingles_cechOfSingles (a : ∀ j : ι, Γ(X.left, U j)) :
    cechToSingles (cechOfSingles a) = a := by
  funext j
  rw [cechToSingles, cechRestrict, cechOfSingles, π_piIsoPi_inv, sectionRestrict_comp]
  exact sectionRestrict_refl _ _ _

/-- The pair cochain of a degree-zero coboundary is the pair coboundary. -/
theorem cechToPairs_d_zero (y : (structureCechComplex X U).X 0) :
    cechToPairs ((structureCechComplex X U).d 0 1 y) = pairCoboundary U (cechToSingles y) := by
  funext j l
  rw [cechToPairs, cechRestrict_d_zero, pairCoboundary_apply, cechToSingles, cechToSingles,
    cechRestrict_restrict, cechRestrict_restrict]
  rfl

section Homology

variable (X U)

/-- The degree-one cycles of the structure Čech complex are the pair cocycles. -/
def cechCyclesEquiv :
    LinearMap.ker ((structureCechComplex X U).d 1 2).hom ≃+ pairCocycles U where
  toFun x := ⟨cechToPairs x.1, (cech_d_one_eq_zero_iff x.1).mp (LinearMap.mem_ker.mp x.2)⟩
  invFun b := ⟨cechOfPairs b.1, LinearMap.mem_ker.mpr ((cech_d_one_eq_zero_iff _).mpr (by
    rw [cechToPairs_cechOfPairs]
    exact b.2))⟩
  left_inv x := Subtype.ext (cechOfPairs_cechToPairs x.1)
  right_inv b := Subtype.ext (cechToPairs_cechOfPairs b.1)
  map_add' x y := Subtype.ext (cechToPairs_add x.1 y.1)

/-- The degree-one boundaries correspond to the pair coboundaries. -/
theorem map_range_cechCyclesEquiv :
    (LinearMap.range ((structureCechComplex X U).sc' 0 1 2).moduleCatToCycles).toAddSubgroup.map
      (cechCyclesEquiv X U : LinearMap.ker ((structureCechComplex X U).d 1 2).hom →+
        pairCocycles U) = pairCoboundaries U := by
  ext b
  constructor
  · rintro ⟨_, ⟨y, rfl⟩, rfl⟩
    exact ⟨cechToSingles y, Subtype.ext (cechToPairs_d_zero y).symm⟩
  · rintro ⟨a, rfl⟩
    refine ⟨_, ⟨cechOfSingles a, rfl⟩, ?_⟩
    apply Subtype.ext
    change cechToPairs ((structureCechComplex X U).d 0 1 (cechOfSingles a)) = pairCoboundary U a
    rw [cechToPairs_d_zero, cechToSingles_cechOfSingles]

/-- The linear identification of the explicit kernel-modulo-image quotient with the
degree-one homology of the structure Čech complex. -/
def cechHomologyOneLinearEquiv :
    (((structureCechComplex X U).sc' 0 1 2).moduleCatLeftHomologyData.H) ≃ₗ[F]
      (structureCechComplex X U).homology 1 :=
  (((structureCechComplex X U).sc' 0 1 2).moduleCatHomologyIso.symm ≪≫
    ((structureCechComplex X U).homologyIsoSc' 0 1 2 ((ComplexShape.up ℕ).prev_eq' rfl)
      ((ComplexShape.up ℕ).next_eq' rfl)).symm).toLinearEquiv

-- The Čech factors `ModuleCat.of F Γ(X, W)` match the section rings only after unfolding.
set_option backward.isDefEq.respectTransparency false in
/-- Pair cohomology is the degree-one homology of the structure Čech complex. -/
def pairCohomologyEquivCech : PairCohomology U ≃+ (structureCechComplex X U).homology 1 :=
  (QuotientAddGroup.congr _ _ (cechCyclesEquiv X U) (map_range_cechCyclesEquiv X U)).symm.trans
    (cechHomologyOneLinearEquiv X U).toAddEquiv

/-- Multiplication of pair cochains by the structural constants. -/
def pairSMul (a : F) (b : ∀ j l : ι, Γ(X.left, U j ⊓ U l)) : ∀ j l : ι, Γ(X.left, U j ⊓ U l) :=
  fun j l => constantSection X (U j ⊓ U l) a * b j l

theorem sectionRestrict_constantSection_mul {V W : X.left.Opens} (h : V ≤ W) (a : F)
    (s : Γ(X.left, W)) :
    sectionRestrict X.left h (constantSection X W a * s) =
      constantSection X V a * sectionRestrict X.left h s := by
  rw [map_mul]
  congr 1
  exact map_constantSection X (homOfLE h) a

theorem pairSMul_mem (a : F) {b : ∀ j l : ι, Γ(X.left, U j ⊓ U l)} (hb : b ∈ pairCocycles U) :
    pairSMul X U a b ∈ pairCocycles U := by
  rw [mem_pairCocycles_iff] at hb ⊢
  intro j l m V hj hl hm
  simp only [pairSMul, sectionRestrict_constantSection_mul]
  rw [← mul_add, hb j l m V hj hl hm]

variable {X U} in
-- The Čech factors `ModuleCat.of F Γ(X, W)` match the section rings only after unfolding.
set_option backward.isDefEq.respectTransparency false in
theorem cechToPairs_smul (a : F) (x : (structureCechComplex X U).X 1) :
    cechToPairs (a • x) = pairSMul X U a (cechToPairs x) := by
  funext j l
  rw [cechToPairs, cechRestrict, map_smul]
  exact sectionRestrict_constantSection_mul X _ a _

-- The Čech factors `ModuleCat.of F Γ(X, W)` match the section rings only after unfolding.
set_option backward.isDefEq.respectTransparency false in
/-- The comparison carries the structural scalar multiplication of pair cocycles to the scalar
multiplication of Čech homology. -/
theorem pairCohomologyEquivCech_smul (a : F) (b : pairCocycles U) :
    pairCohomologyEquivCech X U
        (QuotientAddGroup.mk ⟨pairSMul X U a b.1, pairSMul_mem X U a b.2⟩) =
      a • pairCohomologyEquivCech X U (QuotientAddGroup.mk b) := by
  change cechHomologyOneLinearEquiv X U (Submodule.Quotient.mk
      ((cechCyclesEquiv X U).symm ⟨pairSMul X U a b.1, pairSMul_mem X U a b.2⟩)) =
    a • cechHomologyOneLinearEquiv X U (Submodule.Quotient.mk ((cechCyclesEquiv X U).symm b))
  rw [← LinearEquiv.map_smul, ← Submodule.Quotient.mk_smul]
  congr 2
  apply (cechCyclesEquiv X U).injective
  rw [AddEquiv.apply_symm_apply]
  apply Subtype.ext
  change pairSMul X U a b.1 =
    cechToPairs (a • cechOfPairs (b : ∀ j l : ι, Γ(X.left, U j ⊓ U l)))
  rw [cechToPairs_smul, cechToPairs_cechOfPairs]

end Homology

end AlgebraicGeometry.Scheme.Cohomology
