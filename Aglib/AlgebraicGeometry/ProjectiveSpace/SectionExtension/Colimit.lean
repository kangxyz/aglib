/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Modules.Linear
public import Aglib.AlgebraicGeometry.ProjectiveSpace.SectionExtension.Bounds
public import Aglib.AlgebraicGeometry.ProjectiveSpace.Twisting.Frames
public import Mathlib.Algebra.Colimit.Module

/-!
# Chart sections as the colimit of negative-twist morphisms

Let `M` be a quasicoherent module on projective space `P = ProjectiveSpace R ι` with finitely
many coordinates, and fix a coordinate `i`. Evaluating a morphism `φ : O(-r) ⟶ M` on the standard
generator `X_i^{-r}` of `O(-r)` over the chart `D_+(X_i)` gives a section of `M` on that chart.
Precomposition with multiplication by `X_i^{N-r}` (`negativeTwistCoordinatePowerMap`) commutes
with this evaluation. The chart sections are the colimit of the morphism groups `O(-r) ⟶ M`
along these maps, in the following elementwise form:

* every chart section is the value of some `O(-N) ⟶ M` on the generator, for every large `N`
  (`exists_negativeTwistHom_generator_eventually`, in `SectionExtension.Bounds`);
* a morphism `O(-r) ⟶ M` vanishes on the generator if and only if its precomposition with
  some coordinate power `X_i^{N-r}` is zero (`twistingGenerator_eq_zero_iff_exists_comp_eq_zero`).

The precompositions form a directed system (`directedSystem_negativeTwistHomTransition`), linear
over any specified structural ring map `α : A →+* Γ(P, ⊤)`, and the chart evaluations induce a
linear equivalence from its `Module.DirectLimit` onto the chart sections with the restricted
structural action (`negativeTwistHomDirectLimitLinearEquiv`).

Through `Hom(O(-r), M) ≅ Γ(P, O(r) ⊗ M)` (`negativeTwistHomLinearEquivSections`, in
`ProjectiveSpace.Tensor.Equivalence.Hom`) this corresponds to the description of
`Γ(D_+(X_i), M)` as the direct limit of `Γ(P, M(r))` under multiplication by `X_i`,
[Stacks, Tag 01PW] and Hartshorne, *Algebraic Geometry*, II.5.14. The transport of the transition
maps along this identification, to multiplication by `X_i` on `Γ(P, M(r))`, is not formalized
here. The injectivity half uses the chart-level
annihilation `coordinateSection_exists_power_annihilate` on every chart and a common exponent
for the finitely many coordinates; no Noetherian or finite-type hypothesis is used.
-/

@[expose] public section

noncomputable section

open CategoryTheory Opposite MvPolynomial HomogeneousLocalization

universe u v

attribute [local instance] MvPolynomial.gradedAlgebra

namespace AlgebraicGeometry.ProjectiveSpace

variable (R : Type u) [CommRing R] (ι : Type u)

-- Like its source family `HomogeneousSections`, elaborated with `respectTransparency` off:
-- otherwise the `simp` call does not close the localization identity.
set_option backward.isDefEq.respectTransparency false in
/-- On the chart of `X_j`, the homogeneous fraction of `X_i^n` is the `n`th power of the
original ratio `X_i / X_j`. -/
theorem homogeneousChartFraction_coordinatePower_eq_pow (n : ℕ) (i j : ι) :
    homogeneousChartFraction R ι n (coordinatePower R ι n i) j =
      coordinateRatio R ι j i ^ n := by
  apply HomogeneousLocalization.val_injective
  simp [homogeneousChartFraction, coordinatePower, coordinateRatio, Localization.mk_pow]

/-- On the chart of `X_j`, the local coefficient of the global section `X_i^n` is the `n`th
power of the original ratio section `X_i / X_j`. -/
theorem homogeneousChartSection_coordinatePower (n : ℕ) (i j : ι) :
    homogeneousChartSection R ι n (coordinatePower R ι n i) j =
      coordinateRatioSection R ι j i ^ n := by
  rw [homogeneousChartSection, homogeneousChartFraction_coordinatePower_eq_pow, map_pow]
  rfl

-- The twisting-sheaf API (`Twisting.Frames`, `SectionExtension.Bounds`) is elaborated with
-- `respectTransparency` off; its section coercions and rewrite lemmas match only with it off.
set_option backward.isDefEq.respectTransparency false in
/-- On the chart of `X_j`, multiplication by `X_i^{N-N₀}` multiplies the standard frame
coefficient by `(X_i / X_j)^{N-N₀}`. -/
theorem negativeTwistCoordinatePowerMap_chart (i j : ι) (N₀ N : ℕ) (hN : N₀ ≤ N)
    (t : Γ(twistingSheaf R ι (-(N : ℤ)), coordinateOpen R ι j)) :
    twistingSectionsEquiv R ι (-(N₀ : ℤ)) j le_rfl
        ((negativeTwistCoordinatePowerMap R ι i N₀ N hN).val.app
          (op (coordinateOpen R ι j)) t) =
      coordinateRatioSection R ι j i ^ (N - N₀) *
        twistingSectionsEquiv R ι (-(N : ℤ)) j le_rfl t := by
  have hdeg : ((N - N₀ : ℕ) : ℤ) + -(N : ℤ) = -(N₀ : ℤ) := by omega
  change twistingSectionsEquiv R ι (-(N₀ : ℤ)) j le_rfl
      ((eqToHom (congrArg (twistingSheaf R ι) hdeg)).val.app
        (op (coordinateOpen R ι j))
        ((polynomialMultiplication R ι (N - N₀)
          (coordinatePower R ι (N - N₀) i) (-(N : ℤ))).val.app
            (op (coordinateOpen R ι j)) t)) = _
  rw [twistingSectionsEquiv_eqToHom R ι hdeg, polynomialMultiplication_local,
    homogeneousChartSection_coordinatePower]

-- The twisting-sheaf API (`Twisting.Frames`, `SectionExtension.Bounds`) is elaborated with
-- `respectTransparency` off; its section coercions and rewrite lemmas match only with it off.
set_option backward.isDefEq.respectTransparency false in
/-- On the chart of `X_j`, multiplication by `X_i^{N-N₀}` sends the standard generator to
`(X_i / X_j)^{N-N₀}` times the standard generator. -/
theorem negativeTwistCoordinatePowerMap_generator_chart (i j : ι) (N₀ N : ℕ)
    (hN : N₀ ≤ N) :
    (negativeTwistCoordinatePowerMap R ι i N₀ N hN).val.app (op (coordinateOpen R ι j))
        (twistingGenerator R ι (-(N : ℤ)) j le_rfl) =
      coordinateRatioSection R ι j i ^ (N - N₀) •
        twistingGenerator R ι (-(N₀ : ℤ)) j le_rfl := by
  apply (twistingSectionsEquiv R ι (-(N₀ : ℤ)) j le_rfl).injective
  rw [negativeTwistCoordinatePowerMap_chart, map_smul, twistingSectionsEquiv_generator,
    twistingSectionsEquiv_generator, smul_eq_mul]

-- The twisting-sheaf API (`Twisting.Frames`, `SectionExtension.Bounds`) is elaborated with
-- `respectTransparency` off; its section coercions and rewrite lemmas match only with it off.
set_option backward.isDefEq.respectTransparency false in
/-- A morphism from a twist vanishes if it vanishes on the standard generator of every
coordinate chart. -/
theorem twistingHom_eq_zero_of_generator {d : ℤ} {M : (ProjectiveSpace R ι).Modules}
    (φ : twistingSheaf R ι d ⟶ M)
    (h : ∀ j, φ.val.app (op (coordinateOpen R ι j)) (twistingGenerator R ι d j le_rfl) = 0) :
    φ = 0 := by
  apply hom_ext_of_coordinateSubopens R ι
  intro j V hj s
  rw [← twistingSectionsEquiv_smul_generator R ι d j hj s,
    ← twistingGenerator_restrict R ι d j hj le_rfl, (φ.val.app (op V)).hom.map_smul,
    PresheafOfModules.naturality_apply, h j, map_zero, smul_zero]
  rfl

-- The twisting-sheaf API (`Twisting.Frames`, `SectionExtension.Bounds`) is elaborated with
-- `respectTransparency` off; its section coercions and rewrite lemmas match only with it off.
set_option backward.isDefEq.respectTransparency false in
/-- Two morphisms from a twist agree if they agree on the standard generator of every coordinate
chart. -/
theorem twistingHom_ext_of_generator {d : ℤ} {M : (ProjectiveSpace R ι).Modules}
    {φ ψ : twistingSheaf R ι d ⟶ M}
    (h : ∀ j, φ.val.app (op (coordinateOpen R ι j)) (twistingGenerator R ι d j le_rfl) =
      ψ.val.app (op (coordinateOpen R ι j)) (twistingGenerator R ι d j le_rfl)) :
    φ = ψ := by
  apply hom_ext_of_coordinateSubopens R ι
  intro j V hj s
  rw [← twistingSectionsEquiv_smul_generator R ι d j hj s,
    ← twistingGenerator_restrict R ι d j hj le_rfl, (φ.val.app (op V)).hom.map_smul,
    (ψ.val.app (op V)).hom.map_smul, PresheafOfModules.naturality_apply,
    PresheafOfModules.naturality_apply, h j]

/-- Multiplication by `X_i^0` is the identity. -/
theorem negativeTwistCoordinatePowerMap_self (i : ι) (r : ℕ) :
    negativeTwistCoordinatePowerMap R ι i r r le_rfl = 𝟙 _ := by
  apply twistingHom_ext_of_generator R ι
  intro j
  rw [negativeTwistCoordinatePowerMap_generator_chart, Nat.sub_self, pow_zero, one_smul]
  rfl

-- The twisting-sheaf API (`Twisting.Frames`, `SectionExtension.Bounds`) is elaborated with
-- `respectTransparency` off; its section coercions and rewrite lemmas match only with it off.
set_option backward.isDefEq.respectTransparency false in
/-- Multiplication by `X_i^{s-r}` after multiplication by `X_i^{t-s}` is multiplication by
`X_i^{t-r}`. -/
theorem negativeTwistCoordinatePowerMap_comp (i : ι) (r s t : ℕ) (hrs : r ≤ s) (hst : s ≤ t) :
    negativeTwistCoordinatePowerMap R ι i s t hst ≫
        negativeTwistCoordinatePowerMap R ι i r s hrs =
      negativeTwistCoordinatePowerMap R ι i r t (hrs.trans hst) := by
  apply twistingHom_ext_of_generator R ι
  intro j
  change (negativeTwistCoordinatePowerMap R ι i r s hrs).val.app (op (coordinateOpen R ι j))
      ((negativeTwistCoordinatePowerMap R ι i s t hst).val.app (op (coordinateOpen R ι j))
        (twistingGenerator R ι (-(t : ℤ)) j le_rfl)) = _
  rw [negativeTwistCoordinatePowerMap_generator_chart,
    ((negativeTwistCoordinatePowerMap R ι i r s hrs).val.app _).hom.map_smul,
    negativeTwistCoordinatePowerMap_generator_chart,
    negativeTwistCoordinatePowerMap_generator_chart, smul_smul, ← pow_add,
    show t - s + (s - r) = t - r by omega]

variable {R ι} (M : (ProjectiveSpace R ι).Modules)

-- The twisting-sheaf API (`Twisting.Frames`, `SectionExtension.Bounds`) is elaborated with
-- `respectTransparency` off; its section coercions and rewrite lemmas match only with it off.
set_option backward.isDefEq.respectTransparency false in
/-- Precomposition with a coordinate power does not change the value on the generator of the
selected chart. -/
theorem negativeTwistCoordinatePowerMap_comp_generator (i : ι) (r N : ℕ) (hN : r ≤ N)
    (φ : twistingSheaf R ι (-(r : ℤ)) ⟶ M) :
    (negativeTwistCoordinatePowerMap R ι i r N hN ≫ φ).val.app (op (coordinateOpen R ι i))
        (twistingGenerator R ι (-(N : ℤ)) i le_rfl) =
      φ.val.app (op (coordinateOpen R ι i)) (twistingGenerator R ι (-(r : ℤ)) i le_rfl) := by
  change φ.val.app (op (coordinateOpen R ι i))
      ((negativeTwistCoordinatePowerMap R ι i r N hN).val.app (op (coordinateOpen R ι i))
        ((twistingSectionsEquiv R ι (-(N : ℤ)) i le_rfl).symm 1)) = _
  rw [negativeTwistCoordinatePowerMap_generator]
  rfl

-- The twisting-sheaf API (`Twisting.Frames`, `SectionExtension.Bounds`) is elaborated with
-- `respectTransparency` off; its section coercions and rewrite lemmas match only with it off.
set_option backward.isDefEq.respectTransparency false in
/-- If a morphism from a negative twist vanishes on the generator of the chart of `X_i`, its
value on the generator of every other chart restricts to zero on the overlap. -/
theorem twistingGenerator_restrict_overlap_eq_zero (i j : ι) (r : ℕ)
    (φ : twistingSheaf R ι (-(r : ℤ)) ⟶ M)
    (hφ : φ.val.app (op (coordinateOpen R ι i))
      (twistingGenerator R ι (-(r : ℤ)) i le_rfl) = 0) :
    M.presheaf.map (homOfLE (inf_le_left :
        coordinateOpen R ι j ⊓ coordinateOpen R ι i ≤ coordinateOpen R ι j)).op
      (φ.val.app (op (coordinateOpen R ι j)) (twistingGenerator R ι (-(r : ℤ)) j le_rfl)) =
      0 := by
  change M.val.map _ _ = 0
  rw [← PresheafOfModules.naturality_apply, twistingGenerator_restrict,
    twistingGenerator_transition R ι _ i j inf_le_right, (φ.val.app _).hom.map_smul,
    ← twistingGenerator_restrict R ι _ i (inf_le_right :
      coordinateOpen R ι j ⊓ coordinateOpen R ι i ≤ coordinateOpen R ι i) le_rfl,
    PresheafOfModules.naturality_apply, hφ, map_zero, smul_zero]

section Linear

variable {A : Type v} [CommRing A] (α : A →+* Γ(ProjectiveSpace R ι, ⊤))

/-- Evaluation on the standard generator of the chart of `X_i`, linear over any specified
structural ring map; the chart sections carry the restricted structural action. -/
def negativeTwistChartEval (i : ι) (d : ℤ) :
    letI := Scheme.Modules.moduleCategoryLinearOfHom (ProjectiveSpace R ι) α
    (twistingSheaf R ι d ⟶ M) →ₗ[A]
      (ModuleCat.restrictScalars (((ProjectiveSpace R ι).presheaf.map
        (homOfLE (le_top : coordinateOpen R ι i ≤ ⊤)).op).hom.comp α)).obj
        (ModuleCat.of Γ(ProjectiveSpace R ι, coordinateOpen R ι i)
          Γ(M, coordinateOpen R ι i)) := by
  letI := Scheme.Modules.moduleCategoryLinearOfHom (ProjectiveSpace R ι) α
  exact {
    toFun := fun φ => φ.val.app (op (coordinateOpen R ι i)) (twistingGenerator R ι d i le_rfl)
    map_add' := fun φ ψ => rfl
    map_smul' := fun a φ => Scheme.Modules.moduleCategoryLinearOfHom_smul_app _ α φ a _ _ }

theorem negativeTwistChartEval_apply (i : ι) (d : ℤ) (φ : twistingSheaf R ι d ⟶ M) :
    negativeTwistChartEval M α i d φ =
      φ.val.app (op (coordinateOpen R ι i)) (twistingGenerator R ι d i le_rfl) := rfl

/-- Precomposition with multiplication by `X_i^{s-r}`, linear over any specified structural ring
map. -/
def negativeTwistHomTransition (i : ι) (r s : ℕ) (h : r ≤ s) :
    letI := Scheme.Modules.moduleCategoryLinearOfHom (ProjectiveSpace R ι) α
    (twistingSheaf R ι (-(r : ℤ)) ⟶ M) →ₗ[A] (twistingSheaf R ι (-(s : ℤ)) ⟶ M) :=
  letI := Scheme.Modules.moduleCategoryLinearOfHom (ProjectiveSpace R ι) α
  Linear.leftComp A M (negativeTwistCoordinatePowerMap R ι i r s h)

theorem negativeTwistHomTransition_apply (i : ι) (r s : ℕ) (h : r ≤ s)
    (φ : twistingSheaf R ι (-(r : ℤ)) ⟶ M) :
    negativeTwistHomTransition M α i r s h φ = negativeTwistCoordinatePowerMap R ι i r s h ≫ φ :=
  rfl

/-- The precompositions with coordinate powers form a directed system. -/
theorem directedSystem_negativeTwistHomTransition (i : ι) :
    letI := Scheme.Modules.moduleCategoryLinearOfHom (ProjectiveSpace R ι) α
    DirectedSystem (fun r : ℕ => twistingSheaf R ι (-(r : ℤ)) ⟶ M)
      (negativeTwistHomTransition M α i · · ·) := by
  let := Scheme.Modules.moduleCategoryLinearOfHom (ProjectiveSpace R ι) α
  constructor
  · intro r φ
    change negativeTwistCoordinatePowerMap R ι i r r le_rfl ≫ φ = φ
    rw [negativeTwistCoordinatePowerMap_self, Category.id_comp]
  · intro t s r hrs hst φ
    change negativeTwistCoordinatePowerMap R ι i s t hst ≫
        negativeTwistCoordinatePowerMap R ι i r s hrs ≫ φ =
      negativeTwistCoordinatePowerMap R ι i r t (hrs.trans hst) ≫ φ
    rw [← Category.assoc, negativeTwistCoordinatePowerMap_comp]

end Linear

variable [M.IsQuasicoherent] [Finite ι]

-- The twisting-sheaf API (`Twisting.Frames`, `SectionExtension.Bounds`) is elaborated with
-- `respectTransparency` off; its section coercions and rewrite lemmas match only with it off.
set_option backward.isDefEq.respectTransparency false in
/-- **Injectivity half of the chart colimit.** If a morphism `O(-r) ⟶ M` vanishes on the
generator of the chart of `X_i`, then its precomposition with multiplication by `X_i^{N-r}` is
zero for all sufficiently large `N`. ([Stacks, Tag 01PW], Hartshorne II.5.14(a).) -/
theorem exists_negativeTwistCoordinatePowerMap_comp_eq_zero (i : ι) (r : ℕ)
    (φ : twistingSheaf R ι (-(r : ℤ)) ⟶ M)
    (hφ : φ.val.app (op (coordinateOpen R ι i))
      (twistingGenerator R ι (-(r : ℤ)) i le_rfl) = 0) :
    ∃ m : ℕ, ∀ (N : ℕ) (hN : r ≤ N), r + m ≤ N →
      negativeTwistCoordinatePowerMap R ι i r N hN ≫ φ = 0 := by
  classical
  let := Fintype.ofFinite ι
  choose n hn using fun j => coordinateSection_exists_power_annihilate R ι M j i _
    (twistingGenerator_restrict_overlap_eq_zero M i j r φ hφ)
  refine ⟨Finset.univ.sup n, fun N hN hmN => twistingHom_eq_zero_of_generator R ι _ ?_⟩
  intro j
  have hj : n j ≤ N - r := by
    have := Finset.le_sup (f := n) (Finset.mem_univ j)
    omega
  change φ.val.app (op (coordinateOpen R ι j))
      ((negativeTwistCoordinatePowerMap R ι i r N hN).val.app (op (coordinateOpen R ι j))
        (twistingGenerator R ι (-(N : ℤ)) j le_rfl)) = 0
  rw [negativeTwistCoordinatePowerMap_generator_chart, (φ.val.app _).hom.map_smul,
    ← Nat.sub_add_cancel hj, pow_add, mul_smul, hn j, smul_zero]

/-- **Kernel of the chart evaluation.** A morphism `O(-r) ⟶ M` vanishes on the generator of the
chart of `X_i` if and only if its precomposition with some coordinate power `X_i^{N-r}` is
zero. Together with `exists_negativeTwistHom_generator_eventually` this identifies the chart
sections with the colimit of `O(-r) ⟶ M` under multiplication by `X_i`
([Stacks, Tag 01PW]; Hartshorne II.5.14). -/
theorem twistingGenerator_eq_zero_iff_exists_comp_eq_zero (i : ι) (r : ℕ)
    (φ : twistingSheaf R ι (-(r : ℤ)) ⟶ M) :
    φ.val.app (op (coordinateOpen R ι i)) (twistingGenerator R ι (-(r : ℤ)) i le_rfl) = 0 ↔
      ∃ (N : ℕ) (hN : r ≤ N), negativeTwistCoordinatePowerMap R ι i r N hN ≫ φ = 0 := by
  constructor
  · intro hφ
    obtain ⟨m, hm⟩ := exists_negativeTwistCoordinatePowerMap_comp_eq_zero M i r φ hφ
    exact ⟨r + m, Nat.le_add_right r m, hm _ _ le_rfl⟩
  · rintro ⟨N, hN, h⟩
    rw [← negativeTwistCoordinatePowerMap_comp_generator M i r N hN φ, h]
    rfl

section DirectLimit

variable {A : Type v} [CommRing A] (α : A →+* Γ(ProjectiveSpace R ι, ⊤))

-- The twisting-sheaf API (`Twisting.Frames`, `SectionExtension.Bounds`) is elaborated with
-- `respectTransparency` off; its section coercions and rewrite lemmas match only with it off.
set_option backward.isDefEq.respectTransparency false in
/-- **Chart sections as a direct limit** ([Stacks, Tag 01PW]; Hartshorne II.5.14): for a
quasicoherent `M` and finitely many coordinates, evaluation on the chart generators identifies
the direct limit of `Hom(O(-r), M)` under multiplication by `X_i` with `Γ(D_+(X_i), M)`, linearly
over any specified structural ring map. -/
def negativeTwistHomDirectLimitLinearEquiv (i : ι) :
    letI := Scheme.Modules.moduleCategoryLinearOfHom (ProjectiveSpace R ι) α
    Module.DirectLimit (fun r : ℕ => twistingSheaf R ι (-(r : ℤ)) ⟶ M)
        (negativeTwistHomTransition M α i) ≃ₗ[A]
      (ModuleCat.restrictScalars (((ProjectiveSpace R ι).presheaf.map
        (homOfLE (le_top : coordinateOpen R ι i ≤ ⊤)).op).hom.comp α)).obj
        (ModuleCat.of Γ(ProjectiveSpace R ι, coordinateOpen R ι i)
          Γ(M, coordinateOpen R ι i)) := by
  letI := Scheme.Modules.moduleCategoryLinearOfHom (ProjectiveSpace R ι) α
  refine LinearEquiv.ofBijective (Module.DirectLimit.lift A ℕ _ (negativeTwistHomTransition M α i)
    (fun r => negativeTwistChartEval M α i (-(r : ℤ)))
    (fun r s h φ => negativeTwistCoordinatePowerMap_comp_generator M i r s h φ)) ⟨?_, ?_⟩
  · rw [injective_iff_map_eq_zero]
    intro z hz
    obtain ⟨r, φ, rfl⟩ := Module.DirectLimit.exists_of z
    rw [Module.DirectLimit.lift_of] at hz
    obtain ⟨N, hN, h⟩ := (twistingGenerator_eq_zero_iff_exists_comp_eq_zero M i r φ).mp hz
    rw [← Module.DirectLimit.of_f (hij := hN)]
    change Module.DirectLimit.of A ℕ _ (negativeTwistHomTransition M α i) N
      (negativeTwistCoordinatePowerMap R ι i r N hN ≫ φ) = 0
    rw [h, map_zero]
  · intro s
    obtain ⟨N₀, hN₀⟩ := exists_negativeTwistHom_generator_eventually R ι M i s
    obtain ⟨φ, hφ⟩ := hN₀ N₀ le_rfl
    exact ⟨Module.DirectLimit.of A ℕ _ (negativeTwistHomTransition M α i) N₀ φ, by
      rw [Module.DirectLimit.lift_of]
      exact hφ⟩

/-- The direct-limit equivalence sends the class of `φ : O(-r) ⟶ M` to its value on the chart
generator. -/
theorem negativeTwistHomDirectLimitLinearEquiv_of (i : ι) (r : ℕ)
    (φ : twistingSheaf R ι (-(r : ℤ)) ⟶ M) :
    letI := Scheme.Modules.moduleCategoryLinearOfHom (ProjectiveSpace R ι) α
    negativeTwistHomDirectLimitLinearEquiv M α i
        (Module.DirectLimit.of A ℕ _ (negativeTwistHomTransition M α i) r φ) =
      φ.val.app (op (coordinateOpen R ι i)) (twistingGenerator R ι (-(r : ℤ)) i le_rfl) := by
  let := Scheme.Modules.moduleCategoryLinearOfHom (ProjectiveSpace R ι) α
  exact Module.DirectLimit.lift_of (fun k : ℕ => negativeTwistChartEval M α i (-(k : ℤ)))
    (fun k l h ψ => negativeTwistCoordinatePowerMap_comp_generator M i k l h ψ) φ

end DirectLimit

end AlgebraicGeometry.ProjectiveSpace
