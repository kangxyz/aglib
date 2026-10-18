/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Cohomology.Projective.FiberBaseChange
public import Aglib.AlgebraicGeometry.Cohomology.Projective.Projection.Coherence
public import Aglib.AlgebraicGeometry.FlatteningStratification.Closed
public import Aglib.Algebra.Polynomial.RationalValues
public import Aglib.RingTheory.FittingIdeal.Stratification

/-!
# The strata `S_f` of the flattening stratification

Let `A` be a Noetherian ring, `ι ≃ Fin (n + 1)` and `F` a coherent module on `P^n_A`, flat or not.
This file constructs the strata `S_f` of Nitsure, *Construction of Hilbert and Quot schemes*,
arXiv:math/0504590v1, proof of Thm 4.3, p. 22, over the affine base `S = Spec A`, and proves
statements (i) and (iii) of the theorem (p. 19) for them.

* **Fibre ranks of the direct images.** `directImageTwist F d` is `E_d = π_* F(d)` on `Spec A`;
  it is coherent (`affineLocallyFiniteType_directImageTwist`), and its global sections are
  `H^0(P^n_A, F(d))`, `A`-linearly (`directImageTwistSectionsLinearEquiv`). Fibre ranks on
  `Spec A` are read from the Fitting ideals of the global sections
  (`Scheme.Modules.sheafRank_le_iff_fittingIdeal_moduleSpecΓFunctor`, in
  `Modules/FittingIdeal/LocallyFree`), so where the fibre statements (B) and (C) hold, the fibre
  of `π_* F(d)` at `y` has dimension `χ(F_y(d))` (`sheafRank_directImageTwist`), the value at `d`
  of the fibre Hilbert polynomial `P_y` (`sheafRank_directImageTwist_eq_eval`).
  `IsFiberBaseChangeBound F N` says that the fibre statements of (B) and (C) hold beyond `N`: the
  positive cohomology of every fibre of `F(d)` vanishes and every fibre base-change map of `F(d)`
  in degree zero is an isomorphism. It does not contain the vanishing of `H^r(P^n_A, F(d))`
  itself. Such `N` exists (`exists_isFiberBaseChangeBound`, from `FiberBaseChange`).
* **Re-indexing by polynomials** (p. 22). The Hilbert polynomials of coherent sheaves on `P^n_k`
  have degree `≤ n` (`natDegree_projectiveHilbertPolynomial_le`, in
  `Cohomology/Projective/HilbertPolynomial/NatDegree`), so for every `N` the map
  `f ↦ (f(N), …, f(N + n))` is injective on the polynomials that occur
  (`injOn_eval_projectiveHilbertPolynomial_fiber`, in `HilbertPolynomial/Finiteness`, from
  `Polynomial.eq_of_natDegree_le_of_eval_add_eq`, in `Algebra/Polynomial/RationalValues`).
* **The strata.** `hilbertPolynomialStratum n e F hF N f` is the refined joint rank stratum of
  `FlatteningStratification/Closed` for the family `E_i = π_* F(N + i)`, `i ≥ 0`, the ranks
  `e_i = f(N + i)` (`hilbertPolynomialRank`) and the open conditions `J₀ = {0, …, n}`: Nitsure's
  closed subscheme `S_f ⊆ W_f` cut out by `Σ_{i ≥ 0} I_i` inside the joint stratum `W_f` of
  `E_0, …, E_n`, for `f` that occurs and `N` a bound of the fibre statements of (B) and (C). Its
  points are described by `mem_range_refinedJointRankStratumι_iff` (in `Closed`).
* **Theorem 4.3 (i)** (`range_hilbertPolynomialStratumι`, `exists_range_hilbertPolynomialStratumι`):
  for `N` beyond the fibre statements of (B) and (C) and `f` a polynomial that occurs,
  `|S_f| = {s : P_s = f}`.
* **The universal property of `S_f`** (`exists_lift_hilbertPolynomialStratumι_iff`, p. 22): for
  `N` beyond the fibre statements of (B) and (C) and `f` a polynomial that occurs,
  `g : T ⟶ Spec A` factors through `S_f` if and only if every `g^* π_* F(N + i)` is finite
  locally free of rank `f(N + i)`. This discharges, for Nitsure's sheaves and `f` that occurs,
  the hypothesis of `exists_lift_refinedJointRankStratumι_iff`.
* **Theorem 4.3 (iii)** (`closure_range_hilbertPolynomialStratumι_subset`, p. 23): the closure of
  `|S_f|` lies in the union of the `|S_g|`, `g` occurring with `f(m) ≤ g(m)` for `m ≫ 0`. As in
  Nitsure's proof, one `p ≥ N` orders the finitely many polynomials that occur
  (`Polynomial.exists_eval_le_imp_eventually_le`, with (A)), and the case `n = 0`
  (`closure_range_rankStratumι_subset`) is applied to `π_* F(p)`. For polynomials,
  "`f(m) ≤ g(m)` for `m ≫ 0`" is Nitsure's `f ≤ g`: distinct polynomials eventually differ.

The universal property (ii) of the coproduct `∐ S_f ⟶ S` (flatness) is not part of this file.
-/

@[expose] public section

noncomputable section

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry.ProjectiveSpace
open AlgebraicGeometry.Scheme.Modules AlgebraicGeometry.Scheme.Modules.QuasiCoherent
open scoped TensorProduct

universe u

namespace AlgebraicGeometry.Scheme.Cohomology

variable {A : Type u} [CommRing A] {ι : Type u}

/-! ### The direct images `E_d = π_* F(d)` -/

/-- Nitsure's direct image `E_d = π_* F(d)` on `Spec A`, for `π : P^n_A ⟶ Spec A`. -/
abbrev directImageTwist (F : (ProjectiveSpace A ι).Modules) (d : ℤ) :
    (Spec (CommRingCat.of A)).Modules :=
  (Scheme.Modules.pushforward (toSpec A ι)).obj
    ((moduleTensorLeftFunctor (ProjectiveSpace A ι) (twistingSheaf A ι d)).obj F)

/-- **Global sections of the direct image** `E_d = π_* F(d)` on `Spec A` are
`H^0(P^n_A, F(d))`, `A`-linearly. -/
def directImageTwistSectionsLinearEquiv [IsNoetherianRing A] [Finite ι]
    (F : (ProjectiveSpace A ι).Modules)
    (hF : affineLocallyFiniteType (ProjectiveSpace A ι) F) (d : ℤ) :
    letI := moduleCohomologyModuleOfHom (ProjectiveSpace A ι)
      ((toSpec A ι).appTop.hom.comp (Scheme.ΓSpecIso (CommRingCat.of A)).inv.hom)
      ((moduleTensorLeftFunctor (ProjectiveSpace A ι) (twistingSheaf A ι d)).obj F) 0
    moduleSpecΓFunctor.obj (directImageTwist F d) ≃ₗ[A]
      Sheaf.H.{u + 1} (moduleAddSheaf (ProjectiveSpace A ι)
        ((moduleTensorLeftFunctor (ProjectiveSpace A ι) (twistingSheaf A ι d)).obj F)) 0 :=
  letI := moduleCohomologyModuleOfHom (ProjectiveSpace A ι)
    ((toSpec A ι).appTop.hom.comp (Scheme.ΓSpecIso (CommRingCat.of A)).inv.hom)
    ((moduleTensorLeftFunctor (ProjectiveSpace A ι) (twistingSheaf A ι d)).obj F) 0
  haveI : ((moduleTensorLeftFunctor (ProjectiveSpace A ι) (twistingSheaf A ι d)).obj
      F).IsQuasicoherent := quasicoherent_of_affineCharts _
    (fun R j _ => (twistingTensor_affineLocallyFiniteType A ι d F hF R j).1)
  (moduleSpecΓFunctor.mapIso
      (((Scheme.Modules.pushforward (toSpec A ι)).rightDerivedZeroIsoSelf).app _).symm
      ).toLinearEquiv.trans
    (moduleHigherDirectImageAffineSectionsLinearEquiv (toSpec A ι) _ (injectiveResolution _) 0)

variable [IsNoetherianRing A] (n : ℕ) (e : ι ≃ Fin (n + 1)) (F : (ProjectiveSpace A ι).Modules)
  (hF : affineLocallyFiniteType (ProjectiveSpace A ι) F)

include e hF in
/-- The direct images `π_* F(d)` of a coherent `F` are coherent. -/
theorem affineLocallyFiniteType_directImageTwist (d : ℤ) :
    affineLocallyFiniteType (Spec (CommRingCat.of A)) (directImageTwist F d) :=
  have : Finite ι := Finite.of_equiv _ e.symm
  (affineLocallyFiniteType _).prop_of_iso
    (((Scheme.Modules.pushforward (toSpec A ι)).rightDerivedZeroIsoSelf).app _)
    (projectiveProjection_higherDirectImage_coherent A ι (𝟙 _) (toSpec A ι) (𝟙 _)
      (IsPullback.id_horiz (toSpec A ι)) n e _
      (twistingTensor_affineLocallyFiniteType A ι d F hF) 0)

include e hF in
/-- **The fibre rank of `π_* F(d)` is the fibre Hilbert function** (Nitsure,
arXiv:math/0504590v1, proof of Thm 4.3, p. 22, "each `π_* F(N + i)` has fibres of constant rank
`f(N + i)` on `W_f`"): if at `y` the positive cohomology of the fibre `F_y(d)` vanishes and the
fibre base-change map of `F(d)` is an isomorphism, the fibre of `π_* F(d)` at `y` has dimension
`χ(F_y(d))`. -/
theorem sheafRank_directImageTwist (d : ℤ) (y : PrimeSpectrum A)
    (hvan : ∀ q : ℕ, q ≠ 0 → Subsingleton (Sheaf.H.{u + 1}
      (moduleAddSheaf (pullback (toSpec A ι)
          (Spec.map (CommRingCat.ofHom (algebraMap A y.asIdeal.ResidueField))))
        ((Scheme.Modules.pullback (pullback.fst (toSpec A ι)
          (Spec.map (CommRingCat.ofHom (algebraMap A y.asIdeal.ResidueField))))).obj
          ((moduleTensorLeftFunctor (ProjectiveSpace A ι) (twistingSheaf A ι d)).obj F))) q))
    (hiso : IsIso (moduleCohomologyBaseChangeMap (toSpec A ι) (algebraMap A y.asIdeal.ResidueField)
      ((moduleTensorLeftFunctor (ProjectiveSpace A ι) (twistingSheaf A ι d)).obj F) 0)) :
    (sheafRank (directImageTwist F d) y : ℤ) =
      projectiveHilbertFunction y.asIdeal.ResidueField ι
        ((Scheme.Modules.pullback (map (algebraMap A y.asIdeal.ResidueField) ι)).obj F) d := by
  have : Finite ι := Finite.of_equiv _ e.symm
  let M := (moduleTensorLeftFunctor (ProjectiveSpace A ι) (twistingSheaf A ι d)).obj F
  have hM : affineLocallyFiniteType (ProjectiveSpace A ι) M :=
    twistingTensor_affineLocallyFiniteType A ι d F hF
  have hE := affineLocallyFiniteType_directImageTwist n e F hF d
  have : (directImageTwist F d).IsFinitePresentation :=
    affineLocallyFiniteType_finitePresentation hE
  have : M.IsQuasicoherent := quasicoherent_of_affineCharts M (fun R j _ => (hM R j).1)
  let α := (toSpec A ι).appTop.hom.comp (Scheme.ΓSpecIso (CommRingCat.of A)).inv.hom
  let := moduleCohomologyModuleOfHom (ProjectiveSpace A ι) α M 0
  have : Module.Finite A (Sheaf.H.{u + 1} (moduleAddSheaf (ProjectiveSpace A ι) M) 0) :=
    moduleCohomology_finite_of_projectiveEmbedding A ι (𝟙 _) n e (toSpec A ι)
      (Category.id_comp _) M hM 0
  let eΓ : moduleSpecΓFunctor.obj (directImageTwist F d) ≃ₗ[A]
      Sheaf.H.{u + 1} (moduleAddSheaf (ProjectiveSpace A ι) M) 0 :=
    directImageTwistSectionsLinearEquiv F hF d
  have h₁ : sheafRank (directImageTwist F d) y = Module.finrank y.asIdeal.ResidueField
      ((ModuleCat.extendScalars (algebraMap A y.asIdeal.ResidueField)).obj
        (ModuleCat.of A (Sheaf.H.{u + 1} (moduleAddSheaf (ProjectiveSpace A ι) M) 0))) := by
    have key : ∀ k, sheafRank (directImageTwist F d) y ≤ k ↔ Module.finrank
        y.asIdeal.ResidueField ((ModuleCat.extendScalars (algebraMap A y.asIdeal.ResidueField)).obj
          (ModuleCat.of A (Sheaf.H.{u + 1} (moduleAddSheaf (ProjectiveSpace A ι) M) 0))) ≤ k :=
      fun k => by
        rw [sheafRank_le_iff_fittingIdeal_moduleSpecΓFunctor _ hE y k,
          Module.fittingIdeal_congr eΓ k, Module.finrank_extendScalars_residueField_le_iff]
    exact le_antisymm ((key _).mpr le_rfl) ((key _).mp le_rfl)
  have h₂ : Module.finrank y.asIdeal.ResidueField
      ((ModuleCat.extendScalars (algebraMap A y.asIdeal.ResidueField)).obj
        (ModuleCat.of A (Sheaf.H.{u + 1} (moduleAddSheaf (ProjectiveSpace A ι) M) 0))) =
      moduleFiberCohomologyDimension (toSpec A ι) M 0 y := by
    let β := (pullback.snd (toSpec A ι)
      (Spec.map (CommRingCat.ofHom (algebraMap A y.asIdeal.ResidueField)))).appTop.hom.comp
        (Scheme.ΓSpecIso (CommRingCat.of y.asIdeal.ResidueField)).inv.hom
    let := moduleCohomologyModuleOfHom
      (pullback (toSpec A ι) (Spec.map (CommRingCat.ofHom (algebraMap A y.asIdeal.ResidueField))))
      β ((Scheme.Modules.pullback (pullback.fst (toSpec A ι)
        (Spec.map (CommRingCat.ofHom (algebraMap A y.asIdeal.ResidueField))))).obj M) 0
    exact (asIso (moduleCohomologyBaseChangeMap (toSpec A ι) (algebraMap A y.asIdeal.ResidueField)
      M 0)).toLinearEquiv.finrank_eq
  have h₃ : moduleFiberEulerChar (toSpec A ι) M y =
      (moduleFiberCohomologyDimension (toSpec A ι) M 0 y : ℤ) := by
    rw [moduleFiberEulerChar_eq_sum_range (toSpec A ι) M y 0 fun q hq => ?_]
    · simp
    · have := hvan q (by omega)
      let β := (pullback.snd (toSpec A ι)
        (Spec.map (CommRingCat.ofHom (algebraMap A y.asIdeal.ResidueField)))).appTop.hom.comp
          (Scheme.ΓSpecIso (CommRingCat.of y.asIdeal.ResidueField)).inv.hom
      let := moduleCohomologyModuleOfHom
        (pullback (toSpec A ι) (Spec.map (CommRingCat.ofHom (algebraMap A y.asIdeal.ResidueField))))
        β ((Scheme.Modules.pullback (pullback.fst (toSpec A ι)
          (Spec.map (CommRingCat.ofHom (algebraMap A y.asIdeal.ResidueField))))).obj M) q
      exact Module.finrank_zero_of_subsingleton
  rw [h₁, h₂, ← h₃, moduleFiberEulerChar_twistingTensor_toSpec]

/-! ### The strata `S_f` and Theorem 4.3 (i) -/

/-- The ranks `e_i = f(N + i)` of the stratum `S_f`, as natural numbers (the floor, truncated at
`0`; for the polynomials that occur these are the values themselves). -/
def hilbertPolynomialRank (N : ℕ) (f : Polynomial ℚ) (i : ℕ) : ℕ :=
  ⌊f.eval ((N + i : ℕ) : ℚ)⌋.toNat

/-- **Nitsure's stratum `S_f`** (arXiv:math/0504590v1, proof of Thm 4.3, p. 22): for the direct
images `E_i = π_* F(N + i)`, `i ≥ 0`, the locally closed subscheme cut out by
`⨆_{i ≥ 0} Fitt_{f(N+i) - 1}(E_i)` in the open complement of
`⋃_{j ≤ n} V(Fitt_{f(N+j)}(E_j))`. For `f` that occurs and `N` a bound of the fibre statements of
(B) and (C), this is the closed subscheme `S_f ⊆ W_f` defined by the sum of the ideals `I_i` inside
the joint stratum `W_f` of `E_0, …, E_n`; for other `f` it can be nonempty without being one of
Nitsure's strata. -/
abbrev hilbertPolynomialStratum (N : ℕ) (f : Polynomial ℚ) : Scheme.{u} :=
  refinedJointRankStratum (fun i : ℕ => directImageTwist F ((N + i : ℕ) : ℤ))
    (fun i => affineLocallyFiniteType_directImageTwist n e F hF ((N + i : ℕ) : ℤ))
    (hilbertPolynomialRank N f) (Finset.range (n + 1))

/-- The immersion `S_f ⟶ Spec A`. -/
def hilbertPolynomialStratumι (N : ℕ) (f : Polynomial ℚ) :
    hilbertPolynomialStratum n e F hF N f ⟶ Spec (CommRingCat.of A) :=
  refinedJointRankStratumι _ _ _ _

instance (N : ℕ) (f : Polynomial ℚ) : IsImmersion (hilbertPolynomialStratumι n e F hF N f) := by
  unfold hilbertPolynomialStratumι
  infer_instance

/-- A bound `N` of the fibre statements of (B) and (C): beyond it, the positive cohomology of every
fibre of `F(d)` vanishes and every fibre base-change map of `F(d)` in degree zero is an
isomorphism. The vanishing of `H^r(P^n_A, F(d))` itself, also part of (B), is not included. -/
def IsFiberBaseChangeBound (N : ℕ) : Prop :=
  ∀ d : ℤ, (N : ℤ) ≤ d → ∀ s : PrimeSpectrum A,
    (∀ q : ℕ, q ≠ 0 → Subsingleton (Sheaf.H.{u + 1}
      (moduleAddSheaf (pullback (toSpec A ι)
          (Spec.map (CommRingCat.ofHom (algebraMap A s.asIdeal.ResidueField))))
        ((Scheme.Modules.pullback (pullback.fst (toSpec A ι)
          (Spec.map (CommRingCat.ofHom (algebraMap A s.asIdeal.ResidueField))))).obj
          ((moduleTensorLeftFunctor (ProjectiveSpace A ι) (twistingSheaf A ι d)).obj F))) q)) ∧
    IsIso (moduleCohomologyBaseChangeMap (toSpec A ι) (algebraMap A s.asIdeal.ResidueField)
      ((moduleTensorLeftFunctor (ProjectiveSpace A ι) (twistingSheaf A ι d)).obj F) 0)

include e hF in
/-- Such a bound exists (from statements (B) and (C), `FiberBaseChange`). -/
theorem exists_isFiberBaseChangeBound : ∃ N : ℕ, IsFiberBaseChangeBound F N :=
  exists_twist_fiber_vanishing_and_baseChange_isIso n e F hF

include e hF in
/-- Beyond a bound of the fibre statements of (B) and (C), the fibre rank of `E_i = π_* F(N + i)` at
`y` is `P_y(N + i)` (Nitsure, arXiv:math/0504590v1, proof of Thm 4.3, p. 22). -/
theorem sheafRank_directImageTwist_eq_eval {N : ℕ} (hN : IsFiberBaseChangeBound F N)
    (y : PrimeSpectrum A) (i : ℕ) :
    (sheafRank (directImageTwist F ((N + i : ℕ) : ℤ)) y : ℚ) =
      (projectiveHilbertPolynomial y.asIdeal.ResidueField ι
        ((Scheme.Modules.pullback (map (algebraMap A y.asIdeal.ResidueField) ι)).obj F)).eval
          (((N + i : ℕ) : ℤ) : ℚ) := by
  have : Finite ι := Finite.of_equiv _ e.symm
  obtain ⟨h₁, h₂⟩ := hN ((N + i : ℕ) : ℤ) (by push_cast; omega) y
  rw [← projectiveHilbertFunction_eq_eval _ ι n e _ (affineLocallyFiniteType_pullback _ hF),
    ← sheafRank_directImageTwist n e F hF _ y h₁ h₂]
  rfl

/-- The fibre Hilbert polynomial `P_s` of `F` at `s`. -/
abbrev fiberHilbertPolynomial (s : PrimeSpectrum A) : Polynomial ℚ :=
  projectiveHilbertPolynomial s.asIdeal.ResidueField ι
    ((Scheme.Modules.pullback (map (algebraMap A s.asIdeal.ResidueField) ι)).obj F)

include e hF in
/-- Beyond a bound of the fibre statements of (B) and (C), the ranks of `S_{P_s}` are the fibre
ranks at `s`. -/
theorem hilbertPolynomialRank_fiberHilbertPolynomial {N : ℕ} (hN : IsFiberBaseChangeBound F N)
    (s : PrimeSpectrum A) (i : ℕ) :
    hilbertPolynomialRank N (fiberHilbertPolynomial F s) i =
      sheafRank (directImageTwist F ((N + i : ℕ) : ℤ)) s := by
  have h := sheafRank_directImageTwist_eq_eval n e F hF hN s i
  push_cast at h
  unfold hilbertPolynomialRank
  push_cast
  rw [← h, Int.floor_natCast, Int.toNat_natCast]

include e hF in
/-- Beyond a bound of the fibre statements of (B) and (C), two points have the same fibre ranks of
`π_* F(N + i)` at one `i` exactly when their fibre Hilbert polynomials agree at `N + i`. -/
theorem sheafRank_directImageTwist_eq_iff {N : ℕ} (hN : IsFiberBaseChangeBound F N)
    (y s : PrimeSpectrum A) (i : ℕ) :
    sheafRank (directImageTwist F ((N + i : ℕ) : ℤ)) y =
        sheafRank (directImageTwist F ((N + i : ℕ) : ℤ)) s ↔
      (fiberHilbertPolynomial F y).eval (((N + i : ℕ) : ℤ) : ℚ) =
        (fiberHilbertPolynomial F s).eval (((N + i : ℕ) : ℤ) : ℚ) := by
  rw [← sheafRank_directImageTwist_eq_eval n e F hF hN y i,
    ← sheafRank_directImageTwist_eq_eval n e F hF hN s i, Nat.cast_inj]

include e hF in
/-- Beyond a bound of the fibre statements of (B) and (C), the fibre ranks of `π_* F(N + j)`,
`0 ≤ j ≤ n`, determine the fibre Hilbert polynomial (Nitsure, arXiv:math/0504590v1, proof of
Thm 4.3, p. 22). -/
theorem fiberHilbertPolynomial_eq_of_sheafRank_eq {N : ℕ} (hN : IsFiberBaseChangeBound F N)
    (y s : PrimeSpectrum A)
    (h : ∀ j : ℕ, j ≤ n → sheafRank (directImageTwist F ((N + j : ℕ) : ℤ)) y =
      sheafRank (directImageTwist F ((N + j : ℕ) : ℤ)) s) :
    fiberHilbertPolynomial F y = fiberHilbertPolynomial F s := by
  have : Finite ι := Finite.of_equiv _ e.symm
  refine Polynomial.eq_of_natDegree_le_of_eval_add_eq
    (natDegree_projectiveHilbertPolynomial_le n e _ (affineLocallyFiniteType_pullback _ hF))
    (natDegree_projectiveHilbertPolynomial_le n e _ (affineLocallyFiniteType_pullback _ hF))
    (N : ℤ) fun j hj => ?_
  have h' := (sheafRank_directImageTwist_eq_iff n e F hF hN y s j).mp (h j hj)
  push_cast at h' ⊢
  exact h'

include e hF in
/-- **Nitsure's Theorem 4.3 (i)** (arXiv:math/0504590v1, p. 19, and proof, p. 22), over the affine
Noetherian base `S = Spec A`: for a bound `N` of the fibre statements of (B) and (C) and a
polynomial `f` that occurs as a fibre Hilbert polynomial, the underlying set of `S_f` consists of
the points `s` with `P_s = f`. -/
theorem range_hilbertPolynomialStratumι {N : ℕ} (hN : IsFiberBaseChangeBound F N)
    (f : Polynomial ℚ) (hf : f ∈ Set.range (fiberHilbertPolynomial F)) :
    Set.range (hilbertPolynomialStratumι n e F hF N f) =
      {s : PrimeSpectrum A | fiberHilbertPolynomial F s = f} := by
  have hE := fun i : ℕ => affineLocallyFiniteType_directImageTwist n e F hF ((N + i : ℕ) : ℤ)
  have : ∀ i : ℕ, (directImageTwist F ((N + i : ℕ) : ℤ)).IsFinitePresentation :=
    fun i => affineLocallyFiniteType_finitePresentation (hE i)
  obtain ⟨s₀, rfl⟩ := hf
  ext y
  rw [hilbertPolynomialStratumι, mem_range_refinedJointRankStratumι_iff]
  change _ ↔ fiberHilbertPolynomial F y = fiberHilbertPolynomial F s₀
  simp only [hilbertPolynomialRank_fiberHilbertPolynomial n e F hF hN, Finset.mem_range]
  constructor
  · rintro ⟨h₁, h₂⟩
    exact fiberHilbertPolynomial_eq_of_sheafRank_eq n e F hF hN y s₀ fun j hj =>
      le_antisymm (h₂ j (Nat.lt_succ_of_le hj)) (h₁ j)
  · intro h
    have h' : ∀ i, sheafRank (directImageTwist F ((N + i : ℕ) : ℤ)) y =
        sheafRank (directImageTwist F ((N + i : ℕ) : ℤ)) s₀ :=
      fun i => (sheafRank_directImageTwist_eq_iff n e F hF hN y s₀ i).mpr (by rw [h])
    exact ⟨fun i => (h' i).ge, fun j _ => (h' j).le⟩

include e hF in
/-- **Theorem 4.3 (i), "in particular"** (Nitsure, arXiv:math/0504590v1, p. 19): beyond a bound
of the fibre statements of (B) and (C), the sets `|S_f|`, `f` occurring, are pairwise disjoint and
cover `Spec A`. -/
theorem iUnion_range_hilbertPolynomialStratumι_eq_univ_and_pairwiseDisjoint {N : ℕ}
    (hN : IsFiberBaseChangeBound F N) :
    (⋃ f ∈ Set.range (fiberHilbertPolynomial F),
        Set.range (hilbertPolynomialStratumι n e F hF N f)) = Set.univ ∧
      (Set.range (fiberHilbertPolynomial F)).PairwiseDisjoint
        fun f => Set.range (hilbertPolynomialStratumι n e F hF N f) := by
  refine ⟨Set.eq_univ_of_forall fun s => Set.mem_iUnion₂.mpr ⟨fiberHilbertPolynomial F s,
    ⟨s, rfl⟩, ?_⟩, fun f hf g hg hfg => ?_⟩
  · rw [range_hilbertPolynomialStratumι n e F hF hN _ ⟨s, rfl⟩]
    rfl
  · rw [Function.onFun, range_hilbertPolynomialStratumι n e F hF hN f hf,
      range_hilbertPolynomialStratumι n e F hF hN g hg]
    exact Set.disjoint_left.mpr fun s hsf hsg =>
      hfg ((show fiberHilbertPolynomial F s = f from hsf).symm.trans hsg)

include e hF in
/-- **Theorem 4.3 (i), with the bound of the fibre statements of (B) and (C)**: there is `N` such
that for every polynomial `f` that occurs, `|S_f| = {s : P_s = f}`. -/
theorem exists_range_hilbertPolynomialStratumι :
    ∃ N : ℕ, ∀ f ∈ Set.range (fiberHilbertPolynomial F),
      Set.range (hilbertPolynomialStratumι n e F hF N f) =
        {s : PrimeSpectrum A | fiberHilbertPolynomial F s = f} := by
  obtain ⟨N, hN⟩ := exists_isFiberBaseChangeBound n e F hF
  exact ⟨N, fun f hf => range_hilbertPolynomialStratumι n e F hF hN f hf⟩

include e hF in
/-- **The universal property of `S_f`** (Nitsure, arXiv:math/0504590v1, proof of Thm 4.3, p. 22):
for a bound `N` of the fibre statements of (B) and (C) and a polynomial `f` that occurs, a morphism
`g : T ⟶ Spec A` factors through `S_f` if and only if every `g^* π_* F(N + i)`, `i ≥ 0`, is finite
locally free of constant rank `f(N + i)`. This discharges the hypothesis of
`exists_lift_refinedJointRankStratumι_iff` for Nitsure's sheaves. -/
theorem exists_lift_hilbertPolynomialStratumι_iff {N : ℕ} (hN : IsFiberBaseChangeBound F N)
    (f : Polynomial ℚ) (hf : f ∈ Set.range (fiberHilbertPolynomial F))
    {T : Scheme.{u}} (g : T ⟶ Spec (CommRingCat.of A)) :
    (∃ g' : T ⟶ hilbertPolynomialStratum n e F hF N f,
        g' ≫ hilbertPolynomialStratumι n e F hF N f = g) ↔
      ∀ i : ℕ, SheafHasRank ((Scheme.Modules.pullback g).obj
        (directImageTwist F ((N + i : ℕ) : ℤ))) (hilbertPolynomialRank N f i) := by
  have hE := fun i : ℕ => affineLocallyFiniteType_directImageTwist n e F hF ((N + i : ℕ) : ℤ)
  have : ∀ i : ℕ, (directImageTwist F ((N + i : ℕ) : ℤ)).IsFinitePresentation :=
    fun i => affineLocallyFiniteType_finitePresentation (hE i)
  obtain ⟨s₀, rfl⟩ := hf
  refine exists_lift_refinedJointRankStratumι_iff _ hE _ _ (fun y hy i => ?_) g
  simp only [hilbertPolynomialRank_fiberHilbertPolynomial n e F hF hN, Finset.mem_range] at hy ⊢
  have hP := fiberHilbertPolynomial_eq_of_sheafRank_eq n e F hF hN y s₀ fun j hj =>
    hy j (Nat.lt_succ_of_le hj)
  exact ((sheafRank_directImageTwist_eq_iff n e F hF hN y s₀ i).mpr (by rw [hP])).le

include e hF in
/-- **Nitsure's Theorem 4.3 (iii)** (arXiv:math/0504590v1, p. 19, and proof, p. 23), over the
affine Noetherian base `S = Spec A`: for a bound `N` of the fibre statements of (B) and (C) and a
polynomial `f` that occurs, the closure of `|S_f|` lies in the union of the `|S_g|` over the
polynomials `g` that occur with `f ≤ g`, that is, `f(m) ≤ g(m)` for all `m ≫ 0`. As in Nitsure's
proof, one `p ≥ N` orders the finitely many polynomials that occur
(`exists_eval_le_imp_eventually_le`, with (A), `finite_range_projectiveHilbertPolynomial_fiber`),
and the case `n = 0` (`closure_range_rankStratumι_subset`) applies to `π_* F(p)`. -/
theorem closure_range_hilbertPolynomialStratumι_subset {N : ℕ} (hN : IsFiberBaseChangeBound F N)
    (f : Polynomial ℚ) (hf : f ∈ Set.range (fiberHilbertPolynomial F)) :
    closure (Set.range (hilbertPolynomialStratumι n e F hF N f)) ⊆
      ⋃ g ∈ {g ∈ Set.range (fiberHilbertPolynomial F) |
          ∀ᶠ m : ℕ in Filter.atTop, f.eval (m : ℚ) ≤ g.eval (m : ℚ)},
        Set.range (hilbertPolynomialStratumι n e F hF N g) := by
  obtain ⟨p, hNp, hp⟩ := Polynomial.exists_eval_le_imp_eventually_le
    (finite_range_projectiveHilbertPolynomial_fiber n e F hF) N
  obtain ⟨i, rfl⟩ : ∃ i, p = N + i := ⟨p - N, (Nat.add_sub_cancel' hNp).symm⟩
  let E := directImageTwist F ((N + i : ℕ) : ℤ)
  have hE := affineLocallyFiniteType_directImageTwist n e F hF ((N + i : ℕ) : ℤ)
  have : E.IsFinitePresentation := affineLocallyFiniteType_finitePresentation hE
  obtain ⟨s₀, rfl⟩ := hf
  have hsub : Set.range (hilbertPolynomialStratumι n e F hF N (fiberHilbertPolynomial F s₀)) ⊆
      Set.range (rankStratumι E hE (sheafRank E s₀)) := by
    rw [range_hilbertPolynomialStratumι n e F hF hN _ ⟨s₀, rfl⟩]
    intro y hy
    rw [mem_range_rankStratumι_iff]
    exact (sheafRank_directImageTwist_eq_iff n e F hF hN y s₀ i).mpr (by rw [hy])
  refine (closure_mono hsub).trans ((closure_range_rankStratumι_subset E hE _).trans ?_)
  intro y hy
  obtain ⟨r', hr', hy⟩ := Set.mem_iUnion₂.mp hy
  have hrank : sheafRank E s₀ ≤ sheafRank E y := by
    rw [(mem_range_rankStratumι_iff E hE y r').mp hy]
    exact hr'
  have hle : (fiberHilbertPolynomial F s₀).eval ((N + i : ℕ) : ℚ) ≤
      (fiberHilbertPolynomial F y).eval ((N + i : ℕ) : ℚ) := by
    have h₀ := sheafRank_directImageTwist_eq_eval n e F hF hN s₀ i
    have h₁ := sheafRank_directImageTwist_eq_eval n e F hF hN y i
    push_cast at h₀ h₁ ⊢
    rw [← h₀, ← h₁]
    exact_mod_cast hrank
  refine Set.mem_iUnion₂.mpr ⟨fiberHilbertPolynomial F y,
    ⟨⟨y, rfl⟩, hp _ ⟨s₀, rfl⟩ _ ⟨y, rfl⟩ (by exact_mod_cast hle)⟩, ?_⟩
  rw [range_hilbertPolynomialStratumι n e F hF hN _ ⟨y, rfl⟩]
  rfl

end AlgebraicGeometry.Scheme.Cohomology
