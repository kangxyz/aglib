/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Cohomology.Projective.Regularity.Basic
public import Aglib.AlgebraicGeometry.Cohomology.Projective.Regularity.CoordinateGeneration
public import Aglib.AlgebraicGeometry.Modules.QuasiCoherent.Tensor

/-!
# Regularity passes to all larger twists

If a quasicoherent module `F` on projective `n`-space is `m`-regular, it is `m'`-regular for
every `m' ≥ m` (Nitsure, arXiv:math/0504590v1, Lemma 2.1 (b), p. 10; Stacks, Tag 08A6). The
base is an arbitrary commutative ring. Hence `H^i(O(r) ⊗ F) = 0` for all `r ≥ m` and `i ≥ 1`
(`IsProjectiveRegular.cohomology_subsingleton_of_le`), the vanishing half of Lemma 2.1 (c).

The proof uses neither hyperplane sections nor the full Koszul complex. The coordinates give
the short exact syzygy sequence `0 → Ω G → ∐ᵢ O(0) ⊗ G → O(1 + 0) ⊗ G → 0` for every module
`G` (`epi_coordinateMultiplicationSum`). Say that `G` is `m`-regular from degree `k` when
`H^q(O(m - q) ⊗ G) = 0` for all `q ≥ k`. The long exact sequence of the twisted syzygy
sequence shows that `Ω G` is `m`-regular from degree `k + 1` when `G` is `m`-regular from
degree `k`. A second application, with a downward induction on `k` starting above the
dimension (where the cohomology of quasicoherent modules vanishes), shows that regularity
from degree `k` passes from `m` to `m + 1`.
-/

@[expose] public section

noncomputable section

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry.ProjectiveSpace
open AlgebraicGeometry.Scheme.Modules
open AlgebraicGeometry.Scheme.Modules.QuasiCoherent

universe u

namespace AlgebraicGeometry.Scheme.Cohomology

variable (R : Type u) [CommRing R] (ι : Type u)

/-- `G` is `m`-regular from degree `k`: `H^q(O(m - q) ⊗ G)` vanishes for every `q ≥ k`.
Regularity in the sense of `IsProjectiveRegular` is regularity from degree one. -/
def IsProjectiveRegularFrom (G : (ProjectiveSpace R ι).Modules) (m : ℤ) (k : ℕ) : Prop :=
  ∀ q : ℕ, k ≤ q → Subsingleton (Sheaf.H.{u + 1} (moduleAddSheaf (ProjectiveSpace R ι)
    ((moduleTensorLeftFunctor (ProjectiveSpace R ι) (twistingSheaf R ι (m - q))).obj G)) q)

/-- Regularity is regularity from degree one. -/
theorem isProjectiveRegular_iff_from (G : (ProjectiveSpace R ι).Modules) (m : ℤ) :
    IsProjectiveRegular R ι G m ↔ IsProjectiveRegularFrom R ι G m 1 :=
  ⟨fun h q hq => h q hq, fun h q hq => h q hq⟩

/-- Every twist `O(c) ⊗ F` of a quasicoherent module is quasicoherent. -/
theorem twistingTensor_isQuasicoherent (F : (ProjectiveSpace R ι).Modules) [F.IsQuasicoherent]
    (c : ℤ) :
    ((moduleTensorLeftFunctor (ProjectiveSpace R ι) (twistingSheaf R ι c)).obj F).IsQuasicoherent :=
  isQuasicoherent_moduleTensorLeftFunctor _ _

/-- Twisted cohomology vanishing depends only on the value of the twist degree. -/
theorem twistCohomology_subsingleton_congr {G : (ProjectiveSpace R ι).Modules} {c c' : ℤ}
    (h : c = c') {q : ℕ}
    (hc : Subsingleton (Sheaf.H.{u + 1} (moduleAddSheaf (ProjectiveSpace R ι)
      ((moduleTensorLeftFunctor (ProjectiveSpace R ι) (twistingSheaf R ι c)).obj G)) q)) :
    Subsingleton (Sheaf.H.{u + 1} (moduleAddSheaf (ProjectiveSpace R ι)
      ((moduleTensorLeftFunctor (ProjectiveSpace R ι) (twistingSheaf R ι c')).obj G)) q) := by
  subst h
  exact hc

/-- `H^q(O(a) ⊗ (O(b) ⊗ G))` vanishes when `H^q(O(c) ⊗ G)` does, for `a + b = c`. -/
theorem twistCohomology_subsingleton_comp {G : (ProjectiveSpace R ι).Modules} {a b c : ℤ}
    (hc : a + b = c) {q : ℕ}
    (h : Subsingleton (Sheaf.H.{u + 1} (moduleAddSheaf (ProjectiveSpace R ι)
      ((moduleTensorLeftFunctor (ProjectiveSpace R ι) (twistingSheaf R ι c)).obj G)) q)) :
    Subsingleton (Sheaf.H.{u + 1} (moduleAddSheaf (ProjectiveSpace R ι)
      ((moduleTensorLeftFunctor (ProjectiveSpace R ι) (twistingSheaf R ι a)).obj
        ((moduleTensorLeftFunctor (ProjectiveSpace R ι) (twistingSheaf R ι b)).obj G))) q) := by
  subst hc
  have h' := moduleCohomology_subsingleton_of_iso ((twistingTensorCompIso R ι a b).app G).symm q h
  simpa only [Functor.comp_obj] using h'

/-- `H^q(O(c) ⊗ G)` vanishes when `H^q(O(a) ⊗ (O(b) ⊗ G))` does, for `a + b = c`. -/
theorem twistCohomology_subsingleton_of_comp {G : (ProjectiveSpace R ι).Modules} {a b c : ℤ}
    (hc : a + b = c) {q : ℕ}
    (h : Subsingleton (Sheaf.H.{u + 1} (moduleAddSheaf (ProjectiveSpace R ι)
      ((moduleTensorLeftFunctor (ProjectiveSpace R ι) (twistingSheaf R ι a)).obj
        ((moduleTensorLeftFunctor (ProjectiveSpace R ι) (twistingSheaf R ι b)).obj G))) q)) :
    Subsingleton (Sheaf.H.{u + 1} (moduleAddSheaf (ProjectiveSpace R ι)
      ((moduleTensorLeftFunctor (ProjectiveSpace R ι) (twistingSheaf R ι c)).obj G)) q) := by
  subst hc
  have h' : Subsingleton (Sheaf.H.{u + 1} (moduleAddSheaf (ProjectiveSpace R ι)
      ((moduleTensorLeftFunctor (ProjectiveSpace R ι) (twistingSheaf R ι b) ⋙
        moduleTensorLeftFunctor (ProjectiveSpace R ι) (twistingSheaf R ι a)).obj G)) q) := by
    simpa only [Functor.comp_obj] using h
  exact moduleCohomology_subsingleton_of_iso ((twistingTensorCompIso R ι a b).app G) q h'

variable [Finite ι]

/-- The coordinate syzygy module: the kernel of `∐ᵢ O(0) ⊗ G → O(1 + 0) ⊗ G`. -/
abbrev coordinateSyzygy (G : (ProjectiveSpace R ι).Modules) : (ProjectiveSpace R ι).Modules :=
  kernel (coordinateMultiplicationSum R ι G)

/-- The twisted middle term `O(c) ⊗ ∐ᵢ (O(0) ⊗ G)` has vanishing `H^q` when `O(c) ⊗ G` does. -/
theorem coordinateSyzygy_middle_subsingleton (G : (ProjectiveSpace R ι).Modules) (c : ℤ)
    (q : ℕ) (h : Subsingleton (Sheaf.H.{u + 1} (moduleAddSheaf (ProjectiveSpace R ι)
      ((moduleTensorLeftFunctor (ProjectiveSpace R ι) (twistingSheaf R ι c)).obj G)) q)) :
    Subsingleton (Sheaf.H.{u + 1} (moduleAddSheaf (ProjectiveSpace R ι)
      ((moduleTensorLeftFunctor (ProjectiveSpace R ι) (twistingSheaf R ι c)).obj
        (∐ fun _ : ι => (moduleTensorLeftFunctor (ProjectiveSpace R ι)
          (twistingSheaf R ι 0)).obj G))) q) := by
  apply moduleCohomology_subsingleton_coproduct
  intro _
  exact twistCohomology_subsingleton_comp R ι (add_zero c) h

/-- Twists of the coordinate syzygy module stay quasicoherent. -/
theorem coordinateSyzygy_twist_isQuasicoherent (G : (ProjectiveSpace R ι).Modules)
    (hG : ∀ c : ℤ, ((moduleTensorLeftFunctor (ProjectiveSpace R ι)
      (twistingSheaf R ι c)).obj G).IsQuasicoherent) (c : ℤ) :
    ((moduleTensorLeftFunctor (ProjectiveSpace R ι) (twistingSheaf R ι c)).obj
      (coordinateSyzygy R ι G)).IsQuasicoherent := by
  let T := moduleTensorLeftFunctor (ProjectiveSpace R ι) (twistingSheaf R ι c)
  let Q := SheafOfModules.isQuasicoherent (ProjectiveSpace R ι).ringCatSheaf
  have hcomp (b : ℤ) : (T.obj ((moduleTensorLeftFunctor (ProjectiveSpace R ι)
      (twistingSheaf R ι b)).obj G)).IsQuasicoherent := by
    have h := Q.prop_of_iso ((twistingTensorCompIso R ι c b).app G).symm (hG (c + b))
    simpa only [Functor.comp_obj] using h
  have hsum : (T.obj (∐ fun _ : ι => (moduleTensorLeftFunctor (ProjectiveSpace R ι)
      (twistingSheaf R ι 0)).obj G)).IsQuasicoherent :=
    Q.prop_of_iso (PreservesCoproduct.iso T _).symm (Q.prop_coproduct (fun _ => hcomp 0))
  have hquot := hcomp (((1 : ℕ) : ℤ) + 0)
  have hker := quasicoherent_kernel (T.map (coordinateMultiplicationSum R ι G))
  exact Q.prop_of_iso (PreservesKernel.iso T (coordinateMultiplicationSum R ι G)).symm hker

/-- Regularity from degree `k` passes to the coordinate syzygy module from degree `k + 1`. -/
theorem IsProjectiveRegularFrom.syzygy {G : (ProjectiveSpace R ι).Modules} {m : ℤ}
    {k : ℕ} (hG : IsProjectiveRegularFrom R ι G m k) :
    IsProjectiveRegularFrom R ι (coordinateSyzygy R ι G) m (k + 1) := by
  intro q hq
  obtain ⟨q, rfl⟩ : ∃ q', q = q' + 1 := ⟨q - 1, by omega⟩
  apply moduleCohomology_subsingleton_tensor_kernel (twistingSheaf R ι (m - ((q + 1 : ℕ) : ℤ)))
    (coordinateMultiplicationSum R ι G) q
  · exact twistCohomology_subsingleton_comp R ι (by push_cast; ring) (hG q (by omega))
  · exact coordinateSyzygy_middle_subsingleton R ι G _ (q + 1) (hG (q + 1) (by omega))

/-- Regularity from degree `k` passes from `m` to `m + 1`, for modules whose twists are
quasicoherent; the proof is a downward induction on `k` from above the dimension `n`. -/
theorem IsProjectiveRegularFrom.succ (n : ℕ) (e : ι ≃ Fin (n + 1)) :
    ∀ (d k : ℕ), n + 1 ≤ k + d → ∀ (G : (ProjectiveSpace R ι).Modules),
      (∀ c : ℤ, ((moduleTensorLeftFunctor (ProjectiveSpace R ι)
        (twistingSheaf R ι c)).obj G).IsQuasicoherent) →
      ∀ m : ℤ, IsProjectiveRegularFrom R ι G m k → IsProjectiveRegularFrom R ι G (m + 1) k := by
  intro d
  induction d with
  | zero =>
    intro k hk G hG m _ q hq
    let := hG (m + 1 - q)
    exact projectiveCohomology_subsingleton_of_gt R ι n e _ q (by omega)
  | succ d ih =>
    intro k hk G hG m hreg q hq
    have hΩ := ih (k + 1) (by omega) (coordinateSyzygy R ι G)
      (coordinateSyzygy_twist_isQuasicoherent R ι G hG) m hreg.syzygy
    have h₃ := moduleCohomology_subsingleton_tensor_target (twistingSheaf R ι (m - q))
      (coordinateMultiplicationSum R ι G) q
      (coordinateSyzygy_middle_subsingleton R ι G _ q (hreg q hq))
      (twistCohomology_subsingleton_congr R ι (by push_cast; ring) (hΩ (q + 1) (by omega)))
    exact twistCohomology_subsingleton_of_comp R ι (by push_cast; ring) h₃

omit [Finite ι] in
/-- Castelnuovo–Mumford regularity passes to all larger twists (Nitsure,
arXiv:math/0504590v1, Lemma 2.1 (b), p. 10; Stacks, Tag 08A6): if a quasicoherent module `F` is
`m`-regular, then `F` is `m'`-regular for every `m' ≥ m`. The base is an arbitrary commutative
ring. -/
theorem IsProjectiveRegular.of_le (n : ℕ) (e : ι ≃ Fin (n + 1))
    {F : (ProjectiveSpace R ι).Modules} [F.IsQuasicoherent]
    {m m' : ℤ} (hm : m ≤ m') (h : IsProjectiveRegular R ι F m) :
    IsProjectiveRegular R ι F m' := by
  have : Finite ι := Finite.of_equiv _ e.symm
  induction m', hm using Int.leInduction with
  | base => exact h
  | succ m' _ ih =>
    rw [isProjectiveRegular_iff_from] at ih ⊢
    exact IsProjectiveRegularFrom.succ R ι n e n 1 (by omega) F
      (twistingTensor_isQuasicoherent R ι F) m' ih

omit [Finite ι] in
/-- Castelnuovo–Mumford regularity of an affine-locally finite-type module passes to all larger
twists (Nitsure, arXiv:math/0504590v1, Lemma 2.1 (b), p. 10; Stacks, Tag 08A6). The base is an
arbitrary commutative ring. -/
theorem IsProjectiveRegular.of_le_of_coherent (n : ℕ)
    (e : ι ≃ Fin (n + 1)) {F : (ProjectiveSpace R ι).Modules}
    (hF : affineLocallyFiniteType (ProjectiveSpace R ι) F) {m m' : ℤ} (hm : m ≤ m')
    (h : IsProjectiveRegular R ι F m) : IsProjectiveRegular R ι F m' := by
  have : F.IsQuasicoherent := quasicoherent_of_affineCharts _ (fun A j _ => (hF A j).1)
  exact IsProjectiveRegular.of_le R ι n e hm h

omit [Finite ι] in
/-- **Nitsure, Lemma 2.1 (c)**, vanishing half (arXiv:math/0504590v1, p. 10): if a quasicoherent
module `F` is `m`-regular, then `H^i(O(r) ⊗ F) = 0` for every `r ≥ m` and every `i ≥ 1`. With
the global generation of `O(r) ⊗ F` (`IsProjectiveRegular.epi_globalSectionsEval`) this is
Lemma 2.1 (c). The base is an arbitrary commutative ring. -/
theorem IsProjectiveRegular.cohomology_subsingleton_of_le (n : ℕ) (e : ι ≃ Fin (n + 1))
    {F : (ProjectiveSpace R ι).Modules} [F.IsQuasicoherent] {m r : ℤ}
    (h : IsProjectiveRegular R ι F m) (hr : m ≤ r) {i : ℕ} (hi : 0 < i) :
    Subsingleton (Sheaf.H.{u + 1} (moduleAddSheaf (ProjectiveSpace R ι)
      ((moduleTensorLeftFunctor (ProjectiveSpace R ι) (twistingSheaf R ι r)).obj F)) i) := by
  have h' := IsProjectiveRegular.of_le R ι n e (m' := r + i) (by omega) h i hi
  exact twistCohomology_subsingleton_congr R ι (add_sub_cancel_right r (i : ℤ)) h'

omit [Finite ι] in
/-- **Nitsure, Lemma 2.1 (c)**, vanishing half, for an affine-locally finite-type module
(arXiv:math/0504590v1, p. 10): `H^i(O(r) ⊗ F) = 0` for every `r ≥ m` and every `i ≥ 1`. -/
theorem IsProjectiveRegular.cohomology_subsingleton_of_le_of_coherent (n : ℕ)
    (e : ι ≃ Fin (n + 1)) {F : (ProjectiveSpace R ι).Modules}
    (hF : affineLocallyFiniteType (ProjectiveSpace R ι) F) {m r : ℤ}
    (h : IsProjectiveRegular R ι F m) (hr : m ≤ r) {i : ℕ} (hi : 0 < i) :
    Subsingleton (Sheaf.H.{u + 1} (moduleAddSheaf (ProjectiveSpace R ι)
      ((moduleTensorLeftFunctor (ProjectiveSpace R ι) (twistingSheaf R ι r)).obj F)) i) := by
  have : F.IsQuasicoherent := quasicoherent_of_affineCharts _ (fun A j _ => (hF A j).1)
  exact IsProjectiveRegular.cohomology_subsingleton_of_le R ι n e h hr hi

section Implicit

variable {R ι}

omit [Finite ι] in
/-- An `m`-regular affine-locally finite-type module has `H^q(O(s) ⊗ F) = 0` for every `q ≥ 1`
and `s ≥ m - q`. -/
theorem IsProjectiveRegular.subsingleton_of_le_add (n : ℕ) (e : ι ≃ Fin (n + 1))
    {F : (ProjectiveSpace R ι).Modules} (hF : affineLocallyFiniteType (ProjectiveSpace R ι) F)
    {m s : ℤ} {q : ℕ} (h : IsProjectiveRegular R ι F m) (hq : 0 < q) (hs : m ≤ s + q) :
    Subsingleton (Sheaf.H.{u + 1} (moduleAddSheaf (ProjectiveSpace R ι)
      ((moduleTensorLeftFunctor (ProjectiveSpace R ι) (twistingSheaf R ι s)).obj F)) q) := by
  have h' := IsProjectiveRegular.of_le_of_coherent R ι n e hF hs h q hq
  exact twistCohomology_subsingleton_congr R ι (add_sub_cancel_right s (q : ℤ)) h'

end Implicit

end AlgebraicGeometry.Scheme.Cohomology
