/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Cohomology.Projective.SerreVanishing

/-!
# Castelnuovo–Mumford regularity on polynomial projective space

A module `F` on actual polynomial projective space is `m`-regular when the original
cohomology `H^q(O(m - q) ⊗ F)` vanishes in every positive degree `q`
(Nitsure, arXiv:math/0504590v1, §2, p. 9, before Lemma 2.1; Stacks, Tag 08A3). The twist is the
native tensor `O(m - q) ⊗ F` and the cohomology is the unchanged `Sheaf.H`.

Every coherent module over a Noetherian base is `m`-regular for some `m`: Serre vanishing
handles the degrees `1 ≤ q ≤ n`, and the coordinate-cover bound handles `q > n`. The
consequences of Nitsure, Lemma 2.1 (`(m + 1)`-regularity, global generation of `O(m) ⊗ F`
and surjectivity of the multiplication maps) are not proved here.
-/

@[expose] public section

noncomputable section

open CategoryTheory
open AlgebraicGeometry.ProjectiveSpace
open AlgebraicGeometry.Scheme.Modules
open AlgebraicGeometry.Scheme.Modules.QuasiCoherent

universe u

namespace AlgebraicGeometry.Scheme.Cohomology

variable (R : Type u) [CommRing R] (ι : Type u)

/-- Castelnuovo–Mumford `m`-regularity: the original cohomology of the tensor twist
`O(m - q) ⊗ F` vanishes in every positive degree `q`. -/
def IsProjectiveRegular (F : (ProjectiveSpace R ι).Modules) (m : ℤ) : Prop :=
  ∀ q : ℕ, 0 < q → Subsingleton (Sheaf.H.{u + 1} (moduleAddSheaf (ProjectiveSpace R ι)
    ((moduleTensorLeftFunctor (ProjectiveSpace R ι) (twistingSheaf R ι (m - q))).obj F)) q)

/-- Every coherent module on projective `n`-space over a Noetherian ring is `m`-regular for
some integer `m`. -/
theorem exists_isProjectiveRegular [IsNoetherianRing R] (n : ℕ) (e : ι ≃ Fin (n + 1))
    (F : (ProjectiveSpace R ι).Modules)
    (hF : affineLocallyFiniteType (ProjectiveSpace R ι) F) :
    ∃ m : ℤ, IsProjectiveRegular R ι F m := by
  let := Fintype.ofEquiv (Fin (n + 1)) e.symm
  obtain ⟨B, hB⟩ := projectiveSerreVanishing R ι n e F hF
  refine ⟨B + n, fun q hq => ?_⟩
  by_cases hqn : q ≤ n
  · exact hB _ (by omega) q (by omega)
  · let T := (moduleTensorLeftFunctor (ProjectiveSpace R ι)
      (twistingSheaf R ι ((B : ℤ) + n - q))).obj F
    have hT := twistingTensor_affineLocallyFiniteType R ι ((B : ℤ) + n - q) F hF
    let : T.IsQuasicoherent := quasicoherent_of_affineCharts T (fun A j _ => (hT A j).1)
    exact projectiveCohomology_subsingleton_of_gt R ι n e T q (by omega)

end AlgebraicGeometry.Scheme.Cohomology
