/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Cohomology.BaseChange.Modules.Separated.Cartesian
public import Aglib.AlgebraicGeometry.Cohomology.Projective.HilbertPolynomial.Basic
public import Aglib.AlgebraicGeometry.Cohomology.Projective.HilbertPolynomial.EulerCharacteristic
public import Aglib.AlgebraicGeometry.ProjectiveSpace.BaseChange.Cartesian
public import Aglib.AlgebraicGeometry.ProjectiveSpace.BaseChange.Twisting
public import Aglib.AlgebraicGeometry.Modules.QuasiCoherent.Tensor
public import Aglib.Algebra.Category.ModuleCat.ChangeOfRings.Algebra
public import Mathlib.RingTheory.RingHom.Flat

/-!
# Cohomology dimensions under field extension

For a field extension `k → K`, finitely many coordinates and a quasicoherent module `M` on
`P^n_k`, the original cohomology of the pullback of `M` along
`π = ProjectiveSpace.map (algebraMap k K) ι : P^n_K → P^n_k` has the same dimensions
(`projectiveCohomologyDim_pullback_map`). This is the dimension form of flat base change
(`moduleCohomologyTensorMap_isIso_of_isPullback`, with the cartesian square
`ProjectiveSpace.isPullback_map`): `K ⊗_k Hᵠ(P^n_k, M) ≅ Hᵠ(P^n_K, π^* M)`. Nitsure,
arXiv:math/0504590v1, uses this to reduce Lemma 2.1 (p. 10) and Thm 2.3 (p. 12) to an infinite
field. With the twisting pullback `twistingTensorPullbackIso` it gives the invariance of Hilbert
functions under a field map `ψ : k →+* K` (`projectiveHilbertFunction_pullback_map`).
-/

@[expose] public section

noncomputable section

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry.ProjectiveSpace
open AlgebraicGeometry.Scheme.Modules

universe u

namespace AlgebraicGeometry.Scheme.Cohomology

/-- **Cohomology dimensions are invariant under field extension**: for a quasicoherent `M` on
`P^n_k` and the projection `π : P^n_K → P^n_k`, `hᵠ(π^* M) = hᵠ(M)` for every `q`. -/
theorem projectiveCohomologyDim_pullback_map (k K : Type u) [Field k] [Field K] [Algebra k K]
    (ι : Type u) [Finite ι] (M : (ProjectiveSpace k ι).Modules) [M.IsQuasicoherent] (q : ℕ) :
    projectiveCohomologyDim K ι
        ((Scheme.Modules.pullback (ProjectiveSpace.map (algebraMap k K) ι)).obj M) q =
      projectiveCohomologyDim k ι M q := by
  have hsq := ProjectiveSpace.isPullback_map (algebraMap k K) ι
  have hflat : (algebraMap k K).Flat := RingHom.flat_algebraMap_iff.mpr inferInstance
  have hiso := moduleCohomologyTensorMap_isIso_of_isPullback
    (ProjectiveSpace.map (algebraMap k K) ι) (toSpec K ι) (toSpec k ι) (algebraMap k K) hsq hflat
    M q
  let := moduleCohomologyModuleOfHom (ProjectiveSpace k ι) (projectiveConstants k ι) M q
  let := moduleCohomologyModuleOfHom (ProjectiveSpace K ι) (projectiveConstants K ι)
    ((Scheme.Modules.pullback (ProjectiveSpace.map (algebraMap k K) ι)).obj M) q
  let φ := moduleCohomologyTensorMap (ProjectiveSpace.map (algebraMap k K) ι) (algebraMap k K)
    ((toSpec k ι).appTop.hom.comp (Scheme.ΓSpecIso (CommRingCat.of k)).inv.hom)
    ((toSpec K ι).appTop.hom.comp (Scheme.ΓSpecIso (CommRingCat.of K)).inv.hom)
    (moduleSectionsBaseChangeScalars (ProjectiveSpace.map (algebraMap k K) ι) (toSpec K ι)
      (toSpec k ι) (algebraMap k K) hsq.w)
    ((Scheme.Modules.pullbackPushforwardAdjunction
      (ProjectiveSpace.map (algebraMap k K) ι)).unit.app M) q
  have : IsIso φ := hiso
  have hE := (asIso φ).toLinearEquiv.finrank_eq
  have hA := (ModuleCat.extendScalarsAlgebraObjIso k K
    (ModuleCat.of k (Sheaf.H.{u + 1} (moduleAddSheaf (ProjectiveSpace k ι) M)
      q))).toLinearEquiv.finrank_eq
  unfold projectiveCohomologyDim
  rw [← hE]
  exact hA.trans Module.finrank_baseChange

/-- **Hilbert functions are invariant under field extension**: for a field map `ψ : k →+* K`,
finitely many coordinates and a quasicoherent `G` on `P_k`, `χ(O(m) ⊗ π^* G) = χ(O(m) ⊗ G)` for
`π = ProjectiveSpace.map ψ ι`. -/
theorem projectiveHilbertFunction_pullback_map (ι : Type u) {k K : Type u} [Field k] [Field K]
    (ψ : k →+* K) [Finite ι] (G : (ProjectiveSpace k ι).Modules) [G.IsQuasicoherent] :
    projectiveHilbertFunction K ι ((Scheme.Modules.pullback (map ψ ι)).obj G) =
      projectiveHilbertFunction k ι G := by
  funext m
  let := ψ.toAlgebra
  have := isQuasicoherent_moduleTensorLeftFunctor (twistingSheaf k ι m) G
  have h (q : ℕ) : projectiveCohomologyDim K ι ((Scheme.Modules.pullback (map ψ ι)).obj
      ((moduleTensorLeftFunctor (ProjectiveSpace k ι) (twistingSheaf k ι m)).obj G)) q =
      projectiveCohomologyDim k ι
        ((moduleTensorLeftFunctor (ProjectiveSpace k ι) (twistingSheaf k ι m)).obj G) q :=
    projectiveCohomologyDim_pullback_map k K ι _ q
  unfold projectiveHilbertFunction
  rw [← projectiveEulerChar_congr K ι (twistingTensorPullbackIso ψ ι m G)]
  unfold projectiveEulerChar
  exact finsum_congr fun q => by rw [h q]

end AlgebraicGeometry.Scheme.Cohomology
