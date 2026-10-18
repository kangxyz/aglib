/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Cohomology.Projective.Regularity.Mumford.Ambient
public import Aglib.AlgebraicGeometry.Cohomology.Projective.HilbertPolynomial.FieldBaseChange
public import Aglib.AlgebraicGeometry.ProjectiveSpace.BaseChange.Flat
public import Aglib.AlgebraicGeometry.ProjectiveSpace.BaseChange.Twisting
public import Aglib.AlgebraicGeometry.Modules.QuasiCoherent.FiniteType.Pullback

/-!
# Descent of Mumford's bound along a field extension

Nitsure (arXiv:math/0504590v1) proves Lemma 2.1 (p. 10) and Thm 2.3 (p. 12) after passing to an
infinite field: cohomology base-changes correctly under a field extension. This leaf carries
that reduction out for Thm 2.3, for `π = ProjectiveSpace.map (algebraMap k K) ι`, with the base
change of the twisting sheaves `ProjectiveSpace.twistingPullbackIso` and its twisted-module form
`twistingTensorPullbackIso` (`ProjectiveSpace/BaseChange/Twisting.lean`):
* `projectiveCohomologyDim_twist_pullback`: `hᵠ(O_K(d) ⊗ π^* F) = hᵠ(O_k(d) ⊗ F)`, from
  `projectiveCohomologyDim_pullback_map`;
* `IsProjectiveRegular.of_pullback_map`: regularity of `π^* F` gives regularity of `F`; the
  Hilbert functions agree (`projectiveHilbertFunction_pullback_map`, in
  `HilbertPolynomial/FieldBaseChange`);
* `isProjectiveRegular_mumfordBound_free_of_extension`: Thm 2.3 over `k` follows from the
  premise `HasHyperplaneSections K ι` over the extension `K`.
-/

@[expose] public section

noncomputable section

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry.ProjectiveSpace
open AlgebraicGeometry.Scheme.Modules
open AlgebraicGeometry.Scheme.Modules.QuasiCoherent

universe u

namespace AlgebraicGeometry.Scheme.Cohomology

variable {k K : Type u} [Field k] [Field K] [Algebra k K] {ι : Type u}

/-- `hᵠ(O_K(d) ⊗ π^* F) = hᵠ(O_k(d) ⊗ F)` for quasicoherent `F`. -/
theorem projectiveCohomologyDim_twist_pullback [Finite ι] (d : ℤ)
    (F : (ProjectiveSpace k ι).Modules) [F.IsQuasicoherent] (q : ℕ) :
    projectiveCohomologyDim K ι ((moduleTensorLeftFunctor (ProjectiveSpace K ι)
        (twistingSheaf K ι d)).obj
          ((Scheme.Modules.pullback (ProjectiveSpace.map (algebraMap k K) ι)).obj F)) q =
      projectiveCohomologyDim k ι
        ((moduleTensorLeftFunctor (ProjectiveSpace k ι) (twistingSheaf k ι d)).obj F) q := by
  have : ((moduleTensorLeftFunctor (ProjectiveSpace k ι) (twistingSheaf k ι d)).obj
      F).IsQuasicoherent := twistingTensor_isQuasicoherent k ι F d
  rw [← projectiveCohomologyDim_congr K ι (twistingTensorPullbackIso (algebraMap k K) ι d F) q]
  exact projectiveCohomologyDim_pullback_map k K ι _ q

/-- **Regularity descends along a field extension**: if `π^* F` is `m`-regular on `P^n_K`, then
the coherent module `F` is `m`-regular on `P^n_k`. -/
theorem IsProjectiveRegular.of_pullback_map (n : ℕ) (e : ι ≃ Fin (n + 1))
    {F : (ProjectiveSpace k ι).Modules} (hF : affineLocallyFiniteType (ProjectiveSpace k ι) F)
    {m : ℤ} (h : IsProjectiveRegular K ι
      ((Scheme.Modules.pullback (ProjectiveSpace.map (algebraMap k K) ι)).obj F) m) :
    IsProjectiveRegular k ι F m := by
  have : Finite ι := Finite.of_equiv _ e.symm
  have : F.IsQuasicoherent := quasicoherent_of_affineCharts _ (fun A j _ => (hF A j).1)
  intro q hq
  apply subsingleton_of_projectiveCohomologyDim_eq_zero n e
    (twistingTensor_affineLocallyFiniteType k ι _ F hF)
  rw [← projectiveCohomologyDim_twist_pullback (K := K) _ F q]
  exact projectiveCohomologyDim_eq_zero_of_subsingleton (h q hq)

/-- The pullback of the free module `∐_{i : I} O_k(0)` is `∐_{i : I} O_K(0)`. -/
theorem nonempty_pullback_twistingCoproduct_iso (I : Type u) :
    Nonempty ((Scheme.Modules.pullback (ProjectiveSpace.map (algebraMap k K) ι)).obj
        (∐ fun _ : I => twistingSheaf k ι 0) ≅ ∐ fun _ : I => twistingSheaf K ι 0) :=
  ⟨PreservesCoproduct.iso (Scheme.Modules.pullback
      (ProjectiveSpace.map (algebraMap k K) ι)) (fun _ : I => twistingSheaf k ι 0) ≪≫
    Sigma.mapIso fun _ => ProjectiveSpace.twistingPullbackIso (algebraMap k K) ι 0⟩

/-- **Mumford's bound over any field, from an extension with hyperplane sections** (Nitsure,
arXiv:math/0504590v1, Thm 2.3, p. 11, reduced to an infinite field on p. 12): if `K / k` is a field
extension with `HasHyperplaneSections K ι`, every coherent submodule `F` of `O^p` on `P^n_k` with
`χ(F(r)) = Σ_{i ≤ n} aᵢ C(r, i)` is `mumfordBound n p (n + 1)`-regular at `a`. -/
theorem isProjectiveRegular_mumfordBound_free_of_extension (n p : ℕ) (e : ι ≃ Fin (n + 1))
    (hgen : HasHyperplaneSections K ι)
    {F : (ProjectiveSpace k ι).Modules}
    (j : F ⟶ ∐ fun _ : ULift.{u} (Fin p) => twistingSheaf k ι 0) [Mono j]
    (hF : affineLocallyFiniteType (ProjectiveSpace k ι) F) (a : Fin (n + 1) → ℤ)
    (hχ : ∀ r : ℤ, projectiveHilbertFunction k ι F r =
      ∑ i : Fin (n + 1), a i * Ring.choose r i) :
    IsProjectiveRegular k ι F (MvPolynomial.eval a (mumfordBound n p (n + 1))) := by
  have : Finite ι := Finite.of_equiv _ e.symm
  have : F.IsQuasicoherent := quasicoherent_of_affineCharts _ (fun A j _ => (hF A j).1)
  obtain ⟨ψ⟩ := nonempty_pullback_twistingCoproduct_iso (k := k) (K := K) (ι := ι)
    (ULift.{u} (Fin p))
  let j' := (Scheme.Modules.pullback (ProjectiveSpace.map (algebraMap k K) ι)).map j ≫ ψ.hom
  have : Mono j' := mono_comp _ _
  apply IsProjectiveRegular.of_pullback_map (K := K) n e hF
  exact isProjectiveRegular_mumfordBound_free_of_hasHyperplaneSections n p e hgen j'
    (affineLocallyFiniteType_pullback _ hF) a
    (fun r => (congrFun (projectiveHilbertFunction_pullback_map ι (algebraMap k K) F) r).trans
      (hχ r))

end AlgebraicGeometry.Scheme.Cohomology
