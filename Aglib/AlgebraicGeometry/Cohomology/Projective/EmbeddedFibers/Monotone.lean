/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Cohomology.Projective.EmbeddedFibers.Projective
public import Aglib.AlgebraicGeometry.Cohomology.Projective.HilbertPolynomial.GeneralHyperplane
public import Aglib.AlgebraicGeometry.ProjectiveSpace.Tensor.Equivalence
public import Aglib.AlgebraicGeometry.Modules.Invertible.Affine
public import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure

/-!
# Global sections of twists do not decrease

For a coherent `F` on `P^N_k` over an infinite field `k`, multiplication by a general section `s`
of `O(1)` is injective on `O(m) ⊗ F`: the frame coefficients of `s` avoid the associated points
(`exists_forall_frameCoefficient_isSMulRegular`, Nitsure, *Construction of Hilbert and Quot
schemes*, arXiv:math/0504590v1, p. 10), so `O(m) ⊗ F → O(1) ⊗ O(m) ⊗ F ≅ O(m + 1) ⊗ F` is a
monomorphism (`mono_twistingTensorMultiply_of_isSMulRegular`) and
`h^0(O(m) ⊗ F) ≤ h^0(O(m + 1) ⊗ F)` (`projectiveCohomologyDim_twist_zero_le_add_one`).

For a closed immersion `i : X ⟶ P^N_A`, a field point `k : Spec K ⟶ Spec A` and a line bundle
`L` on `X_K`, the dimensions `h^0(X_K, O(m) ⊗ L)` therefore do not decrease in `m`
(`embeddedFiberTwistDim_zero_le_add_one`): pass to the algebraic closure of `K`, which leaves the
dimensions unchanged (`embeddedFiberTwistDim_fieldBaseChange`), and compute on `P^N` there
(`embeddedFiberTwistDim_eq_projectiveCohomologyDim`). In particular
`h^0(X_K, O(m) ⊗ L) ≠ 0` implies `h^0(X_K, O(m') ⊗ L) ≠ 0` for every `m' ≥ m`
(`embeddedFiberTwistDim_zero_ne_zero_of_le`).

This is the monotonicity of the strata `Pic^φ_m` in `m` (Kleiman, *The Picard scheme*,
arXiv:math/0504020v1, proof of Thm 4.8, p. 29, with the nonvanishing condition of the plan's
repair). The plan's argument multiplies by a section of `O(1)` nonzero on the integral fibre;
the general hyperplane used here needs neither integrality nor a rational point of the fibre.
-/

@[expose] public section

noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open AlgebraicGeometry.Scheme.Modules AlgebraicGeometry.Scheme.Modules.QuasiCoherent
open AlgebraicGeometry.ProjectiveSpace

namespace AlgebraicGeometry.Scheme.Cohomology

/-- Over an infinite field, a general section of `O(1)` is a nonzerodivisor on a coherent `G`, so
`h^0(G) ≤ h^0(O(1) ⊗ G)`. -/
theorem projectiveCohomologyDim_zero_le_twist_one {k : Type u} [Field k] [Infinite k]
    {ι : Type u} (N : ℕ) (e : ι ≃ Fin (N + 1)) (G : (ProjectiveSpace k ι).Modules)
    (hG : affineLocallyFiniteType (ProjectiveSpace k ι) G) :
    projectiveCohomologyDim k ι G 0 ≤ projectiveCohomologyDim k ι
      ((moduleTensorLeftFunctor (ProjectiveSpace k ι)
        (twistingSheaf k ι (((1 : ℕ) : ℤ) + 0))).obj G) 0 := by
  have : Finite ι := Finite.of_equiv _ e.symm
  obtain ⟨s, hs⟩ := exists_forall_frameCoefficient_isSMulRegular k ι (J := PUnit.{1})
    (fun _ => G) (fun _ => hG)
  have hmono : Mono ((twistingTensorZeroIso k ι).inv.app G ≫
      (twistingTensorMultiply k ι ((1 : ℕ) : ℤ) 0 s).app G) :=
    mono_twistingTensorMultiply_of_isSMulRegular k ι s G (hs ⟨⟩)
  exact projectiveCohomologyDim_zero_le_of_mono N e
    ((twistingTensorZeroIso k ι).inv.app G ≫ (twistingTensorMultiply k ι ((1 : ℕ) : ℤ) 0 s).app G)
    (twistingTensor_affineLocallyFiniteType k ι _ G hG)

/-- **Sections of twists do not decrease over an infinite field**: for coherent `F` on `P^N_k`,
`h^0(O(m) ⊗ F) ≤ h^0(O(m + 1) ⊗ F)`, by multiplication with a general section of `O(1)`. -/
theorem projectiveCohomologyDim_twist_zero_le_add_one {k : Type u} [Field k] [Infinite k]
    {ι : Type u} (N : ℕ) (e : ι ≃ Fin (N + 1)) (F : (ProjectiveSpace k ι).Modules)
    (hF : affineLocallyFiniteType (ProjectiveSpace k ι) F) (m : ℤ) :
    projectiveCohomologyDim k ι
        ((moduleTensorLeftFunctor (ProjectiveSpace k ι) (twistingSheaf k ι m)).obj F) 0 ≤
      projectiveCohomologyDim k ι
        ((moduleTensorLeftFunctor (ProjectiveSpace k ι) (twistingSheaf k ι (m + 1))).obj F) 0 := by
  have : Finite ι := Finite.of_equiv _ e.symm
  have hle := projectiveCohomologyDim_zero_le_twist_one N e _
    (twistingTensor_affineLocallyFiniteType k ι m F hF)
  have h2 := projectiveCohomologyDim_congr k ι
    ((twistingTensorCompIso k ι (((1 : ℕ) : ℤ) + 0) m).app F) 0
  have h3 : ((1 : ℕ) : ℤ) + 0 + m = m + 1 := by
    push_cast
    ring
  rw [h3] at h2
  exact hle.trans h2.le

variable {A : Type u} [CommRing A] {ι : Type u} {X : Scheme.{u}} (i : X ⟶ ProjectiveSpace A ι)

/-- **Sections of twists of a line bundle on a fibre do not decrease**: for a closed immersion
`i : X ⟶ P^N_A`, a field point `k : Spec K ⟶ Spec A` and a line bundle `L` on `X_K`,
`h^0(X_K, O(m) ⊗ L) ≤ h^0(X_K, O(m + 1) ⊗ L)`. -/
theorem embeddedFiberTwistDim_zero_le_add_one [IsClosedImmersion i] (N : ℕ)
    (e : ι ≃ Fin (N + 1)) {K : Type u} [Field K] (k : Spec (.of K) ⟶ Spec (.of A))
    (L : Invertible.LineBundle (pullback (i ≫ toSpec A ι) k)) (m : ℤ) :
    embeddedFiberTwistDim i k L.val m 0 ≤ embeddedFiberTwistDim i k L.val (m + 1) 0 := by
  have : Finite ι := Finite.of_equiv _ e.symm
  let σ : K →+* AlgebraicClosure K := algebraMap K (AlgebraicClosure K)
  have hq (n : ℤ) :
      (pulledTwist (pullback.fst (i ≫ toSpec A ι) k ≫ i) n L.val).IsQuasicoherent :=
    Invertible.lineBundle_isQuasicoherent ⟨_, isLocallyRankOne_pulledTwist _ n L.property⟩
  have := hq m
  have := hq (m + 1)
  rw [← embeddedFiberTwistDim_fieldBaseChange i k σ L.val m 0,
    ← embeddedFiberTwistDim_fieldBaseChange i k σ L.val (m + 1) 0]
  have hL' : affineLocallyFiniteType _
      ((Scheme.Modules.pullback (fieldExtensionBaseChange i k σ)).obj L.val) :=
    affineLocallyFiniteType_of_isLocallyRankOne
      (Invertible.pullback_locallyRankOne _ _ L.property)
  rw [embeddedFiberTwistDim_eq_projectiveCohomologyDim i _ _ hL' m 0,
    embeddedFiberTwistDim_eq_projectiveCohomologyDim i _ _ hL' (m + 1) 0]
  exact projectiveCohomologyDim_twist_zero_le_add_one N e _
    (affineLocallyFiniteType_pushforward_embeddedFiberι i _ hL') m

/-- `h^0(X_K, O(m) ⊗ L)` is monotone in `m`. -/
theorem embeddedFiberTwistDim_zero_mono [IsClosedImmersion i] (N : ℕ) (e : ι ≃ Fin (N + 1))
    {K : Type u} [Field K] (k : Spec (.of K) ⟶ Spec (.of A))
    (L : Invertible.LineBundle (pullback (i ≫ toSpec A ι) k)) {m m' : ℤ} (h : m ≤ m') :
    embeddedFiberTwistDim i k L.val m 0 ≤ embeddedFiberTwistDim i k L.val m' 0 := by
  induction m', h using Int.leInduction with
  | base => exact le_rfl
  | succ m' _ ih => exact ih.trans (embeddedFiberTwistDim_zero_le_add_one i N e k L m')

/-- **Monotonicity of the nonvanishing condition**: `h^0(X_K, O(m) ⊗ L) ≠ 0` implies
`h^0(X_K, O(m') ⊗ L) ≠ 0` for every `m' ≥ m`. -/
theorem embeddedFiberTwistDim_zero_ne_zero_of_le [IsClosedImmersion i] (N : ℕ)
    (e : ι ≃ Fin (N + 1)) {K : Type u} [Field K] (k : Spec (.of K) ⟶ Spec (.of A))
    (L : Invertible.LineBundle (pullback (i ≫ toSpec A ι) k)) {m m' : ℤ} (h : m ≤ m')
    (hm : embeddedFiberTwistDim i k L.val m 0 ≠ 0) : embeddedFiberTwistDim i k L.val m' 0 ≠ 0 :=
  fun h' => hm (Nat.eq_zero_of_le_zero ((embeddedFiberTwistDim_zero_mono i N e k L h).trans h'.le))

end AlgebraicGeometry.Scheme.Cohomology
