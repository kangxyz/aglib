/-
Copyright (c) 2026 Algebraic geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.LinearAlgebra.ExteriorPower.Wedge
public import Aglib.RingTheory.Grassmannian.Plucker

/-!
# Injectivity of the Plücker map on points

`Module.Grassmannian.plucker_injective`: a point `N ∈ G(k, A ⊗[R] M; A)` is determined by its
Plücker point. The Plücker point is the preimage, under the surjective base-change map
`A ⊗[R] ⋀[R]^k M → ⋀[A]^k (A ⊗[R] M)`, of the kernel of `⋀^k` of the quotient map, so that kernel
is determined (`ker_map_mkQ_eq_of_plucker_eq`). For `k = j + 1` it determines `N`
(`exteriorPower.mem_iff_forall_wedgeLeft_mem_ker`: `v ∈ N` exactly when `v ∧ η` lies in it for
every `η ∈ ⋀^j`); for `k = 0` every point is `⊤`.

Source: Nitsure, *Construction of Hilbert and Quot schemes*, arXiv:math/0504590v1, §1, p. 9
("Projective embedding": the Plücker sections separate points, left to the reader there).
-/

@[expose] public section

noncomputable section

open TensorProduct

universe u w

namespace Module.Grassmannian

variable {R : Type u} [CommRing R] {M : Type u} [AddCommGroup M] [Module R M] {k : ℕ}
  {A : Type w} [CommRing A] [Algebra R A]

/-- Points with the same Plücker point have the same kernel of `⋀^k` of the quotient map. -/
theorem ker_map_mkQ_eq_of_plucker_eq {N₁ N₂ : G(k, A ⊗[R] M; A)}
    (h : plucker N₁ = plucker N₂) :
    LinearMap.ker (exteriorPower.map k N₁.toSubmodule.mkQ) =
      LinearMap.ker (exteriorPower.map k N₂.toSubmodule.mkQ) := by
  have h' := congrArg Module.Grassmannian.toSubmodule h
  rw [plucker_toSubmodule, plucker_toSubmodule, pluckerMap, pluckerMap, LinearMap.ker_comp,
    LinearMap.ker_comp] at h'
  have hγ := exteriorPower.liftBaseChange_toBaseChange_surjective R A k M
  rw [← Submodule.map_comap_eq_of_surjective hγ
      (LinearMap.ker (exteriorPower.map k N₁.toSubmodule.mkQ)), h',
    Submodule.map_comap_eq_of_surjective hγ]

/-- **The Plücker map is injective on points**: a point of the Grassmannian is determined by the
top exterior power of its quotient. -/
theorem plucker_injective :
    Function.Injective (plucker : G(k, A ⊗[R] M; A) → G(1, A ⊗[R] ⋀[R]^k M; A)) := by
  intro N₁ N₂ h
  have hK := ker_map_mkQ_eq_of_plucker_eq h
  apply Module.Grassmannian.ext
  cases k with
  | zero =>
    have h0 : ∀ N : G(0, A ⊗[R] M; A), N.toSubmodule = ⊤ := fun N => by
      have : Subsingleton ((A ⊗[R] M) ⧸ N.toSubmodule) :=
        Module.rankAtStalk_eq_zero_iff_subsingleton.mp (funext N.rankAtStalk_eq)
      exact Submodule.Quotient.subsingleton_iff.mp this
    rw [h0 N₁, h0 N₂]
  | succ j =>
    ext v
    rw [exteriorPower.mem_iff_forall_wedgeLeft_mem_ker N₁.toSubmodule N₁.rankAtStalk_eq v,
      exteriorPower.mem_iff_forall_wedgeLeft_mem_ker N₂.toSubmodule N₂.rankAtStalk_eq v, hK]

end Module.Grassmannian
