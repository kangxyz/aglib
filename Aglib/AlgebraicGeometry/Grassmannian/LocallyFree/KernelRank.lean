/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Grassmannian.LocallyFree.Basic
public import Aglib.AlgebraicGeometry.Modules.LocallyFree.Kernel
public import Aglib.AlgebraicGeometry.Modules.LocallyFree.KernelPullback
public import Aglib.AlgebraicGeometry.Modules.LocallyFree.RankAdditivity
public import Aglib.AlgebraicGeometry.Modules.Invertible.RankOne
public import Aglib.AlgebraicGeometry.Modules.LocallyFree.LineSubbundle

/-!
# Kernels of locally free quotients

For a rank-`k` locally free quotient `P : F ↠ Q` of a module sheaf `F`, the kernel `K = ker P.π`
fits in the short exact sequence `0 → K → F → Q → 0`. If `F` is finite locally free, so is `K`
(`isFiniteLocallyFree_kernel`), and its rank is the difference of the ranks
(`sheafRank_kernel_add`). If `F` has constant rank `k + 1`, the kernel is a line bundle
(`isLocallyRankOne_kernel`): a point of `Gr(F, k)` is a line subbundle of `F` with locally free
quotient, the form in which Kleiman's `P(Q)` with `Q = F^∨` appears in the proof of
Thm 3.13 (*The Picard scheme*, arXiv:math/0504020v1, pp. 25–26).

Conversely, a map `u : N ⟶ F` from a locally rank-one sheaf to `F` of constant rank `k + 1` that
is nonzero on every field fibre gives the point `ofLineSubbundle` of `Gr(F, k)`, the quotient
`F ↠ coker u` (`Modules/LocallyFree/LineSubbundle`), whose kernel inclusion is `u` up to an
isomorphism `N ≅ ker (F ↠ coker u)` (`exists_iso_hom_kernel_ι_ofLineSubbundle`).

This is the locally free counterpart of `Grassmannian/Quotient/KernelRank` (quotients of `O^n`).
Arbitrary schemes; no Noetherian hypothesis.
-/

@[expose] public section

noncomputable section

set_option backward.isDefEq.respectTransparency false

universe u

open CategoryTheory Limits

namespace AlgebraicGeometry.Grassmannian.LocallyFreeQuotientOf

open Scheme.Modules

variable {X : Scheme.{u}} {F : X.Modules} {k : ℕ}

/-- The kernel of a locally free quotient of a finite locally free sheaf is finite locally free. -/
theorem isFiniteLocallyFree_kernel [IsFiniteLocallyFree X F] (P : LocallyFreeQuotientOf F k) :
    IsFiniteLocallyFree X (kernel P.π) := by
  have hS := shortExact_kernelSequence P.π
  have : IsFiniteLocallyFree X (ShortComplex.kernelSequence P.π).X₂ :=
    inferInstanceAs (IsFiniteLocallyFree X F)
  have : IsFiniteLocallyFree X (ShortComplex.kernelSequence P.π).X₃ :=
    P.hasRank.isFiniteLocallyFree
  exact finiteLocallyFree_X₁_of_shortExact hS

/-- Ranks add along the kernel sequence of a locally free quotient. -/
theorem sheafRank_kernel_add [IsFiniteLocallyFree X F] (P : LocallyFreeQuotientOf F k) (x : X) :
    sheafRank F x = sheafRank (kernel P.π) x + sheafRank P.obj x := by
  have hS := shortExact_kernelSequence P.π
  have : IsFiniteLocallyFree X (ShortComplex.kernelSequence P.π).X₁ :=
    isFiniteLocallyFree_kernel P
  have : IsFiniteLocallyFree X (ShortComplex.kernelSequence P.π).X₃ :=
    P.hasRank.isFiniteLocallyFree
  exact sheafRank_X₂_eq_add_of_shortExact hS x

/-- **The kernel of a corank-one locally free quotient is a line bundle**: if `F` has constant
rank `k + 1` and `Q` has rank `k`, then `ker (F ↠ Q)` is locally free of rank one. -/
theorem isLocallyRankOne_kernel (hF : SheafHasRank F (k + 1)) (P : LocallyFreeQuotientOf F k) :
    Invertible.IsLocallyRankOne X (kernel P.π) := by
  have : IsFiniteLocallyFree X F := hF.isFiniteLocallyFree
  have : IsFiniteLocallyFree X P.obj := P.hasRank.isFiniteLocallyFree
  have : IsFiniteLocallyFree X (kernel P.π) := isFiniteLocallyFree_kernel P
  rw [Invertible.isLocallyRankOne_iff_sheafHasRank_one, sheafHasRank_iff_rank_eq]
  intro x
  have h1 := sheafRank_kernel_add P x
  have h2 := (sheafHasRank_iff_rank_eq F (k + 1)).mp hF x
  have h3 := (sheafHasRank_iff_rank_eq P.obj k).mp P.hasRank x
  omega

/-- **The quotient by a line subbundle**: for `F` of constant rank `k + 1` and `u : N ⟶ F` from a
locally rank-one sheaf, nonzero on every field fibre, `F ↠ coker u` is a rank-`k` locally free
quotient of `F`. -/
def ofLineSubbundle (hF : SheafHasRank F (k + 1)) {N : X.Modules}
    (hN : Invertible.IsLocallyRankOne X N) (u : N ⟶ F)
    (hu : ∀ (K : Type u) [Field K] (t : Spec (.of K) ⟶ X),
      (Scheme.Modules.pullback t).map u ≠ 0) :
    LocallyFreeQuotientOf F k where
  obj := cokernel u
  π := cokernel.π u
  epi_π := inferInstance
  hasRank := by
    have : IsFiniteLocallyFree X F := hF.isFiniteLocallyFree
    have h := sheafHasRank_cokernel_of_pullback_map_ne_zero hN u hu hF
    rwa [Nat.add_sub_cancel] at h

theorem ofLineSubbundle_π (hF : SheafHasRank F (k + 1)) {N : X.Modules}
    (hN : Invertible.IsLocallyRankOne X N) (u : N ⟶ F)
    (hu : ∀ (K : Type u) [Field K] (t : Spec (.of K) ⟶ X),
      (Scheme.Modules.pullback t).map u ≠ 0) :
    (ofLineSubbundle hF hN u hu).π = cokernel.π u :=
  rfl

/-- The kernel inclusion of the quotient by a line subbundle `u` is `u`, up to an isomorphism
`N ≅ ker (F ↠ coker u)`: a fibrewise nonzero `u` is a monomorphism. -/
theorem exists_iso_hom_kernel_ι_ofLineSubbundle (hF : SheafHasRank F (k + 1)) {N : X.Modules}
    (hN : Invertible.IsLocallyRankOne X N) (u : N ⟶ F)
    (hu : ∀ (K : Type u) [Field K] (t : Spec (.of K) ⟶ X),
      (Scheme.Modules.pullback t).map u ≠ 0) :
    ∃ e : N ≅ kernel (ofLineSubbundle hF hN u hu).π,
      e.hom ≫ kernel.ι (ofLineSubbundle hF hN u hu).π = u := by
  have : IsFiniteLocallyFree X F := hF.isFiniteLocallyFree
  have hS := shortExact_cokernel_of_pullback_map_ne_zero hN u hu
  exact ⟨IsLimit.conePointUniqueUpToIso hS.fIsKernel (limit.isLimit _),
    IsLimit.conePointUniqueUpToIso_hom_comp hS.fIsKernel (limit.isLimit _)
      WalkingParallelPair.zero⟩

end AlgebraicGeometry.Grassmannian.LocallyFreeQuotientOf
