/-
Copyright (c) 2026 Algebraic geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Grassmannian.Quotient.Kernel
public import Aglib.AlgebraicGeometry.Modules.LocallyFree.Kernel
public import Aglib.AlgebraicGeometry.Modules.LocallyFree.RankAdditivity

/-!
# The kernel of a rank-`k` quotient of `O^n` has rank `n - k`

For `q : LocallyFreeQuotient X k n`, the kernel `q.kernel` of `q.π : O_X^n ⟶ Q` is finite locally
free (`isFiniteLocallyFree_kernel`), hence quasi-coherent, and has constant rank `n - k`
(`sheafHasRank_kernel`): at every point the fibre ranks satisfy `n = rank K + k`
(`sheafRank_X₂_eq_add_of_shortExact`). For nonempty `X` this forces `k ≤ n`
(`rank_le_of_nonempty`).

Source: Nitsure, *Construction of Hilbert and Quot schemes*, arXiv:math/0504590v1, §5, p. 26
(the kernel `K` of the universal quotient and its pullbacks `K_Y`); rank additivity is stated in
the text of Stacks, Tag 0B37, without proof, and the kernel statement has no Stacks lemma. Encoded
subset: quotients of `O^n = SheafOfModules.free (ULift (Fin n))` on arbitrary schemes, all `k`
and `n`; `n - k` is truncated subtraction (on an empty scheme every rank holds). Convention: `k` is
the rank of the quotient.
-/

@[expose] public section

noncomputable section

set_option backward.isDefEq.respectTransparency false

universe u

open CategoryTheory Opposite Limits

namespace AlgebraicGeometry.Grassmannian

open Scheme.Modules

namespace LocallyFreeQuotient

variable {X : Scheme.{u}} {k n : ℕ}

/-- The kernel of a rank-`k` locally free quotient of `O_X^n` is finite locally free. -/
instance isFiniteLocallyFree_kernel (q : LocallyFreeQuotient X k n) :
    IsFiniteLocallyFree X q.kernel :=
  have : IsFiniteLocallyFree X q.shortComplex.X₂ :=
    inferInstanceAs (IsFiniteLocallyFree X (freeSheaf X n))
  have : IsFiniteLocallyFree X q.shortComplex.X₃ := q.isFiniteLocallyFree_obj
  finiteLocallyFree_X₁_of_shortExact q.shortExact

/-- The kernel of a quotient is quasi-coherent. -/
instance isQuasicoherent_kernel (q : LocallyFreeQuotient X k n) : q.kernel.IsQuasicoherent :=
  inferInstance

/-- At every point, the fibre ranks of `0 → K → O_X^n → Q → 0` satisfy `n = rank K + k`. -/
theorem sheafRank_kernel_add (q : LocallyFreeQuotient X k n) (x : X) :
    sheafRank q.kernel x + k = n := by
  have : IsFiniteLocallyFree X q.shortComplex.X₁ := q.isFiniteLocallyFree_kernel
  have : IsFiniteLocallyFree X q.shortComplex.X₃ := q.isFiniteLocallyFree_obj
  have h := sheafRank_X₂_eq_add_of_shortExact q.shortExact x
  have hfree : sheafRank (freeSheaf X n) x = n := by
    rw [sheafRank_free, Nat.card_ulift, Nat.card_eq_fintype_card, Fintype.card_fin]
  have hQ := (sheafHasRank_iff_rank_eq q.obj k).mp q.hasRank x
  change sheafRank (freeSheaf X n) x = sheafRank q.kernel x + sheafRank q.obj x at h
  omega

/-- **The kernel of a rank-`k` quotient of `O^n` is finite locally free of rank `n - k`.** -/
theorem sheafHasRank_kernel (q : LocallyFreeQuotient X k n) : SheafHasRank q.kernel (n - k) :=
  (sheafHasRank_iff_rank_eq q.kernel (n - k)).mpr fun x ↦ by
    have := q.sheafRank_kernel_add x
    omega

/-- A rank-`k` locally free quotient of `O^n` on a nonempty scheme has `k ≤ n`. -/
theorem rank_le_of_nonempty (q : LocallyFreeQuotient X k n) [Nonempty X] : k ≤ n := by
  obtain ⟨x⟩ := ‹Nonempty X›
  have := q.sheafRank_kernel_add x
  omega

end LocallyFreeQuotient

end AlgebraicGeometry.Grassmannian
