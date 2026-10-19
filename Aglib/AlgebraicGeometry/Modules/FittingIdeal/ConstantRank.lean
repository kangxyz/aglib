/-
Copyright (c) 2026 Algebraic geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Modules.FittingIdeal.LocallyFree
public import Aglib.AlgebraicGeometry.Modules.LocallyFree.Pullback
public import Aglib.AlgebraicGeometry.Modules.LocallyFree.Affine.Projective
public import Aglib.AlgebraicGeometry.Modules.LocallyFree.Affine.LocalBases
public import Aglib.AlgebraicGeometry.Modules.LocallyFree.FiniteType

/-!
# Constant rank: pullback, isomorphism, and global sections on `Spec A`

Constant rank `k` (`SheafHasRank M k`, a local basis indexed by `Fin k` on every cover member) is
stable under pullback along every morphism of schemes (`sheafHasRank_pullback`) and under
isomorphism (`sheafHasRank_of_iso`).

On `Spec A` the fibre rank at `y` of a finitely presented sheaf whose module of global sections is
finite and flat is the stalk rank at `y` of its global sections (`sheafRank_eq_rankAtStalk`,
through the Fitting criterion `sheafRank_le_iff_fittingIdeal_moduleSpecΓFunctor`; flatness is
needed: for `A = ℤ` and `(ℤ/p)~` the fibre rank at `(p)` is `1` and the stalk rank is `0`).
Consequently a finite projective module of constant stalk rank `k` has a sheaf of constant rank
`k` (`sheafHasRank_tilde`), and the global sections of a sheaf of constant rank `k` on `Spec A`
have constant stalk rank `k` (`rankAtStalk_globalSections`).
-/

@[expose] public section

noncomputable section

set_option backward.isDefEq.respectTransparency false

universe u

open CategoryTheory

namespace AlgebraicGeometry.Scheme.Modules

section Pullback

variable {X Y : Scheme.{u}}

/-- Constant rank is stable under pullback. -/
theorem sheafHasRank_pullback (f : X ⟶ Y) {M : Y.Modules} {k : ℕ} (h : SheafHasRank M k) :
    SheafHasRank ((pullback f).obj M) k := by
  have : IsFiniteLocallyFree Y M := h.isFiniteLocallyFree
  rw [sheafHasRank_iff_rank_eq]
  intro x
  rw [sheafRank_pullback M f x]
  exact (sheafHasRank_iff_rank_eq M k).mp h (f x)

/-- Constant rank is invariant under isomorphism. -/
theorem sheafHasRank_of_iso {M N : X.Modules} (e : M ≅ N) {k : ℕ}
    (h : SheafHasRank M k) : SheafHasRank N k := by
  obtain ⟨q, hq, hk⟩ := h
  exact ⟨localBasisOfIso e q, inferInstance, hk⟩

end Pullback

section Affine

variable {A : CommRingCat.{u}} {k : ℕ}


/-- On `Spec A`, the fibre rank at `y` of a finitely presented sheaf whose module of global sections
is finite and flat is the stalk rank at `y` of its global sections. -/
theorem sheafRank_eq_rankAtStalk (G : (Spec A).Modules)
    [G.IsFinitePresentation] [Module.Finite A (moduleSpecΓFunctor.obj G)]
    [Module.Flat A (moduleSpecΓFunctor.obj G)] (y : PrimeSpectrum A) :
    sheafRank G y = Module.rankAtStalk (R := A) (moduleSpecΓFunctor.obj G) y := by
  have hG := QuasiCoherent.affineLocallyFiniteType_of_finitePresentation G
  have key : ∀ j, sheafRank G y ≤ j ↔
      Module.rankAtStalk (R := A) (moduleSpecΓFunctor.obj G) y ≤ j := fun j ↦ by
    rw [sheafRank_le_iff_fittingIdeal_moduleSpecΓFunctor (A := A) G hG y j,
      Module.rankAtStalk_eq, ← Module.finrank_residueField_tensor_le_iff]
  exact le_antisymm ((key _).mpr le_rfl) ((key _).mp le_rfl)

/-- A finite projective module of constant rank `k` gives a sheaf of constant rank `k`. -/
theorem sheafHasRank_tilde (P : ModuleCat.{u} A) [Module.Finite A P] [Module.Projective A P]
    (hk : ∀ p, Module.rankAtStalk (R := A) P p = k) :
    SheafHasRank (tilde P) k := by
  have : IsFiniteLocallyFree (Spec A) (tilde P) :=
    finiteLocallyFree_tilde_of_finite_projective A P
  let e : P ≃ₗ[A] moduleSpecΓFunctor.obj (tilde P) :=
    (tilde.toTildeΓNatIso.app P).toLinearEquiv
  have : Module.Finite A (moduleSpecΓFunctor.obj (tilde P)) :=
    Module.Finite.equiv e
  have : Module.Projective A (moduleSpecΓFunctor.obj (tilde P)) :=
    Module.Projective.of_equiv e
  rw [sheafHasRank_iff_rank_eq]
  intro y
  rw [sheafRank_eq_rankAtStalk, ← congrFun (Module.rankAtStalk_eq_of_equiv e) y]
  exact hk y

/-- The global sections of a sheaf of constant rank `k` on `Spec A` have constant stalk rank
`k`. -/
theorem rankAtStalk_globalSections (Q : (Spec A).Modules)
    (h : SheafHasRank Q k) (p : PrimeSpectrum A) :
    Module.rankAtStalk (R := A) (moduleSpecΓFunctor.obj Q) p = k := by
  have : IsFiniteLocallyFree _ Q := h.isFiniteLocallyFree
  have : Module.Finite A (moduleSpecΓFunctor.obj Q) :=
    finite_globalSections_of_finiteLocallyFree A Q
  have : Module.Projective A (moduleSpecΓFunctor.obj Q) :=
    projective_globalSections_of_finiteLocallyFree A Q
  rw [← sheafRank_eq_rankAtStalk]
  exact (sheafHasRank_iff_rank_eq Q k).mp h p

end Affine

end AlgebraicGeometry.Scheme.Modules
