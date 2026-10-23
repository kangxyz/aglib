/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.FundamentalGroup.Basic

/-! # Pointed fibre transport and actual precomposition

The native inverse pullback-fibre equivalence preserves precomposition by
endomorphisms of the common point scheme. Keeping the actual pointed map,
automorphisms and endomorphisms as typed parameters avoids unfolding their
concrete geometric constructions inside the natural-transformation proof.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open Scheme.FiniteEtale

namespace AlgebraicGeometry.Scheme.EtaleFundamentalGroups

universe u

variable {K : Type u} [Field K] {S X : PointedScheme K} (f : S ⟶ X)

/-- Projection of the actual pulled-back point recovers the original point. -/
theorem pointedFiberEquiv_left_projection (Y : Scheme.FiniteEtale X.right)
    (p : Fiber X.hom Y) :
    (pointedFiberEquiv f Y p).left ≫ pullback.fst Y.obj.hom f.right = p.left := by
  have h := pointedFiberEquiv_symm_left f Y (pointedFiberEquiv f Y p)
  exact h.symm.trans (congrArg (fun q : Fiber X.hom Y => q.left)
    ((pointedFiberEquiv f Y).symm_apply_apply p))

/-- Actual inverse fibre transport commutes with point precomposition when
the two original point endomorphisms have the same underlying scheme map. -/
theorem pointedFiberEquiv_symm_precomp
    (g : Over.mk S.hom ⟶ Over.mk S.hom)
    (h : Over.mk X.hom ⟶ Over.mk X.hom) (he : g.left = h.left)
    (Y : Scheme.FiniteEtale X.right) (p : Fiber X.hom Y) :
    (pointedFiberEquiv f Y).symm (g ≫ pointedFiberEquiv f Y p) = h ≫ p := by
  apply Over.OverMorphism.ext
  rw [pointedFiberEquiv_symm_left]
  change (g.left ≫ (pointedFiberEquiv f Y p).left) ≫
    pullback.fst Y.obj.hom f.right = h.left ≫ p.left
  exact (Category.assoc _ _ _).trans
    ((congrArg (fun z : Spec (.of K) ⟶ Y.obj.left => g.left ≫ z)
      (pointedFiberEquiv_left_projection f Y p)).trans
        (congrArg (fun z : Spec (.of K) ⟶ Spec (.of K) => z ≫ p.left) he))

/-- Pointwise equality through the original pullback-fibre equivalence is
an equality of the original pointed fibre automorphisms. -/
theorem pointedMap_eq_of_fiber_components
    (a : FiberAutGroup S.hom) (b : FiberAutGroup X.hom)
    (h : ∀ (Y : Scheme.FiniteEtale X.right) (p : Fiber X.hom Y),
      (pointedFiberEquiv f Y).symm
        (a.hom.app ((baseChange f.right).obj Y) (pointedFiberEquiv f Y p)) =
          b.hom.app Y p) : pointedMap f a = b := by
  apply Aut.ext
  apply NatTrans.ext
  funext Y
  apply FintypeCat.hom_ext
  intro p
  exact h Y p

end AlgebraicGeometry.Scheme.EtaleFundamentalGroups
