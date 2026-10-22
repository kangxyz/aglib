/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Modules.BaseChange.Affine.Mate

/-! # Original adjoints commute with the original base-change mate

For any actual cartesian square, base change of an adjoint followed by the
native pushforward comparison is the adjoint of the original pulled-back
arrow. This is an equation of actual maps, without invertibility hypotheses.
-/

@[expose] public noncomputable section
open CategoryTheory
namespace AlgebraicGeometry.Scheme.Modules
universe u
variable {W X T S : Scheme.{u}}

/-- Base change preserves the original adjunction equation through its actual mate. -/
theorem cartesianBaseChangeMap_adjoint
    (a : W ⟶ X) (b : W ⟶ T) (f : X ⟶ S) (g : T ⟶ S)
    (h : CategoryTheory.IsPullback a b f g)
    (M : S.Modules) (N : X.Modules) (e : (pullback f).obj M ⟶ N) :
    (pullback g).map ((pullbackPushforwardAdjunction f).homEquiv _ _ e) ≫
      (cartesianBaseChangeMap a b f g h).app N =
    (pullbackPushforwardAdjunction b).homEquiv _ _
      ((pullbackSquareIso a b f g h.w).hom.app M ≫ (pullback a).map e) := by
  let δ := (pullbackPushforwardAdjunction f).homEquiv _ _ e
  let c := (pullbackSquareIso a b f g h.w).hom
  rw [cartesianBaseChangeMap_eq_counit,
    ← (pullbackPushforwardAdjunction b).homEquiv_naturality_left]
  congr 1
  change (pullback g ⋙ pullback b).map δ ≫
      c.app ((pushforward f).obj N) ≫
        (pullback a).map ((pullbackPushforwardAdjunction f).counit.app N) =
    c.app M ≫ (pullback a).map e
  rw [← Category.assoc, c.naturality δ, Category.assoc]
  change c.app M ≫ (pullback a).map ((pullback f).map δ) ≫
      (pullback a).map ((pullbackPushforwardAdjunction f).counit.app N) = _
  rw [← Functor.map_comp]
  have he : (pullback f).map δ ≫
      (pullbackPushforwardAdjunction f).counit.app N = e :=
    ((pullbackPushforwardAdjunction f).homEquiv M N).symm_apply_apply e
  rw [he]

end AlgebraicGeometry.Scheme.Modules
