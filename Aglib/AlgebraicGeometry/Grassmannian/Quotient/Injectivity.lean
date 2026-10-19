/-
Copyright (c) 2026 Algebraic geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Grassmannian.Quotient.Points
public import Aglib.AlgebraicGeometry.Descent.Modules.ZariskiEpi

/-!
# Quotients are determined by their Grassmannian points

A class of rank-`k` locally free quotients of `O_T^n` is determined by its Grassmannian points
(`toPointsNatTrans_injective`): on the affine open cover `coverPt i` of `T`, equal points give
isomorphic quotients (`affinePoint_mk_eq_iff`), and two epimorphisms out of one module sheaf whose
pullbacks along a jointly surjective family of open immersions are compatibly isomorphic are
isomorphic (`Scheme.Modules.exists_iso_of_openImmersion`, in
`Aglib.AlgebraicGeometry.Descent.Modules.ZariskiEpi`; here `equiv_of_openImmersion`).

`AlgSpecPoints.isOpenImmersion_coverPt` and `AlgSpecPoints.exists_coverPt_apply_eq` say that the
affine charts `coverPt i : Spec (coverAlg i) ⟶ T` form a jointly surjective family of open
immersions.
-/

@[expose] public section

noncomputable section

set_option backward.isDefEq.respectTransparency false

universe u

open CategoryTheory Opposite Limits

namespace AlgebraicGeometry

namespace AlgSpecPoints

variable {R : CommRingCat.{u}}

/-- The affine charts `coverPt i` of a scheme over `Spec R` are open immersions. -/
theorem isOpenImmersion_coverPt {T : Over (Spec R)} (i : T.left.affineOpenCover.I₀) :
    IsOpenImmersion (coverPt i).left := by
  have : IsIso (coverIso i).hom.left := inferInstanceAs (IsIso ((Over.forget _).map _))
  change IsOpenImmersion ((coverIso i).hom.left ≫ T.left.affineOpenCover.f i)
  infer_instance

/-- The affine charts `coverPt i` of a scheme over `Spec R` cover it. -/
theorem exists_coverPt_apply_eq {T : Over (Spec R)} (x : T.left) :
    ∃ (i : T.left.affineOpenCover.I₀) (y : ((algSpec R).obj (op (coverAlg i))).left),
      (coverPt i).left y = x := by
  obtain ⟨y, hy⟩ := T.left.affineOpenCover.covers x
  have : IsIso (coverIso (T.left.affineOpenCover.idx x)).hom.left :=
    inferInstanceAs (IsIso ((Over.forget _).map _))
  refine ⟨T.left.affineOpenCover.idx x,
    (inv (coverIso (T.left.affineOpenCover.idx x)).hom.left) y, ?_⟩
  change ((coverIso _).hom.left ≫ T.left.affineOpenCover.f _) _ = x
  have hinv : (coverIso (T.left.affineOpenCover.idx x)).hom.left
      ((inv (coverIso (T.left.affineOpenCover.idx x)).hom.left) y) = y := by
    rw [← Scheme.Hom.comp_apply, IsIso.inv_hom_id]
    rfl
  rw [Scheme.Hom.comp_apply, hinv]
  exact hy

end AlgSpecPoints

namespace Grassmannian

open Scheme.Modules LocallyFreeQuotient AlgSpecPoints

variable {R : CommRingCat.{u}} {k n : ℕ}

/-- Quotients that are locally isomorphic on a jointly surjective family of open immersions are
isomorphic. -/
theorem equiv_of_openImmersion {S : Scheme.{u}} {ι : Type*} {X : ι → Scheme.{u}}
    (f : ∀ i, X i ⟶ S) [∀ i, IsOpenImmersion (f i)] (hf : ∀ x : S, ∃ (i : ι) (y : X i), f i y = x)
    {P P' : LocallyFreeQuotient S k n} (h : ∀ i, P.pullback (f i) ≈ P'.pullback (f i)) :
    P ≈ P' := by
  let e := fun i ↦ (h i).some
  obtain ⟨g, hg⟩ := exists_iso_of_openImmersion f hf P.π P'.π (fun i ↦ (e i).iso) fun i ↦ by
    have := (e i).comm
    rw [pullback_π, pullback_π, Category.assoc, cancel_epi] at this
    exact this
  exact ⟨⟨g, hg⟩⟩

variable [Module.Grassmannian.BaseChangeMkQFormula.{u, u, u} R (Fin n → R)]

/-- **A quotient is determined by its Grassmannian points.** -/
theorem toPointsNatTrans_injective (T : Over (Spec R)) :
    Function.Injective (toPointsNatTrans (k := k) (n := n) T) := by
  intro q q' h
  induction q using Quotient.inductionOn with | h P =>
  induction q' using Quotient.inductionOn with | h P' =>
  have : ∀ i, IsOpenImmersion (coverPt (T := T) i).left := isOpenImmersion_coverPt
  refine Quotient.sound (equiv_of_openImmersion (fun i ↦ (coverPt (T := T) i).left)
    exists_coverPt_apply_eq fun i ↦ ?_)
  have hi := congrArg (fun α ↦ α.app (coverAlg i) (coverPt i)) h
  exact (affinePoint_mk_eq_iff _ _ _).mp hi

end Grassmannian

end AlgebraicGeometry
