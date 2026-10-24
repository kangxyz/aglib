/-
Copyright (c) 2026 Algebraic geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Grassmannian.LocallyFree.Chart
public import Aglib.AlgebraicGeometry.Grassmannian.Quotient.Reindex

/-!
# Trivializing affine charts of a finite locally free sheaf of constant rank

If `E` is finite locally free of constant rank `n` (`Scheme.Modules.SheafHasRank E n`), every
point of `S` lies in the image of a trivializing affine chart `j : Spec R ⟶ S`, `j^* E ≅ O^n`
(`exists_trivializingChart`); `TrivializingChart.chartAt h x` is a choice of one at `x`.

The chart is built from the local basis of `SheafHasRank` on an open `U ∋ x`, given in Mathlib's
over-site form `free I ≅ E.over U`; `Scheme.Modules.restrictFreeIsoOfOverFreeIso` turns it into
`free I ≅ E.restrict U.ι` on the open subscheme `U` (Mathlib's `Scheme.Modules.overEquiv` and
`overFunctorEquiv`; the inverse direction of Aglib's `freeIsoOverOfRestrictFreeIso`). The basis
is reindexed to `ULift (Fin n)` (`freeReindexIso`), and the trivialization is pulled back to a
member `Spec R ⟶ U` of Mathlib's `affineOpenCover` of `U` (`TrivializingChart.ofOpen`).
-/

@[expose] public section

noncomputable section

set_option backward.isDefEq.respectTransparency false

universe u

open CategoryTheory Opposite Limits

namespace AlgebraicGeometry.Scheme.Modules

/-- A free presentation of the over-site restriction `E.over U` gives a free presentation of the
restriction `E.restrict U.ι` to the open subscheme `U` (the inverse direction of
`freeIsoOverOfRestrictFreeIso`). -/
def restrictFreeIsoOfOverFreeIso {X : Scheme.{u}} {I : Type u} {M : X.Modules} (U : X.Opens)
    (e : SheafOfModules.free (R := X.ringCatSheaf.over U) I ≅ M.over U) :
    SheafOfModules.free (R := U.toScheme.ringCatSheaf) I ≅ M.restrict U.ι :=
  let F := (Scheme.Modules.overEquiv U).functor
  let η : SheafOfModules.unit U.toScheme.ringCatSheaf ≅
      F.obj (SheafOfModules.unit (X.ringCatSheaf.over U)) :=
    (U.sheafOfModulesEquivOverUnit X.ringCatSheaf).symm
  SheafOfModules.mapFreeIso F I η ≪≫ F.mapIso e ≪≫ (Scheme.Modules.overFunctorEquiv U).app M

end AlgebraicGeometry.Scheme.Modules

namespace AlgebraicGeometry.Grassmannian

open Scheme.Modules

variable {S : Scheme.{u}} {E : S.Modules} {n : ℕ}

/-- The trivializing chart given by an open `U` with `O_U^n ≅ E|_U` and a member of Mathlib's
affine open cover of `U`. -/
def TrivializingChart.ofOpen (U : S.Opens) (e : freeSheaf U n ≅ E.restrict U.ι)
    (a : U.toScheme.affineOpenCover.I₀) : TrivializingChart E n where
  R := U.toScheme.affineOpenCover.X a
  j := U.toScheme.affineOpenCover.f a ≫ U.ι
  isOpenImmersion := inferInstance
  φ := ((pullbackTriangleIso (U.toScheme.affineOpenCover.f a) U.ι _ rfl).app E).symm ≪≫
    (Scheme.Modules.pullback (U.toScheme.affineOpenCover.f a)).mapIso
      (((restrictFunctorIsoPullback U.ι).app E).symm ≪≫ e.symm) ≪≫
    pullbackFreeIso (U.toScheme.affineOpenCover.f a) (ULift.{u} (Fin n))

/-- **Trivializing affine charts cover `S`**: if `E` is finite locally free of constant rank `n`,
every point of `S` lies in the image of a trivializing affine chart. -/
theorem exists_trivializingChart (h : SheafHasRank E n) (x : S) :
    ∃ c : TrivializingChart E n, x ∈ Set.range c.j := by
  obtain ⟨q, hq, hn⟩ := h
  obtain ⟨i, hi⟩ := ((_root_.Opens.coversTop_iff S q.X).mp q.coversTop).exists_mem x
  let U : S.Opens := q.X i
  let G := q.generators i
  have : IsIso G.π := hq.isIso i
  let e₂ : SheafOfModules.free (R := U.toScheme.ringCatSheaf) G.I ≅ E.restrict U.ι :=
    restrictFreeIsoOfOverFreeIso U (asIso G.π)
  let e₃ : freeSheaf U n ≅ E.restrict U.ι :=
    freeReindexIso U.toScheme (Equiv.ulift.trans (hn i).some.symm) ≪≫ e₂
  let y : U.toScheme := ⟨x, hi⟩
  obtain ⟨z, hz⟩ := U.toScheme.affineOpenCover.covers y
  refine ⟨TrivializingChart.ofOpen U e₃ (U.toScheme.affineOpenCover.idx y), z, ?_⟩
  change (U.toScheme.affineOpenCover.f (U.toScheme.affineOpenCover.idx y) ≫ U.ι) z = x
  rw [Scheme.Hom.comp_apply, hz]
  rfl

/-- A choice of a trivializing affine chart at a point. -/
def TrivializingChart.chartAt (h : SheafHasRank E n) (x : S) : TrivializingChart E n :=
  (exists_trivializingChart h x).choose

theorem TrivializingChart.mem_range_chartAt (h : SheafHasRank E n) (x : S) :
    x ∈ Set.range (TrivializingChart.chartAt h x).j :=
  (exists_trivializingChart h x).choose_spec

end AlgebraicGeometry.Grassmannian
