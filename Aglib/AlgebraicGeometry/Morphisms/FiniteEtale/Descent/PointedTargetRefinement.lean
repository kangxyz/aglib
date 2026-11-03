/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Morphisms.FiniteEtale.Descent.LimitObjects
public import Mathlib.AlgebraicGeometry.Morphisms.Etale

/-! # Actual pointed target refinements descended from a limit cover

A finite-etale cover of a qcqs affine-transition limit descends by the existing
object theorem. Its original reconstruction transports the specified point,
without descending the point as a finitely presented morphism. When the stage
maps to the original target are etale, the descended cover gives a genuine
etale refinement of that same target with the original point triangle.

This geometric producer does not assert that a class is zero on the whole
limit cover. Generic-open zero cannot be substituted for such a hypothesis.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Scheme.FiniteEtale.LimitDescent

universe u

/-- Descent of the actual cover retains its cartesian reconstruction and the
original marked-source triangle. In particular the mark can be an arbitrary
geometric point, without a closed-point or finite-residue-field assumption. -/
theorem exists_pointed_target_etale_refinement_of_limit_cover
    {I : Type u} [Category.{u} I] [IsCofiltered I] {X P : Scheme.{u}}
    (D : I ⥤ Over X) (c : Cone D)
    (hc : IsLimit ((Over.forget X).mapCone c))
    [∀ {i j} (f : i ⟶ j), IsAffineHom (D.map f).left]
    [∀ i, CompactSpace (D.obj i).left] [∀ i, QuasiSeparatedSpace (D.obj i).left]
    [∀ i, Etale (D.obj i).hom]
    (Y : FiniteEtale c.pt.left) (y : P ⟶ Y.obj.left) (x : P ⟶ X)
    (hy : y ≫ Y.obj.hom ≫ c.pt.hom = x) :
    ∃ (i : I) (Yi : FiniteEtale (D.obj i).left)
      (e : (baseChange (c.π.app i).left).obj Yi ≅ Y)
      (a : Y.obj.left ⟶ Yi.obj.left),
      a = e.inv.hom.left ≫ pullback.fst Yi.obj.hom (c.π.app i).left ∧
      IsPullback a Y.obj.hom Yi.obj.hom (c.π.app i).left ∧
      a ≫ Yi.obj.hom ≫ (D.obj i).hom = Y.obj.hom ≫ c.pt.hom ∧
      Etale (Yi.obj.hom ≫ (D.obj i).hom) ∧
      ∃ yi : P ⟶ Yi.obj.left, yi = y ≫ a ∧
        yi ≫ Yi.obj.hom ≫ (D.obj i).hom = x := by
  let E := D ⋙ Over.forget X
  let d := (Over.forget X).mapCone c
  let : ∀ i, CompactSpace (E.obj i) := fun i =>
    inferInstanceAs (CompactSpace (D.obj i).left)
  let : ∀ i, QuasiSeparatedSpace (E.obj i) := fun i =>
    inferInstanceAs (QuasiSeparatedSpace (D.obj i).left)
  let : ∀ {i j} (f : i ⟶ j), IsAffineHom (E.map f) := fun {_ _} f =>
    inferInstanceAs (IsAffineHom (D.map f).left)
  obtain ⟨i, Yi, ⟨e⟩⟩ := exists_cover_of_isLimit E d hc Y
  change (baseChange (c.π.app i).left).obj Yi ≅ Y at e
  let a := e.inv.hom.left ≫ pullback.fst Yi.obj.hom (c.π.app i).left
  have he : e.inv.hom.left ≫ pullback.snd Yi.obj.hom (c.π.app i).left =
      Y.obj.hom := Over.w e.inv.hom
  have ha : a ≫ Yi.obj.hom = Y.obj.hom ≫ (c.π.app i).left := by
    dsimp only [a]
    exact (Category.assoc e.inv.hom.left
      (pullback.fst Yi.obj.hom (c.π.app i).left) Yi.obj.hom).trans
      ((congrArg (fun z => e.inv.hom.left ≫ z)
        (pullback.condition (f := Yi.obj.hom) (g := (c.π.app i).left))).trans
        ((Category.assoc e.inv.hom.left
          (pullback.snd Yi.obj.hom (c.π.app i).left) (c.π.app i).left).symm.trans
          (congrArg (fun z => z ≫ (c.π.app i).left) he)))
  have H : IsPullback a Y.obj.hom Yi.obj.hom (c.π.app i).left := by
    exact IsPullback.of_iso_pullback ⟨ha⟩
      ((forgetToScheme c.pt.left).mapIso e.symm) rfl he
  have hover : a ≫ Yi.obj.hom ≫ (D.obj i).hom = Y.obj.hom ≫ c.pt.hom := by
    rw [← Category.assoc, ha, Category.assoc, Over.w]
    rfl
  refine ⟨i, Yi, e, a, rfl, H, hover, inferInstance, y ≫ a, rfl, ?_⟩
  rw [Category.assoc, hover]
  exact hy

end AlgebraicGeometry.Scheme.FiniteEtale.LimitDescent
