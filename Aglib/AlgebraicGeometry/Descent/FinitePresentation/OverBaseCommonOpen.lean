/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Descent.FinitePresentation.CommonOpen
public import Aglib.AlgebraicGeometry.Descent.FinitePresentation.OverBaseGluing

/-! # Common-open descent over the unchanged original base

The original schemes remain over their supplied base. The existing native
reassociation gives their sole initial models. After common-open descent,
the same stage reassociation returns maps to the actual original base
changes, retaining the complete original comparison equations.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

open CategoryTheory Limits

namespace AlgebraicGeometry.Scheme.OverBaseSpreading

universe u

open FinitePresentationDescent

variable {I : Type u} [Category.{u} I]
variable (D : I ⥤ Scheme.{u}) (c : Cone D) {B : Scheme.{u}}
variable (β : D ⟶ (Functor.const I).obj B) (α : c.pt ⟶ B)
variable (hα : ∀ k, c.π.app k ≫ β.app k = α) (i : I)

/-- The sole initial model supplied by native reassociation has exactly the
original comparison after its actual stage rebase. -/
theorem initialDescentModel_rebase_comparison
    {X : Scheme.{u}} (f : X ⟶ B)
    [LocallyOfFinitePresentation f] [QuasiCompact f] [QuasiSeparated f]
    (j : Over i) :
    let M := Model.ofOverIso (initialModel D β i f) (localRebase D c β α hα i f)
    (M.rebase D c i j).p ≫ (stageRebase D β i f j).hom.left =
      comparison D c β α hα i f j := by
  let M := Model.ofOverIso (initialModel D β i f) (localRebase D c β α hα i f)
  change (M.rebase D c i j).p ≫ (stageRebase D β i f j).hom.left = _
  apply pullback.hom_ext (f := f) (g := β.app j.left)
  · calc
      _ = ((M.rebase D c i j).p ≫
          pullback.fst (initialModel D β i f) (D.map j.hom)) ≫
          pullback.snd (β.app i) f := by
        exact (Category.assoc _ _ _).trans
          ((congrArg (fun q : pullback (initialModel D β i f) (D.map j.hom) ⟶ X =>
            (M.rebase D c i j).p ≫ q) (stageRebase_hom_fst D β i f j)).trans
              (Category.assoc _ _ _).symm)
      _ = M.p ≫ pullback.snd (β.app i) f := by
        have hp : (M.rebase D c i j).p ≫
            pullback.fst (initialModel D β i f) (D.map j.hom) = M.p :=
          Model.rebase_p_fst D c i M j
        exact congrArg (fun q : pullback f α ⟶ pullback (β.app i) f =>
          q ≫ pullback.snd (β.app i) f) hp
      _ = pullback.fst f α := by
        change ((localRebase D c β α hα i f).inv.left ≫
          pullback.fst (initialModel D β i f) (c.π.app i)) ≫
            pullback.snd (β.app i) f = _
        exact (Category.assoc _ _ _).trans (localRebase_inv_fst D c β α hα i f)
      _ = comparison D c β α hα i f j ≫ pullback.fst f (β.app j.left) :=
        (comparison_fst D c β α hα i f j).symm
  · have hj : (stageRebase D β i f j).hom.left ≫ pullback.snd f (β.app j.left) =
        pullback.snd (initialModel D β i f) (D.map j.hom) :=
      Over.w (stageRebase D β i f j).hom
    calc
      _ = (M.rebase D c i j).p ≫ pullback.snd (initialModel D β i f) (D.map j.hom) := by
        exact (Category.assoc _ _ _).trans
          (congrArg (fun q : pullback (initialModel D β i f) (D.map j.hom) ⟶ D.obj j.left =>
            (M.rebase D c i j).p ≫ q) hj)
      _ = pullback.snd f α ≫ c.π.app j.left := Model.rebase_p_snd D c i M j
      _ = comparison D c β α hα i f j ≫ pullback.snd f (β.app j.left) :=
        (comparison_snd D c β α hα i f j).symm

/-- A common quasi-compact open in the original limit base changes descends
over the unchanged base. Both resulting open maps preserve the original
comparison, not just an abstract isomorphism class. -/
theorem exists_common_open_with_comparison [IsCofiltered I]
    [∀ {j k} (q : j ⟶ k), IsAffineHom (D.map q)]
    [∀ j, CompactSpace (D.obj j)] [∀ j, QuasiSeparatedSpace (D.obj j)]
    (hc : IsLimit c) (X : Bool → Scheme.{u}) (f : ∀ b, X b ⟶ B)
    [∀ b, LocallyOfFinitePresentation (f b)] [∀ b, QuasiCompact (f b)]
    [∀ b, QuasiSeparated (f b)]
    {W : Scheme.{u}} [CompactSpace W] (w : W ⟶ c.pt)
    (m : ∀ b, Over.mk w ⟶ (Over.pullback α).obj (Over.mk (f b)))
    [∀ b, IsOpenImmersion (m b).left] :
    ∃ j : Over i, ∃ N : Model (c.π.app j.left) w,
      ∀ b, ∃ a : Over.mk N.f ⟶ (Over.pullback (β.app j.left)).obj (Over.mk (f b)),
        IsOpenImmersion a.left ∧
        N.p ≫ a.left = (m b).left ≫ comparison D c β α hα i (f b) j := by
  let Z (b : Bool) := pullback (f b) α
  let t (b : Bool) : Z b ⟶ c.pt := pullback.snd (f b) α
  let M (b : Bool) : Model (c.π.app i) (t b) :=
    Model.ofOverIso (initialModel D β i (f b)) (localRebase D c β α hα i (f b))
  obtain ⟨j, N, hN⟩ := Model.exists_common_open_model D c hc i Z t M w m
  refine ⟨j, N, fun b => ?_⟩
  obtain ⟨a, ha⟩ := hN b
  let result : Over.mk N.f ⟶ (Over.pullback (β.app j.left)).obj (Over.mk (f b)) :=
    a.hom ≫ (stageRebase D β i (f b) j).hom
  refine ⟨result, ?_, ?_⟩
  · change IsOpenImmersion (a.hom.left ≫ (stageRebase D β i (f b) j).hom.left)
    have : IsOpenImmersion a.hom.left := ha
    infer_instance
  · have hcomp : ((M b).rebase D c i j).p ≫
        (stageRebase D β i (f b) j).hom.left = comparison D c β α hα i (f b) j :=
      initialDescentModel_rebase_comparison D c β α hα i (f b) j
    change N.p ≫ (a.hom.left ≫ (stageRebase D β i (f b) j).hom.left) = _
    rw [← Category.assoc, a.comm, Category.assoc, hcomp]

end AlgebraicGeometry.Scheme.OverBaseSpreading
