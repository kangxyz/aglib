/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Morphisms.FiniteEtale.Descent.LimitLifting
public import Aglib.AlgebraicGeometry.Morphisms.FiniteEtale.BaseChange.LiftAlongSquare
public import Mathlib.AlgebraicGeometry.AffineTransitionLimit
public import Mathlib.CategoryTheory.Comma.Over.Pullback

/-!
# Finite-etale lifting through an inverse system over a fixed base

Native over-category limits identify the original base change with the limit
of the stage base changes. Stage essential surjectivity then supplies actual
cover lifts. This is a conditional reduction, not a proper approximation theorem.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Scheme.FiniteEtale.LimitDescent

universe u

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

attribute [local instance] IsCofiltered.isConnected

/-- Essential surjectivity at every stage of an actual fixed-base inverse
system implies essential surjectivity for its original base-change functor. -/
theorem baseChange_essSurj_of_fixedBaseLimit
    {I : Type u} [Category.{u} I] [IsCofiltered I]
    (D : I ⥤ Scheme.{u})
    [∀ {s t} (g : s ⟶ t), IsAffineHom (D.map g)]
    {S T : Scheme.{u}} (b : T ⟶ S)
    (a : D ⟶ (Functor.const I).obj S)
    (c : Cone D) (hc : IsLimit c) (p : c.pt ⟶ S)
    (hp : ∀ s, c.π.app s ≫ a.app s = p)
    [∀ s, CompactSpace (pullback (a.app s) b : Scheme.{u})]
    [∀ s, QuasiSeparatedSpace (pullback (a.app s) b : Scheme.{u})]
    (h : ∀ s, (baseChange (pullback.fst (a.app s) b)).EssSurj) :
    (baseChange (pullback.fst p b)).EssSurj := by
  let F := Over.pullback b ⋙ Over.forget T
  let E := Over.lift D a ⋙ F
  let d : Cone E := F.mapCone (Over.liftCone D a c p hp)
  have hd : IsLimit d :=
    isLimitOfPreserves F (Over.isLimitLiftCone D a c p hp hc)
  have {s t : I} (g : s ⟶ t) : IsAffineHom (E.map g) := by
    apply MorphismProperty.overPullbackMap (P := @IsAffineHom) b
      ((Over.lift D a).map g)
    exact inferInstanceAs (IsAffineHom (D.map g))
  have (s : I) : CompactSpace (E.obj s) :=
    inferInstanceAs (CompactSpace (pullback (a.app s) b : Scheme.{u}))
  have (s : I) : QuasiSeparatedSpace (E.obj s) :=
    inferInstanceAs (QuasiSeparatedSpace (pullback (a.app s) b : Scheme.{u}))
  apply baseChange_essSurj_of_stage_lifts E d hd
    (i := pullback.fst p b) (Iso.refl _)
  intro s C
  change FiniteEtale (pullback (a.app s) b) at C
  let : (baseChange (pullback.fst (a.app s) b)).EssSurj := h s
  have w : pullback.fst p b ≫ c.π.app s =
      d.π.app s ≫ pullback.fst (a.app s) b := by
    change pullback.fst p b ≫ c.π.app s =
      pullback.lift _ _ _ ≫ pullback.fst (a.app s) b
    rw [pullback.lift_fst]
    rfl
  dsimp only [Iso.refl_hom]
  rw [Category.id_comp]
  exact exists_cover_pullback_of_square (c.π.app s) (pullback.fst p b)
      (pullback.fst (a.app s) b) (d.π.app s) w C

end AlgebraicGeometry.Scheme.FiniteEtale.LimitDescent
