/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Cohomology.GrothendieckExistence.ReconstructionPullback
public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Pullbacks

/-! # Original reconstruction lifts after a limit-preserving functor

The functor is kept abstract while the inverse-limit and pullback equations
are proved. Open restriction is an eventual specialization. No quasicoherence
is imposed on the original reconstruction pullback or inverse limit.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.Scheme.Modules.Coherent

universe u
variable {X Y : Scheme.{u}} [IsLocallyNoetherian X]
  {K : X.IdealSheafData} {F : AdicSystem X K} {H : X.CoherentSheaf}
  (T : X.Modules ⥤ Y.Modules) [PreservesLimitsOfShape ℕᵒᵖ T]
  [PreservesLimitsOfShape WalkingCospan T]
  (α : F ⟶ (completionFunctor X K).obj H)
  {M : Y.Modules} (a : M ⟶ T.obj H.obj)
  (b : (Functor.const ℕᵒᵖ).obj M ⟶ F.obj ⋙ T)
  (h : ∀ n, b.app n ≫ T.map (α.hom.app n) =
    a ≫ T.map ((idealSheafQuotientUnit X (K ^ n.unop)).app H.obj))

/-- The original compatible formal-stage maps into the mapped inverse limit. -/
def reconstructionMappedFormalLift : M ⟶ T.obj (limit F.obj) :=
  limit.lift _ ⟨M, b⟩ ≫ (preservesLimitIso T F.obj).inv

omit [PreservesLimitsOfShape WalkingCospan T] in
@[reassoc (attr := simp)]
theorem reconstructionMappedFormalLift_π (n : ℕᵒᵖ) :
    reconstructionMappedFormalLift T b ≫ T.map (limit.π F.obj n) = b.app n := by
  simp [reconstructionMappedFormalLift, Category.assoc]

include h in
omit [PreservesLimitsOfShape WalkingCospan T] in
/-- The square after mapping still uses the original completion unit. -/
theorem reconstructionMappedFormalLift_square :
    reconstructionMappedFormalLift T b ≫ T.map (limMap α.hom) =
      a ≫ T.map (completionLimitUnit K H) := by
  apply (isLimitOfPreserves T (limit.isLimit ((completionFunctor X K).obj H).obj)).hom_ext
  intro n
  change (reconstructionMappedFormalLift T b ≫ T.map (limMap α.hom)) ≫
      T.map (limit.π ((completionFunctor X K).obj H).obj n) =
    (a ≫ T.map (completionLimitUnit K H)) ≫
      T.map (limit.π ((completionFunctor X K).obj H).obj n)
  rw [Category.assoc, ← T.map_comp, limMap_π, T.map_comp,
    ← Category.assoc, reconstructionMappedFormalLift_π,
    Category.assoc, ← T.map_comp, completionLimitUnit_π]
  exact h n

/-- The unique original mapped reconstruction lift. -/
def reconstructionMappedLift : M ⟶ T.obj (reconstructionPullback α) :=
  pullback.lift (reconstructionMappedFormalLift T b) a
    (reconstructionMappedFormalLift_square T α a b h) ≫
      (PreservesPullback.iso T (limMap α.hom) (completionLimitUnit K H)).inv

@[reassoc (attr := simp)]
theorem reconstructionMappedLift_toTarget :
    reconstructionMappedLift T α a b h ≫ T.map (reconstructionToTarget α) = a := by
  dsimp only [reconstructionMappedLift, reconstructionToTarget]
  rw [Category.assoc, PreservesPullback.iso_inv_snd, pullback.lift_snd]

@[reassoc (attr := simp)]
theorem reconstructionMappedLift_toStage (n : ℕᵒᵖ) :
    reconstructionMappedLift T α a b h ≫ T.map (reconstructionToStage α n) =
      b.app n := by
  dsimp only [reconstructionMappedLift, reconstructionToStage]
  rw [Functor.map_comp, Category.assoc, ← Category.assoc
    (PreservesPullback.iso T (limMap α.hom) (completionLimitUnit K H)).inv,
    PreservesPullback.iso_inv_fst, ← Category.assoc, pullback.lift_fst,
    reconstructionMappedFormalLift_π]

end AlgebraicGeometry.Scheme.Modules.Coherent
