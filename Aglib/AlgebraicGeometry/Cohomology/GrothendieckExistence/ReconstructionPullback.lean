/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Modules.Coherent.AdicSystem.Completion
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Limits

/-!
# The original sheaf pullback for bounded reconstruction

This is a construction in ordinary module sheaves, not in a hypothetical
abelian category of adic systems. Its universal property retains the actual
maps to every formal stage and the original algebraic target. Coherence of
the pullback is a further local theorem, not an assumption or assertion here.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry.Scheme.Modules.Coherent

variable {X : Scheme.{u}} [IsLocallyNoetherian X] (J : X.IdealSheafData)

/-- The original quotient units, assembled into the inverse-limit sheaf.
The limit is not asserted to be quasicoherent. -/
def completionLimitUnit (H : X.CoherentSheaf) :
    H.obj ⟶ limit ((completionFunctor X J).obj H).obj :=
  limit.lift _ ⟨H.obj, idealSheafQuotientTowerUnit X J H.obj⟩

@[reassoc]
theorem completionLimitUnit_π (H : X.CoherentSheaf) (n : ℕᵒᵖ) :
    completionLimitUnit J H ≫ limit.π ((completionFunctor X J).obj H).obj n =
      (idealSheafQuotientUnit X (J ^ n.unop)).app H.obj := by
  apply limit.lift_π

variable {J} {F : AdicSystem X J} {H : X.CoherentSheaf}
  (α : F ⟶ (completionFunctor X J).obj H)

/-- The canonical candidate before proving coherence: the ordinary sheaf
pullback of the original formal map and the original completion unit. -/
abbrev reconstructionPullback : X.Modules :=
  Limits.pullback (limMap α.hom) (completionLimitUnit J H)

/-- The original algebraic projection of the canonical candidate. -/
abbrev reconstructionToTarget : reconstructionPullback α ⟶ H.obj :=
  Limits.pullback.snd _ _

/-- The original formal projection at a finite stage. -/
def reconstructionToStage (n : ℕᵒᵖ) : reconstructionPullback α ⟶ F.obj.obj n :=
  Limits.pullback.fst _ _ ≫ limit.π F.obj n

@[reassoc]
theorem reconstructionToStage_naturality {m n : ℕᵒᵖ} (f : m ⟶ n) :
    reconstructionToStage α m ≫ F.obj.map f = reconstructionToStage α n := by
  simp only [reconstructionToStage, Category.assoc, limit.w]

/-- The defining square uses the original quotient unit at every stage. -/
@[reassoc]
theorem reconstructionToStage_comp (n : ℕᵒᵖ) :
    reconstructionToStage α n ≫ α.hom.app n =
      reconstructionToTarget α ≫
        (idealSheafQuotientUnit X (J ^ n.unop)).app H.obj := by
  dsimp only [reconstructionToStage, reconstructionToTarget]
  rw [Category.assoc, ← limMap_π, ← Category.assoc, Limits.pullback.condition,
    Category.assoc, completionLimitUnit_π]

/-- Maps to the candidate are determined by their algebraic projection and
all their original finite-stage formal projections. -/
theorem reconstructionPullback_hom_ext {M : X.Modules}
    {f g : M ⟶ reconstructionPullback α}
    (htarget : f ≫ reconstructionToTarget α = g ≫ reconstructionToTarget α)
    (hstage : ∀ n, f ≫ reconstructionToStage α n = g ≫ reconstructionToStage α n) :
    f = g := by
  apply Limits.pullback.hom_ext
  · apply limit.hom_ext
    intro n
    simpa only [reconstructionToStage, Category.assoc] using hstage n
  · exact htarget

/-- A compatible family with the original quotient-unit square induces a
unique map into the canonical candidate. -/
def reconstructionLift {M : X.Modules} (a : M ⟶ H.obj)
    (b : (Functor.const ℕᵒᵖ).obj M ⟶ F.obj)
    (h : ∀ n, b.app n ≫ α.hom.app n =
      a ≫ (idealSheafQuotientUnit X (J ^ n.unop)).app H.obj) :
    M ⟶ reconstructionPullback α :=
  Limits.pullback.lift (limit.lift F.obj ⟨M, b⟩) a (by
    apply limit.hom_ext
    intro n
    rw [Category.assoc, limMap_π, ← Category.assoc, limit.lift_π,
      Category.assoc, completionLimitUnit_π]
    exact h n)

@[reassoc (attr := simp)]
theorem reconstructionLift_toTarget {M : X.Modules} (a : M ⟶ H.obj)
    (b : (Functor.const ℕᵒᵖ).obj M ⟶ F.obj)
    (h : ∀ n, b.app n ≫ α.hom.app n =
      a ≫ (idealSheafQuotientUnit X (J ^ n.unop)).app H.obj) :
    reconstructionLift α a b h ≫ reconstructionToTarget α = a := by
  apply Limits.pullback.lift_snd

@[reassoc (attr := simp)]
theorem reconstructionLift_toStage {M : X.Modules} (a : M ⟶ H.obj)
    (b : (Functor.const ℕᵒᵖ).obj M ⟶ F.obj)
    (h : ∀ n, b.app n ≫ α.hom.app n =
      a ≫ (idealSheafQuotientUnit X (J ^ n.unop)).app H.obj) (n : ℕᵒᵖ) :
    reconstructionLift α a b h ≫ reconstructionToStage α n = b.app n := by
  simp [reconstructionLift, reconstructionToStage]

end AlgebraicGeometry.Scheme.Modules.Coherent
