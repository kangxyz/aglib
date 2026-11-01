/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.Exceptional.Unbounded.Densification
public import Aglib.AlgebraicGeometry.EtaleCohomology.Exceptional.Unbounded.RawTransitionCoherence
public import Aglib.AlgebraicGeometry.Compactification.Refinements.OpenSquare

/-!
# Naturality of the original closed-densification comparison

The two paths consist of the same original raw refinement transitions. Their
ambient composites agree by the actual schematic-image factorization equation;
original comparison composition then proves the square, without replacing maps
by objectwise isomorphisms.
-/

@[expose] public noncomputable section

open CategoryTheory Limits

namespace AlgebraicGeometry.Scheme.EtaleCohomology

open Coefficients

universe u wX wS wC wD wCN wDN

variable {X S : Scheme.{u}} {f : X ⟶ S} [QuasiCompact f]
  (C D : Hom.Compactification f) [QuasiCompact C.j] [QuasiCompact D.j]
  (h : C.Xbar ⟶ D.Xbar) (ho : C.j ≫ h = D.j)
  (sq : IsPullback C.j (𝟙 X) h D.j) (hp : h ≫ D.p = C.p)
  (Λ : Type (u + 1)) [Ring Λ]
  [HasDerivedCategory.{wX} (ModuleSheaf X Λ)]
  [HasDerivedCategory.{wS} (ModuleSheaf S Λ)]
  [HasDerivedCategory.{wC} (ModuleSheaf C.Xbar Λ)]
  [HasDerivedCategory.{wD} (ModuleSheaf D.Xbar Λ)]
  [HasDerivedCategory.{wCN} (ModuleSheaf (Hom.Compactification.densify C).Xbar Λ)]
  [HasDerivedCategory.{wDN} (ModuleSheaf (Hom.Compactification.densify D).Xbar Λ)]

/-- The actual closed-densification maps intertwine the original raw transition
and the transition of the actual schematic-image lift. -/
theorem moduleUnboundedCompactificationDensificationMap_naturality :
    moduleUnboundedRawCompactificationTransition C D h sq hp Λ ≫
      moduleUnboundedCompactificationDensificationMap C Λ =
    moduleUnboundedCompactificationDensificationMap D Λ ≫
      moduleUnboundedRawCompactificationTransition
        (Hom.Compactification.densify C).toCompactification
        (Hom.Compactification.densify D).toCompactification
        (Hom.Compactification.densifyRefinement C D h ho hp).hom
        (Hom.DenseCompactification.isPullback_open
          (Hom.Compactification.densifyRefinement C D h ho hp))
        (Hom.Compactification.densifyRefinement C D h ho hp).base_fac Λ := by
  let n := Hom.Compactification.densifyRefinement C D h ho hp
  have sq₁ : IsPullback (Hom.Compactification.densify C).j (𝟙 X)
      (Hom.Compactification.densifyι C ≫ h) D.j := by
    simpa only [Category.id_comp] using
      ((Hom.Compactification.isPullback_densify C).paste_vert sq)
  have sq₂ : IsPullback (Hom.Compactification.densify C).j (𝟙 X)
      (n.hom ≫ Hom.Compactification.densifyι D) D.j := by
    simpa only [Category.id_comp] using
      ((Hom.DenseCompactification.isPullback_open n).paste_vert
        (Hom.Compactification.isPullback_densify D))
  have hp₁ : (Hom.Compactification.densifyι C ≫ h) ≫ D.p =
      (Hom.Compactification.densify C).p := by
    rw [Category.assoc, hp, Hom.Compactification.densifyι_p]
  have hp₂ : (n.hom ≫ Hom.Compactification.densifyι D) ≫ D.p =
      (Hom.Compactification.densify C).p := by
    rw [Category.assoc, Hom.Compactification.densifyι_p, n.base_fac]
  have h₁ := moduleUnboundedRawCompactificationTransition_comp
    (Hom.Compactification.densify C).toCompactification C
    (Hom.Compactification.densifyι C) (Hom.Compactification.isPullback_densify C)
    (Hom.Compactification.densifyι_p C) Λ D h sq hp sq₁ hp₁
  have h₂ := moduleUnboundedRawCompactificationTransition_comp
    (Hom.Compactification.densify C).toCompactification
    (Hom.Compactification.densify D).toCompactification
    n.hom (Hom.DenseCompactification.isPullback_open n) n.base_fac Λ D
    (Hom.Compactification.densifyι D) (Hom.Compactification.isPullback_densify D)
    (Hom.Compactification.densifyι_p D) sq₂ hp₂
  change moduleUnboundedRawCompactificationTransition C D h sq hp Λ ≫
      moduleUnboundedRawCompactificationTransition _ _ _ _ _ Λ =
    moduleUnboundedRawCompactificationTransition _ _ _ _ _ Λ ≫
      moduleUnboundedRawCompactificationTransition _ _ _ _ _ Λ
  rw [← h₁, ← h₂]
  have hn : n.hom ≫ Hom.Compactification.densifyι D =
      Hom.Compactification.densifyι C ≫ h :=
    Hom.Compactification.densifyMap_ι C D h ho
  congr 1
  exact hn.symm

end AlgebraicGeometry.Scheme.EtaleCohomology
