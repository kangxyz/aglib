/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Cohomology.Duality.Projective.Relative.Comparison
public import Aglib.AlgebraicGeometry.Cohomology.Duality.Projective.Relative.CoverSequence
public import Aglib.AlgebraicGeometry.Cohomology.Duality.Projective.Relative.Coherent.BiproductCore

/-!
# Finite biproduct closure of the original Serre comparison

The original coefficient naturality square identifies the components under
the native Ext and derived-Hom biproduct comparisons.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian
open AlgebraicGeometry AlgebraicGeometry.ProjectiveSpace AlgebraicGeometry.Scheme.Modules

universe u
attribute [local instance] AlgebraicGeometry.Scheme.Modules.standardHasDerivedCategory
attribute [local instance] CategoryTheory.Abelian.hasFiniteBiproducts

namespace AlgebraicGeometry.Scheme.Cohomology

variable (R : Type u) [CommRing R] (ι : Type u)
  {X Y : Scheme.{u}} (a : X ⟶ ProjectiveSpace R ι) (p : X ⟶ Y)
  (f : Y ⟶ Spec (.of R)) (h : IsPullback a p (toSpec R ι) f)
  [Y.IsSeparated]

/-- Bijectivity on each original coefficient gives bijectivity on its finite biproduct. -/
theorem relativeProjectiveSerreMap_biproduct_bijective
    (n : ℕ) (e : ι ≃ Fin (n + 1)) {J : Type u} [Finite J]
    (N : J → Y.Modules) [∀ j, (N j).IsQuasicoherent]
    [(biproduct N).IsQuasicoherent] (M : X.Modules) (q : ℕ)
    (hN : ∀ j, Function.Bijective (relativeProjectiveSerreMap R ι a p f h n e (N j) M q)) :
    Function.Bijective (relativeProjectiveSerreMap R ι a p f h n e (biproduct N) M q) := by
  classical
  let W := relativeTopDifferentialCoefficientsFunctor p n
  let G := DerivedCategory.singleFunctor Y.Modules (n : ℤ) ⋙
    shiftFunctor (DerivedCategory Y.Modules) (q : ℤ)
  apply Ext.bijective_comparison_biproduct W G N M
    ((Scheme.Modules.derivedPushforwardPlus p ⋙ DerivedCategory.Plus.ι).obj
      ((DerivedCategory.Plus.singleFunctor X.Modules 0).obj M)) q
    (relativeProjectiveSerreMap R ι a p f h n e (biproduct N) M q)
    (fun j => relativeProjectiveSerreMap R ι a p f h n e (N j) M q) ?_ hN
  intro j x
  exact relativeProjectiveSerreMap_naturality_coefficients R ι a p f h n e
    (biproduct.π N j) M q x

end AlgebraicGeometry.Scheme.Cohomology
