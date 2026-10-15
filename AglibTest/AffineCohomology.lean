/-
Copyright (c) 2026 Algebraic geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Aglib.AlgebraicGeometry.Cohomology.Affine.Vanishing

/-! The actual derived section functor and an actual injective resolution over an
arbitrary affine scheme. The quasicoherence premise remains explicit. -/

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open AlgebraicGeometry.Scheme.Modules

universe u

example {R : CommRingCat.{u}} (M : (Spec R).Modules) [M.IsQuasicoherent] (n : ℕ) :
    IsZero ((moduleSpecΓFunctor.rightDerived (n + 1)).obj M) :=
  AffineDerived.isZero_rightDerived_globalSections_succ M n

example {R : CommRingCat.{u}} (M : (Spec R).Modules) [M.IsQuasicoherent]
    (I : CategoryTheory.InjectiveResolution M) (n : ℕ) :
    ((moduleSpecΓFunctor.mapHomologicalComplex _).obj I.cocomplex).ExactAt (n + 1) :=
  AffineDerived.globalSections_injectiveResolution_exact_succ M I n
