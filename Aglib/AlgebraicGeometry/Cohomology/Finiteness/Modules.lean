/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Cohomology.Exact.Modules
public import Aglib.RingTheory.Finiteness.Exact

/-!
# Finite generation along original module-sheaf cohomology sequences

Over a Noetherian structural ring, the original long exact sequence transfers
finite generation to its middle term. The quotient transfer uses finite
middle cohomology in degree `n` and finite kernel cohomology in degree `n+1`;
it is the descending-induction step for projective coherent finiteness.
All groups and linear maps are the existing actual cohomology objects.
Neither properness nor a cohomological finiteness family is assumed here.
-/

@[expose] public section

noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Abelian CategoryTheory.Limits
open AlgebraicGeometry TopologicalSpace Opposite

namespace AlgebraicGeometry.Scheme.Cohomology

universe u

variable (X : Scheme.{u}) {R : Type u} [CommRing R] [IsNoetherianRing R]
    (α : R →+* Γ(X, ⊤))

/-- Finite outer cohomology modules give finite middle cohomology. -/
theorem moduleCohomology_finite_middle_of_hom (S : ShortComplex X.Modules)
    (hS : S.ShortExact) (n : ℕ)
    (h₁ : letI := moduleCohomologyModuleOfHom X α S.X₁ n
      Module.Finite R (Sheaf.H.{u + 1} (moduleAddSheaf X S.X₁) n))
    (h₃ : letI := moduleCohomologyModuleOfHom X α S.X₃ n
      Module.Finite R (Sheaf.H.{u + 1} (moduleAddSheaf X S.X₃) n)) :
    letI := moduleCohomologyModuleOfHom X α S.X₂ n
    Module.Finite R (Sheaf.H.{u + 1} (moduleAddSheaf X S.X₂) n) := by
  let := moduleCohomologyModuleOfHom X α S.X₁ n
  let := moduleCohomologyModuleOfHom X α S.X₂ n
  let := moduleCohomologyModuleOfHom X α S.X₃ n
  let := h₁
  let := h₃
  exact Module.Finite.of_exact_of_isNoetherian _ _
    (moduleCohomologyMapOfHom_exact X α S hS n)

/-- Finite middle degree `n` and finite kernel degree `n+1` give finite quotient degree `n`. -/
theorem moduleCohomology_finite_quotient_of_hom (S : ShortComplex X.Modules)
    (hS : S.ShortExact) (n : ℕ)
    (h₂ : letI := moduleCohomologyModuleOfHom X α S.X₂ n
      Module.Finite R (Sheaf.H.{u + 1} (moduleAddSheaf X S.X₂) n))
    (h₁ : letI := moduleCohomologyModuleOfHom X α S.X₁ (n + 1)
      Module.Finite R (Sheaf.H.{u + 1} (moduleAddSheaf X S.X₁) (n + 1))) :
    letI := moduleCohomologyModuleOfHom X α S.X₃ n
    Module.Finite R (Sheaf.H.{u + 1} (moduleAddSheaf X S.X₃) n) := by
  let := moduleCohomologyModuleOfHom X α S.X₂ n
  let := moduleCohomologyModuleOfHom X α S.X₃ n
  let := moduleCohomologyModuleOfHom X α S.X₁ (n + 1)
  let := h₂
  let := h₁
  exact Module.Finite.of_exact_of_isNoetherian _ _
    (moduleCohomologyConnectingOfHom_exact_left X α S hS n)

/-- Finite quotient degree `n` and finite middle degree `n+1` give finite kernel degree `n+1`. -/
theorem moduleCohomology_finite_left_succ_of_hom (S : ShortComplex X.Modules)
    (hS : S.ShortExact) (n : ℕ)
    (h₃ : letI := moduleCohomologyModuleOfHom X α S.X₃ n
      Module.Finite R (Sheaf.H.{u + 1} (moduleAddSheaf X S.X₃) n))
    (h₂ : letI := moduleCohomologyModuleOfHom X α S.X₂ (n + 1)
      Module.Finite R (Sheaf.H.{u + 1} (moduleAddSheaf X S.X₂) (n + 1))) :
    letI := moduleCohomologyModuleOfHom X α S.X₁ (n + 1)
    Module.Finite R (Sheaf.H.{u + 1} (moduleAddSheaf X S.X₁) (n + 1)) := by
  let := moduleCohomologyModuleOfHom X α S.X₃ n
  let := moduleCohomologyModuleOfHom X α S.X₁ (n + 1)
  let := moduleCohomologyModuleOfHom X α S.X₂ (n + 1)
  let := h₃
  let := h₂
  exact Module.Finite.of_exact_of_isNoetherian _ _
    (moduleCohomologyConnectingOfHom_exact_right X α S hS n)

/-- A submodule sheaf of a sheaf with finite H⁰ has finite original H⁰. -/
theorem moduleH0_finite_left_of_hom (S : ShortComplex X.Modules)
    (hS : S.ShortExact)
    (h₂ : letI := moduleCohomologyModuleOfHom X α S.X₂ 0
      Module.Finite R (Sheaf.H.{u + 1} (moduleAddSheaf X S.X₂) 0)) :
    letI := moduleCohomologyModuleOfHom X α S.X₁ 0
    Module.Finite R (Sheaf.H.{u + 1} (moduleAddSheaf X S.X₁) 0) := by
  let := moduleCohomologyModuleOfHom X α S.X₁ 0
  let := moduleCohomologyModuleOfHom X α S.X₂ 0
  let := h₂
  let := hS.mono_f
  exact Module.Finite.of_injective (moduleCohomologyMapOfHom X α S.f 0)
    (moduleH0MapOfHom_injective X α S.f)

end AlgebraicGeometry.Scheme.Cohomology
