/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Cohomology.Modules.Scalars
public import Aglib.AlgebraicGeometry.Cohomology.Flasque.Basic
public import Mathlib.CategoryTheory.Sites.SheafCohomology.ExactSequences

/-!
# Long exact cohomology sequences over a specified structural ring

The original module short exact sequence gives the native additive-sheaf
connecting map. Naturality under multiplication by global functions makes
this same map linear over any specified structural ring. All three adjacent
exactness statements retain the existing coefficient maps on actual `Sheaf.H`.
No quasicoherence, flatness or finiteness premise is required.
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

variable (X : Scheme.{u})

/-- The original module short complex with its scalar action forgotten. -/
abbrev moduleCoefficientSequence (S : ShortComplex X.Modules) :
    ShortComplex (Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}) := by
  let F : X.Modules ⥤ Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u} :=
    SheafOfModules.toSheaf.{u} X.ringCatSheaf
  let : F.Additive := ⟨by intros; rfl⟩
  exact S.map F

/-- Actual module short exactness gives actual additive-sheaf short exactness. -/
theorem moduleCoefficientSequence_shortExact (S : ShortComplex X.Modules)
    (hS : S.ShortExact) : (moduleCoefficientSequence X S).ShortExact :=
  Scheme.Modules.shortExact_toSheaf hS

/-- Multiplication by a global function is an endomorphism of the original short complex. -/
def moduleCoefficientSequenceScalar (S : ShortComplex X.Modules) (a : Γ(X, ⊤)) :
    moduleCoefficientSequence X S ⟶ moduleCoefficientSequence X S where
  τ₁ := moduleScalarOfGlobal X S.X₁ a
  τ₂ := moduleScalarOfGlobal X S.X₂ a
  τ₃ := moduleScalarOfGlobal X S.X₃ a
  comm₁₂ := moduleScalarOfGlobal_naturality X S.f a
  comm₂₃ := moduleScalarOfGlobal_naturality X S.g a

variable {R : Type u} [CommRing R] (α : R →+* Γ(X, ⊤))

/-- The native connecting map is linear for the specified structural ring action. -/
def moduleCohomologyConnectingOfHom (S : ShortComplex X.Modules)
    (hS : S.ShortExact) (n : ℕ) :
    letI := moduleCohomologyModuleOfHom X α S.X₃ n
    letI := moduleCohomologyModuleOfHom X α S.X₁ (n + 1)
    Sheaf.H.{u + 1} (moduleAddSheaf X S.X₃) n →ₗ[R]
      Sheaf.H.{u + 1} (moduleAddSheaf X S.X₁) (n + 1) := by
  letI := moduleCohomologyModuleOfHom X α S.X₃ n
  letI := moduleCohomologyModuleOfHom X α S.X₁ (n + 1)
  refine {
    __ := Sheaf.H.δ (moduleCoefficientSequence_shortExact X S hS) n (n + 1) rfl
    map_smul' := fun a x => ?_ }
  exact Sheaf.H.δ_naturality n (n + 1) rfl
    (moduleCoefficientSequence_shortExact X S hS)
    (moduleCoefficientSequence_shortExact X S hS)
    (moduleCoefficientSequenceScalar X S (α a)) x

/-- The linear connecting map retains the literal native additive connecting map. -/
theorem moduleCohomologyConnectingOfHom_apply (S : ShortComplex X.Modules)
    (hS : S.ShortExact) (n : ℕ) (x : Sheaf.H.{u + 1} (moduleAddSheaf X S.X₃) n) :
    letI := moduleCohomologyModuleOfHom X α S.X₃ n
    letI := moduleCohomologyModuleOfHom X α S.X₁ (n + 1)
    moduleCohomologyConnectingOfHom X α S hS n x =
      Sheaf.H.δ (moduleCoefficientSequence_shortExact X S hS) n (n + 1) rfl x := rfl

/-- Original coefficient maps form an exact cohomology sequence in every degree. -/
theorem moduleCohomologyMapOfHom_exact (S : ShortComplex X.Modules)
    (hS : S.ShortExact) (n : ℕ) :
    letI := moduleCohomologyModuleOfHom X α S.X₁ n
    letI := moduleCohomologyModuleOfHom X α S.X₂ n
    letI := moduleCohomologyModuleOfHom X α S.X₃ n
    Function.Exact (moduleCohomologyMapOfHom X α S.f n)
      (moduleCohomologyMapOfHom X α S.g n) := by
  exact (ShortComplex.ab_exact_iff_function_exact _).mp
    (Sheaf.H.longSequence_exact₂' (moduleCoefficientSequence_shortExact X S hS) n)

/-- Exactness at the term preceding the native connecting map. -/
theorem moduleCohomologyConnectingOfHom_exact_left (S : ShortComplex X.Modules)
    (hS : S.ShortExact) (n : ℕ) :
    letI := moduleCohomologyModuleOfHom X α S.X₂ n
    letI := moduleCohomologyModuleOfHom X α S.X₃ n
    letI := moduleCohomologyModuleOfHom X α S.X₁ (n + 1)
    Function.Exact (moduleCohomologyMapOfHom X α S.g n)
      (moduleCohomologyConnectingOfHom X α S hS n) := by
  exact (ShortComplex.ab_exact_iff_function_exact _).mp
    (Sheaf.H.longSequence_exact₃' (moduleCoefficientSequence_shortExact X S hS) n (n + 1) rfl)

/-- Exactness at the term following the native connecting map. -/
theorem moduleCohomologyConnectingOfHom_exact_right (S : ShortComplex X.Modules)
    (hS : S.ShortExact) (n : ℕ) :
    letI := moduleCohomologyModuleOfHom X α S.X₃ n
    letI := moduleCohomologyModuleOfHom X α S.X₁ (n + 1)
    letI := moduleCohomologyModuleOfHom X α S.X₂ (n + 1)
    Function.Exact (moduleCohomologyConnectingOfHom X α S hS n)
      (moduleCohomologyMapOfHom X α S.f (n + 1)) := by
  exact (ShortComplex.ab_exact_iff_function_exact _).mp
    (Sheaf.H.longSequence_exact₁' (moduleCoefficientSequence_shortExact X S hS) n (n + 1) rfl)

/-- The original connecting maps are natural in an actual morphism of short exact sequences. -/
theorem moduleCohomologyConnectingOfHom_naturality
    {S T : ShortComplex X.Modules} (hS : S.ShortExact) (hT : T.ShortExact)
    (φ : S ⟶ T) (n : ℕ) (x : Sheaf.H.{u + 1} (moduleAddSheaf X S.X₃) n) :
    letI := moduleCohomologyModuleOfHom X α S.X₃ n
    letI := moduleCohomologyModuleOfHom X α S.X₁ (n + 1)
    letI := moduleCohomologyModuleOfHom X α T.X₃ n
    letI := moduleCohomologyModuleOfHom X α T.X₁ (n + 1)
    moduleCohomologyConnectingOfHom X α T hT n
        (moduleCohomologyMapOfHom X α φ.τ₃ n x) =
      moduleCohomologyMapOfHom X α φ.τ₁ (n + 1)
        (moduleCohomologyConnectingOfHom X α S hS n x) := by
  let F : X.Modules ⥤ Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u} :=
    SheafOfModules.toSheaf.{u} X.ringCatSheaf
  let : F.Additive := ⟨by intros; rfl⟩
  exact Sheaf.H.δ_naturality n (n + 1) rfl
    (moduleCoefficientSequence_shortExact X S hS)
    (moduleCoefficientSequence_shortExact X T hT)
    (F.mapShortComplex.map φ) x

/-- An original coefficient monomorphism induces an injective original H⁰ map. -/
theorem moduleH0MapOfHom_injective {M N : X.Modules} (f : M ⟶ N) [Mono f] :
    letI := moduleCohomologyModuleOfHom X α M 0
    letI := moduleCohomologyModuleOfHom X α N 0
    Function.Injective (moduleCohomologyMapOfHom X α f 0) := by
  let F := SheafOfModules.toSheaf.{u} X.ringCatSheaf
  let : Mono (F.map f) := inferInstance
  intro x y h
  apply (Ext.addEquiv₀.{u + 1}).injective
  apply (cancel_mono (F.map f)).mp
  change Sheaf.H.map (F.map f) 0 x = Sheaf.H.map (F.map f) 0 y at h
  simpa only [Sheaf.H.addEquiv₀_map] using congrArg (Ext.addEquiv₀.{u + 1}) h

end AlgebraicGeometry.Scheme.Cohomology
