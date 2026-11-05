/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aglib contributors
-/
module

public import Mathlib.CategoryTheory.Monad.Monadicity
public import Mathlib.CategoryTheory.Preadditive.Basic
public import Mathlib.CategoryTheory.ObjectProperty.Kernels
public import Mathlib.CategoryTheory.Limits.Preserves.Finite

/-! # The original adjunction counit as a bar cokernel

The two arrows and augmentation are the actual maps of the given adjunction.
Reflection of this one coequalizer suffices; fullness of the right adjoint is
neither required nor asserted. No alternate realization of the target is chosen.
-/

@[expose] public noncomputable section

namespace CategoryTheory.Adjunction

open Limits Preadditive

universe u v w

variable {C : Type u} {D : Type v} [Category.{w} C] [Category.{w} D]
  {L : C ⥤ D} {U : D ⥤ C} (adj : L ⊣ U)

/-- The original action map, induced once more. -/
abbrev barAction (M : D) : L.obj (U.obj (L.obj (U.obj M))) ⟶ L.obj (U.obj M) :=
  L.map (U.map (adj.counit.app M))

/-- Multiplication of the original free module (the other counit component). -/
abbrev barMultiplication (M : D) :
    L.obj (U.obj (L.obj (U.obj M))) ⟶ L.obj (U.obj M) :=
  adj.counit.app (L.obj (U.obj M))

/-- The target is literally the original object and the map is its original counit. -/
abbrev barCofork (M : D) : Cofork (barAction adj M) (barMultiplication adj M) :=
  Monad.MonadicityInternal.counitCofork adj M

/-- The universal bar presentation only needs reflection of its own diagram. -/
def barIsColimit (M : D)
    [ReflectsColimit (parallelPair (barAction adj M) (barMultiplication adj M)) U] :
    IsColimit (barCofork adj M) :=
  Monad.MonadicityInternal.counitCoequalizerOfReflectsCoequalizer adj M

variable [Preadditive D]

/-- The original action relation, with a fixed sign convention. -/
abbrev barRelation (M : D) : L.obj (U.obj (L.obj (U.obj M))) ⟶ L.obj (U.obj M) :=
  barAction adj M - barMultiplication adj M

/-- The same counit, now as a cokernel of the difference of the two bar maps. -/
abbrev barCokernelCofork (M : D) : CokernelCofork (barRelation adj M) :=
  cokernelCoforkOfCofork (barCofork adj M)

/-- Complete universal cokernel proof, without an arbitrary-quotient hypothesis. -/
def barCokernelIsColimit (M : D)
    [ReflectsColimit (parallelPair (barAction adj M) (barMultiplication adj M)) U] :
    IsColimit (barCokernelCofork adj M) :=
  isColimitCokernelCoforkOfCofork (barIsColimit adj M)

/-- Weak cokernel closure suffices when both actual free terms have the property. -/
theorem property_of_bar (P : ObjectProperty D) [P.IsClosedUnderCokernels]
    (M : D)
    [ReflectsColimit (parallelPair (barAction adj M) (barMultiplication adj M)) U]
    (h₀ : P (L.obj (U.obj M))) (h₁ : P (L.obj (U.obj (L.obj (U.obj M))))) : P M :=
  P.prop_of_isColimit_cokernelCofork (barCokernelIsColimit adj M) h₁ h₀

include adj

/-- A checkable sufficient condition: the original right adjoint is conservative
and preserves finite colimits. It need not be full or preserve injectives. -/
theorem property_of_bar_of_conservative (P : ObjectProperty D)
    [P.IsClosedUnderCokernels] [HasFiniteColimits D]
    [U.ReflectsIsomorphisms] [PreservesFiniteColimits U]
    (M : D) (h₀ : P (L.obj (U.obj M)))
    (h₁ : P (L.obj (U.obj (L.obj (U.obj M))))) : P M :=
  property_of_bar adj P M h₀ h₁

/-- Transfer from the restricted object by induction preservation and the known
forward restriction implication. The latter is applied only to the first free
term; it does not assume the desired reflection theorem. -/
theorem property_of_restricted (P : ObjectProperty D) (Q : ObjectProperty C)
    [P.IsClosedUnderCokernels] [HasFiniteColimits D]
    [U.ReflectsIsomorphisms] [PreservesFiniteColimits U]
    (hL : ∀ N, Q N → P (L.obj N))
    (hU : ∀ N, P N → Q (U.obj N)) (M : D) (hM : Q (U.obj M)) : P M := by
  have h₀ : P (L.obj (U.obj M)) := hL _ hM
  exact property_of_bar_of_conservative adj P M h₀ (hL _ (hU _ h₀))

end CategoryTheory.Adjunction
