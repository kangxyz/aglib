/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Properties.Normal.Components
public import Mathlib.AlgebraicGeometry.Morphisms.Finite
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion

/-! # The actual normal component at a specified point

The component is the original open subset with its original inclusion.
Its integrality and closed immersion are constructed, not assumed. Finite
structural maps restrict to finite maps on this same component.
-/

@[expose] public noncomputable section

open CategoryTheory

namespace AlgebraicGeometry.Scheme

universe u

variable (X : Scheme.{u}) [IsLocallyNoetherian X] (hX : NormalStalks X) (x : X)

/-- The actual open irreducible component containing the specified point. -/
def normalComponentOpen : X.Opens :=
  ⟨irreducibleComponent x, normalComponentsOpen X inferInstance hX _
    (irreducibleComponent_mem_irreducibleComponents x)⟩

/-- The specified point lies in this original component. -/
theorem mem_normalComponentOpen : x ∈ normalComponentOpen X hX x :=
  mem_irreducibleComponent

/-- This open component is also closed in the original scheme. -/
theorem normalComponentOpen_isClosed :
    IsClosed (normalComponentOpen X hX x : Set X) :=
  isClosed_irreducibleComponent

/-- Integrality is derived on the actual open component, not on a replacement
connected cover or an unrelated field spectrum. -/
instance normalComponentOpen_isIntegral : IsIntegral (normalComponentOpen X hX x) := by
  let : IsReduced X := hX.isReduced
  let : IrreducibleSpace (normalComponentOpen X hX x) :=
    isIrreducible_iff_irreducibleSpace.mp isIrreducible_irreducibleComponent
  exact isIntegral_of_irreducibleSpace_of_isReduced _

/-- The original open inclusion is simultaneously a closed immersion. -/
instance normalComponentOpen_isClosedImmersion :
    IsClosedImmersion (normalComponentOpen X hX x).ι :=
  .of_isPreimmersion _ (by
    rw [Scheme.Opens.range_ι]
    exact normalComponentOpen_isClosed X hX x)

/-- A finite structural map stays finite on the same component. -/
instance normalComponentOpen_isFinite {S : Scheme.{u}} (p : X ⟶ S) [IsFinite p] :
    IsFinite ((normalComponentOpen X hX x).ι ≫ p) := inferInstance

end AlgebraicGeometry.Scheme
