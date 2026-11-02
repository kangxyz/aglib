/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.Finiteness.ConstructiblePrimeField
public import Aglib.AlgebraicGeometry.EtaleCohomology.Finiteness.ConstructibleConstantReduction
public import Aglib.AlgebraicGeometry.EtaleCohomology.Curves.CharacteristicPrimary

/-! # Constructible higher images of original cyclic characteristic-primary coefficients

The genuine cyclic short exact sequences propagate all-degree constructibility
from the original prime-field coefficient to its cyclic powers. The geometric
conclusion is stated separately in each degree; it does not assert one common
partition for all degrees.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Scheme.EtaleCohomology

attribute [local instance] hasSheafifyLarge HasDerivedCategory.standard

/-- Over a locally Noetherian characteristic-p base, every original proper
higher image of a constant cyclic p-power group is constructible. No smoothness,
flatness, reducedness or source-integrality hypothesis is imposed. -/
theorem cyclicPrimePowerHigherDirectImage_isConstructible
    {X S : Scheme.{u}} [IsLocallyNoetherian S] (f : X ⟶ S) [IsProper f]
    (p : ℕ) (hp : p.Prime) (hS : (p : Γ(S, ⊤)) = 0) (r q : ℕ) :
    Constructible.IsConstructible ((higherDirectImage f q).obj
      (ConstantFinite.coefficient (ULift.{u} (ZMod (p ^ r))) X)) := by
  apply cyclicPrimePowerHigherDirectImage_isConstructible_of_prime f p hp.pos
  intro n
  exact (Constructible.isConstructible_iff_of_iso
    ((higherDirectImage f n).mapIso (Curves.cyclicPrimeFieldIso X p))).mpr
      (primeFieldHigherDirectImage_isConstructible f p hp hS n)

end AlgebraicGeometry.Scheme.EtaleCohomology
