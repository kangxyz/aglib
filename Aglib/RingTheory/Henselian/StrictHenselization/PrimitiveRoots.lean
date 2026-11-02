/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.RingTheory.Henselian.StrictHenselization.Colimit
public import Aglib.Algebra.Category.Ring.Descent.PrimitiveRoots

/-! # Primitive roots in genuine etale neighborhoods

The original primitive root descends after any prescribed pointed etale
neighborhood with its exact colimit image. The stage is the original etale
algebra, not its prime localization. No colimit domain or Noetherianity is used.
-/

@[expose] public noncomputable section

open CategoryTheory

namespace GeometricEtaleColimit

universe u

/-- A specified primitive root appears in a genuine etale neighborhood after
any prescribed stage, retaining its original image. -/
theorem exists_primitiveRoot_rep_over
    (R Ω : Type u) [CommRing R] [Field Ω] [Algebra R Ω]
    {n : ℕ} {ζ : GeometricEtaleColimit R Ω} (hζ : IsPrimitiveRoot ζ n)
    (X : GeometricEtaleNeighborhood R Ω) :
    ∃ (Y : GeometricEtaleNeighborhood R Ω) (_ : X ⟶ Y) (a : Y.algebra),
      ι R Ω Y a = ζ ∧ IsPrimitiveRoot a n := by
  exact CommRingCat.exists_primitiveRoot_rep_over
    (GeometricEtaleNeighborhood.ringDiagram R Ω) (ringCocone R Ω)
    (ringCoconeIsColimit R Ω) hζ X

end GeometricEtaleColimit
