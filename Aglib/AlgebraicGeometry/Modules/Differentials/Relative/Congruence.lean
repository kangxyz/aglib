/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Modules.Differentials.Relative.Restriction

/-!
# Reflexivity of the original structural differential comparison

The existing comparison is constructed through the original universal derivations.
Its reflexivity is proved by that same universal property, not by replacing the
comparison with an equality transport. No open or finiteness hypothesis is used.
-/

@[expose] public noncomputable section

open CategoryTheory

universe u

namespace AlgebraicGeometry.Scheme.Modules.Differentials

/-- The original universal-derivation comparison at reflexivity is the identity iso. -/
theorem relativeDifferentialCongrIso_refl {X Y : Scheme.{u}} (f : X ⟶ Y) :
    relativeDifferentialCongrIso f (rfl : f = f) =
      Iso.refl (relativeDifferentialSheaf f) := by
  apply Iso.ext
  apply relativeDifferentialSheaf_hom_ext f _
  intro U a
  exact relativeDifferentialCongrIso_hom_d f rfl U a

end AlgebraicGeometry.Scheme.Modules.Differentials
