/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Modules.ClosedImmersion.Killed
public import Aglib.AlgebraicGeometry.Modules.Locality.Sections

/-! # Ideal annihilation of ordinary module-sheaf subobjects -/

@[expose] public noncomputable section

open CategoryTheory

namespace AlgebraicGeometry.Scheme.Modules

universe u

variable {X : Scheme.{u}}

/-- Every ordinary subobject of a module killed by an ideal sheaf is killed
by the same ideal, on its original affine sections. -/
theorem killedByIdealSheaf_of_mono (I : X.IdealSheafData)
    {M N : X.Modules} (f : M ⟶ N) [Mono f] (hN : killedByIdealSheaf I N) :
    killedByIdealSheaf I M := by
  intro U a ha x
  apply moduleHom_app_injective f U.1
  rw [Hom.app_smul, hN U a ha, map_zero]

end AlgebraicGeometry.Scheme.Modules
