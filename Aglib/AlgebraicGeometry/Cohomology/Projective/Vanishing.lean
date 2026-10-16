/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.ProjectiveSpace.Structure
public import Aglib.AlgebraicGeometry.Cohomology.Cech.Finite.Vanishing

/-!
# The cohomological dimension bound on polynomial projective space

The original coordinate affine cover has `n+1` members. The native finite-affine-cover
bound therefore gives vanishing of the unchanged `Sheaf.H` above degree `n`, for every
quasicoherent module over every commutative base ring. An explicit coordinate labeling
preserves arbitrary ring and scheme universes.
-/

@[expose] public section

noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory
open AlgebraicGeometry.ProjectiveSpace

universe u

namespace AlgebraicGeometry.Scheme.Cohomology

variable (R : Type u) [CommRing R] (ι : Type u)

/-- Actual quasicoherent cohomology on polynomial projective `n`-space vanishes above
degree `n`. No Noetherianity, coherence or cohomological finiteness is assumed. -/
theorem projectiveCohomology_subsingleton_of_gt (n : ℕ) (e : ι ≃ Fin (n + 1))
    (M : (ProjectiveSpace R ι).Modules) [M.IsQuasicoherent] (q : ℕ) (hq : n < q) :
    Subsingleton (Sheaf.H.{u + 1} (moduleAddSheaf (ProjectiveSpace R ι) M) q) := by
  let U : Fin (n + 1) → (ProjectiveSpace R ι).Opens :=
    fun i => coordinateOpen R ι (e.symm i)
  have hcover : iSup U = ⊤ := by
    calc
      iSup U = iSup (coordinateOpen R ι) := by
        apply le_antisymm
        · exact iSup_le fun i => le_iSup (coordinateOpen R ι) (e.symm i)
        · apply iSup_le
          intro i
          simpa only [U, Equiv.symm_apply_apply] using le_iSup U (e i)
      _ = ⊤ := iSup_coordinateOpen_eq_top R ι
  exact subsingleton_sheafH_of_finite_affine_cover M n U
    (fun i => isAffineOpen_coordinateOpen R ι (e.symm i)) hcover q hq

end AlgebraicGeometry.Scheme.Cohomology
