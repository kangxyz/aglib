/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Cohomology.GrothendieckExistence.AffineQuotientDefects
public import Aglib.AlgebraicGeometry.Cohomology.GrothendieckExistence.AffineDefectSections
public import Aglib.AlgebraicGeometry.Modules.QuasiCoherent.AffinePushforward

/-! # Independent quotient bounds on actual affine sheaf defects -/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Scheme.Modules.Coherent

universe u
variable {B : CommRingCat.{u}} {M N : (Spec B).Modules}
  [M.IsQuasicoherent] [N.IsQuasicoherent] (f : M ⟶ N)

/-- The actual independent ideal quotient has bounded ordinary sheaf defects.
The kernel and cokernel are not asserted to form adic systems. -/
theorem affineQuotient_defectsKilled (J K : (Spec B).IdealSheafData) (t n : ℕ)
    (hk : killedByIdealSheaf (J ^ t) (kernel f))
    (hc : killedByIdealSheaf (J ^ t) (cokernel f)) :
    killedByIdealSheaf (J ^ (t * 2))
        (kernel ((idealSheafQuotientFunctor (Spec B) (K ^ n)).map f)) ∧
      killedByIdealSheaf (J ^ (t * 2))
        (cokernel ((idealSheafQuotientFunctor (Spec B) (K ^ n)).map f)) := by
  let : ((idealSheafQuotientFunctor (Spec B) (K ^ n)).obj M).IsQuasicoherent :=
    isQuasicoherent_pushforward_of_isAffineHom (K ^ n).subschemeι
      ((pullback (K ^ n).subschemeι).obj M)
  let : ((idealSheafQuotientFunctor (Spec B) (K ^ n)).obj N).IsQuasicoherent :=
    isQuasicoherent_pushforward_of_isAffineHom (K ^ n).subschemeι
      ((pullback (K ^ n).subschemeι).obj N)
  have h := affineQuotient_sections_bounds f J K t n
    (affineSections_kernel_bound f J t hk) (affineSections_cokernel_bound f J t hc)
  exact ⟨killed_kernel_of_affineSections_bound _ J (t * 2) h.1,
    killed_cokernel_of_affineSections_bound _ J (t * 2) h.2⟩

end AlgebraicGeometry.Scheme.Modules.Coherent
