/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Cohomology.GrothendieckExistence.OpenIdealPullback
public import Aglib.AlgebraicGeometry.Modules.QuasiCoherent.Limits

/-!
# Restriction of original bounded defects

Open restriction preserves ordinary kernels and cokernels. The original
geometric quotient-unit comparison transports their annihilation to the
actual pulled ideal, retaining the exponent. No completion of a localized
ring is identified with an ordinary localization of a completed module.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Scheme.Modules.Coherent

variable {X Y : Scheme.{u}} (j : Y ⟶ X) [IsOpenImmersion j]
  (J : X.IdealSheafData)

/-- An actual killed quasicoherent coefficient remains killed on open
restriction, using the original restriction/pullback comparison. -/
theorem killedByIdealSheaf_restrict_pow (M : X.Modules) [M.IsQuasicoherent]
    (t : ℕ) (hM : killedByIdealSheaf (J ^ t) M) :
    killedByIdealSheaf (J.comap j ^ t) (M.restrict j) :=
  killedByIdealSheaf_of_iso _ ((restrictFunctorIsoPullback j).app M).symm
    (killedByOpenIdeal_pullback j J M t hM)

/-- Restriction preserves the actual kernel defect bound with the same
power of the actual restricted ideal. -/
theorem killed_kernel_restrict_pow {M N : X.Modules}
    [M.IsQuasicoherent] [N.IsQuasicoherent] (f : M ⟶ N) (t : ℕ)
    (h : killedByIdealSheaf (J ^ t) (kernel f)) :
    killedByIdealSheaf (J.comap j ^ t) (kernel ((restrictFunctor j).map f)) := by
  let : (kernel f).IsQuasicoherent := QuasiCoherent.quasicoherent_kernel f
  exact killedByIdealSheaf_of_iso _ (PreservesKernel.iso (restrictFunctor j) f)
    (killedByIdealSheaf_restrict_pow j J (kernel f) t h)

/-- Restriction preserves the actual cokernel defect bound with the same
power of the actual restricted ideal. -/
theorem killed_cokernel_restrict_pow {M N : X.Modules}
    [M.IsQuasicoherent] [N.IsQuasicoherent] (f : M ⟶ N) (t : ℕ)
    (h : killedByIdealSheaf (J ^ t) (cokernel f)) :
    killedByIdealSheaf (J.comap j ^ t) (cokernel ((restrictFunctor j).map f)) := by
  let : (cokernel f).IsQuasicoherent := QuasiCoherent.quasicoherent_cokernel f
  exact killedByIdealSheaf_of_iso _ (PreservesCokernel.iso (restrictFunctor j) f)
    (killedByIdealSheaf_restrict_pow j J (cokernel f) t h)

end AlgebraicGeometry.Scheme.Modules.Coherent
