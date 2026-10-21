/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.IdealSheaf.Invertible.StalkKernel
public import Aglib.RingTheory.RegularLocalRing.HeightOnePrincipal
public import Mathlib.AlgebraicGeometry.FunctionField

/-!
# Height-one integral closed subschemes of regular surfaces

The actual ideal module is locally rank one when all ambient stalks are regular
of dimension at most two and the actual stalk-map kernels have height one.
The height-one ideal bases feed the shared stalk-kernel criterion; all kernel
localization, basis spreading, and sheaf comparisons are implemented there.
-/

@[expose] public section

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry.Scheme.Modules.Invertible

namespace AlgebraicGeometry.Scheme.Hom

variable {C X : Scheme.{u}}

/-- An integral closed subscheme with height-one actual stalk kernels has a
locally rank-one actual ideal module when the ambient scheme is locally
Noetherian and all its stalks are regular of dimension at most two. -/
theorem idealModule_isLocallyRankOne_of_regularSurface
    [IsLocallyNoetherian X] [IsIntegral C] (i : C ⟶ X) [IsClosedImmersion i]
    (hregular : ∀ x : X, IsRegularLocalRing (X.presheaf.stalk x))
    (hdim : ∀ x : X, ringKrullDim (X.presheaf.stalk x) ≤ 2)
    (hheight : ∀ c : C, (RingHom.ker (i.stalkMap c).hom).height = 1) :
    IsLocallyRankOne X (idealModule i) := by
  apply idealModule_isLocallyRankOne_of_stalkKernelBasis i
  intro c
  have : IsRegularLocalRing (X.presheaf.stalk (i c)) := hregular (i c)
  have : (RingHom.ker (i.stalkMap c).hom).IsPrime := RingHom.ker_isPrime _
  exact ⟨IsRegularLocalRing.heightOneIdealBasisOfDimensionLETwo
    (X.presheaf.stalk (i c)) (hdim (i c))
    (RingHom.ker (i.stalkMap c).hom) (hheight c)⟩

end AlgebraicGeometry.Scheme.Hom
