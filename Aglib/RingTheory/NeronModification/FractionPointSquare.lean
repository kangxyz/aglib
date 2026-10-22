/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.RingTheory.NeronModification.FractionField

/-! # Compatibility of the fixed fraction field with the actual global point

A fixed embedding of the original fraction field into the target fraction
field remains compatible with each actual global modification lift.
-/

@[expose] public noncomputable section

namespace Algebra.NeronModification

variable {B C ι : Type*} [CommRing B] [IsDomain B] [CommRing C]
variable (K T : Type*) [Field K] [Field T] [Algebra B K] [IsFractionRing B K]
variable (p : B) (g : ι → B) (hp : p ≠ 0)
variable (f : B →+* C) (z : ι → C) (hz : ∀ i, f p * z i = f (g i))
variable (hfp : IsRegular (f p)) (j : K →+* T) (c : C →+* T)
variable (hcomm : j.comp (algebraMap B K) = c.comp f)

omit [IsDomain B] in
include hcomm in
/-- The actual new point and the new action on the SAME original fraction field agree. -/
theorem fractionPoint_square :
    j.comp (fractionPoint K p g hp) = c.comp (lift p g f z hz hfp) := by
  have hreg : IsRegular ((c.comp f) p) := by
    rw [← hcomm]
    apply isRegular_iff_ne_zero.mpr
    exact (map_ne_zero_iff j j.injective).mpr
      ((map_ne_zero_iff (algebraMap B K) (IsFractionRing.injective B K)).mpr hp)
  have hcz (i : ι) : (c.comp f) p * c (z i) = (c.comp f) (g i) := by
    change c (f p) * c (z i) = c (f (g i))
    rw [← map_mul, hz]
  apply (lift_unique p g (c.comp f) (fun i => c (z i)) hcz hreg _ ?_).trans
    (lift_unique p g (c.comp f) (fun i => c (z i)) hcz hreg _ ?_).symm
  · ext b
    change j (fractionPoint K p g hp (of p g b)) = c (f b)
    rw [fractionPoint_of]
    exact DFunLike.congr_fun hcomm b
  · ext b
    change c (lift p g f z hz hfp (of p g b)) = c (f b)
    rw [lift_of]

end Algebra.NeronModification
