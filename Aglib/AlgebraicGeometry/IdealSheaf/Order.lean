/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.IdealSheaf.Modules
public import Mathlib.AlgebraicGeometry.IdealSheaf.Subscheme

/-!
# Closed subschemes are ordered by their ideal modules

`Scheme.IdealSheafData.le_of_idealInclusion_factor`: if the actual ideal inclusion of `W` factors
through that of `W'`, then `W ≤ W'`. On an affine open `U` the ideal of `W` is the kernel of
`Γ(X, U) ⟶ Γ(W, W ∩ U)` (Mathlib's `ker_subschemeι_app`), and the factorization carries sections
of `I_W` to sections of `I_{W'}`.
-/

@[expose] public section

noncomputable section

open CategoryTheory Opposite

universe u

namespace AlgebraicGeometry.Scheme.IdealSheafData

variable {X : Scheme.{u}}

-- The sectionwise ideal equivalence is applied to ring sections presented through the sheaf of
-- rings.
set_option backward.isDefEq.respectTransparency false in
/-- **Closed subschemes are ordered by their actual ideal modules**: if the ideal inclusion of `W`
factors through that of `W'`, then `W ≤ W'`. -/
theorem le_of_idealInclusion_factor (W W' : X.IdealSheafData)
    (k : Scheme.Hom.idealModule W.subschemeι ⟶ Scheme.Hom.idealModule W'.subschemeι)
    (hk : k ≫ Scheme.Hom.idealInclusion W'.subschemeι = Scheme.Hom.idealInclusion W.subschemeι) :
    W ≤ W' := by
  rw [Scheme.IdealSheafData.le_def]
  intro U a ha
  rw [← ker_subschemeι_app] at ha ⊢
  let b := (Scheme.Hom.idealSectionsEquiv W.subschemeι U).symm ⟨a, ha⟩
  have hb : (Scheme.Hom.idealInclusion W.subschemeι).val.app (op U) b = a := by
    rw [← Scheme.Hom.idealSectionsEquiv_val]
    simp [b]
  have hb' : (Scheme.Hom.idealInclusion W'.subschemeι).val.app (op U)
      (k.val.app (op U) b) = a := by
    rw [← hb, ← hk]
    rfl
  rw [← hb', ← Scheme.Hom.idealSectionsEquiv_val]
  exact (Scheme.Hom.idealSectionsEquiv W'.subschemeι U (k.val.app (op U) b)).2

end AlgebraicGeometry.Scheme.IdealSheafData
