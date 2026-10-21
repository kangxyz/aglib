/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.RingTheory.IntegralClosure.Localization

/-! The canonical scalar-extension tensor product is the literal localized integral closure. -/

@[expose] public section

noncomputable section

open scoped TensorProduct

namespace integralClosure

variable (A D L : Type*) [CommRing A] [CommRing D] [CommRing L]
  [Algebra A D] [Algebra D L] [Algebra A L] [IsScalarTower A D L]
  (M : Submonoid A) [IsLocalization M D]

/-- The original base-change tensor maps to the literal integral closure by multiplication. -/
def scalarExtensionTensorEquiv :
    D ⊗[A] integralClosure A L ≃ₐ[D] integralClosure D L := by
  let := scalarExtensionAlgebra A D L
  let := scalarExtension_isScalarTower_base A D L
  let := scalarExtension_isScalarTower_ambient A D L
  let := scalarExtension_isLocalization A D L M
  let : Algebra.IsPushout A (integralClosure A L) D (integralClosure D L) :=
    Algebra.isPushout_of_isLocalization M D (integralClosure A L) (integralClosure D L)
  let : Algebra.IsPushout A D (integralClosure A L) (integralClosure D L) :=
    Algebra.IsPushout.symm inferInstance
  exact Algebra.IsPushout.equiv A D (integralClosure A L) (integralClosure D L)

/-- The comparison preserves the actual ambient-field inclusion on pure tensors. -/
@[simp] theorem scalarExtensionTensorEquiv_tmul (d : D) (b : integralClosure A L) :
    (scalarExtensionTensorEquiv A D L M (d ⊗ₜ[A] b) : L) = algebraMap D L d * (b : L) := by
  let := scalarExtensionAlgebra A D L
  let := scalarExtension_isScalarTower_base A D L
  let := scalarExtension_isScalarTower_ambient A D L
  let := scalarExtension_isLocalization A D L M
  let : Algebra.IsPushout A (integralClosure A L) D (integralClosure D L) :=
    Algebra.isPushout_of_isLocalization M D (integralClosure A L) (integralClosure D L)
  let : Algebra.IsPushout A D (integralClosure A L) (integralClosure D L) :=
    Algebra.IsPushout.symm inferInstance
  simpa only [scalarExtensionTensorEquiv, map_mul, ← IsScalarTower.algebraMap_apply,
    Subalgebra.algebraMap_def, Algebra.algebraMap_self, RingHom.id_apply] using
    congrArg (algebraMap (integralClosure D L) L)
      (Algebra.IsPushout.equiv_tmul A D (integralClosure A L) (integralClosure D L) d b)

end integralClosure
