/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

import Aglib.RingTheory.IntegralClosure.Localization
import Mathlib.RingTheory.Localization.AtPrime.Basic

/-! The literal normalization inclusion, its ambient map, and prime localization. -/

example {A D L : Type*} [CommRing A] [CommRing D] [CommRing L]
    [Algebra A D] [Algebra D L] [Algebra A L] [IsScalarTower A D L]
    (M : Submonoid A) [IsLocalization M D] :
    IsLocalizedModule M (integralClosure.scalarExtensionHom A D L).toLinearMap :=
  integralClosure.scalarExtensionHom_isLocalizedModule A D L M

example {A L : Type*} [CommRing A] [Field L] [Algebra A L]
    (p : Ideal A) [p.IsPrime] [Algebra (Localization.AtPrime p) L]
    [IsScalarTower A (Localization.AtPrime p) L] :
    letI := integralClosure.scalarExtensionAlgebra A (Localization.AtPrime p) L
    letI := integralClosure.scalarExtension_isScalarTower_base A (Localization.AtPrime p) L
    IsLocalizedModule p.primeCompl
      (IsScalarTower.toAlgHom A (integralClosure A L)
        (integralClosure (Localization.AtPrime p) L)).toLinearMap := by
  exact integralClosure.scalarExtensionHom_isLocalizedModule A (Localization.AtPrime p) L
    p.primeCompl

example {A D L : Type*} [CommRing A] [CommRing D] [CommRing L]
    [Algebra A D] [Algebra D L] [Algebra A L] [IsScalarTower A D L]
    (x : integralClosure A L) :
    (integralClosure.scalarExtensionHom A D L x : L) = x := rfl
