/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

import Aglib.AlgebraicGeometry.Morphisms.Etale.ZariskiNagataPurity

/-! Scheme purity retains the actual maps, generic condition and arbitrary characteristic. -/

open CategoryTheory AlgebraicGeometry

universe u

namespace AglibTest.ZariskiNagataPurityScheme

section Integral

variable {X Y : Scheme.{u}} [IsIntegral X] [IsIntegral Y]
variable (f : X ⟶ Y) [IsFinite f] [IsDominant f] [IsLocallyNoetherian Y]
variable (hX : X.NormalStalks) (hY : Y.RegularStalks)
variable (hsep : letI := Scheme.functionFieldMapAlgebra f
  Algebra.IsSeparable Y.functionField X.functionField)

/-- The conclusion is about the original morphism, with no flatness premise. -/
example (hunram : ∀ x : X, Order.coheight x = 1 →
    (f.stalkMap x).hom.FormallyUnramified) : Etale f :=
  f.etale_of_unramified_coheight_one_of_regularStalks hX hY hsep hunram

/-- The codimension condition can instead use the dimension of actual source stalks. -/
example (hunram : ∀ x : X, ringKrullDim (X.presheaf.stalk x) = 1 →
    (f.stalkMap x).hom.FormallyUnramified) : Etale f :=
  f.etale_of_unramified_stalk_dimension_one_of_regularStalks hX hY hsep hunram

/-- In dimension zero the codimension-one condition is empty, but generic separability
remains an explicit hypothesis. -/
example (hdim : ∀ x : X, Order.coheight x = 0) : Etale f := by
  apply f.etale_of_unramified_coheight_one_of_regularStalks hX hY hsep
  intro x hx
  simp only [hdim x, zero_ne_one] at hx

/-- The nonempty affine conclusion is the literal original section map. -/
example (hunram : ∀ x : X, Order.coheight x = 1 →
    (f.stalkMap x).hom.FormallyUnramified)
    (U : Y.Opens) (hU : IsAffineOpen U) [Nonempty U] : (f.app U).hom.Etale :=
  f.etale_app_of_unramified_coheight_one_of_regularStalks hX hY hsep hunram U hU

end Integral

/-- Empty target charts are etale without introducing a domain of empty sections. -/
example {X Y : Scheme.{u}} (f : X ⟶ Y) (U : Y.Opens) [IsEmpty U] : Etale (f ∣_ U) :=
  inferInstance

/-- The integer spectrum is permitted as base, so no field or equicharacteristic
assumption has entered the scheme interface. -/
example {X : Scheme.{0}} [IsIntegral X]
    (f : X ⟶ Spec (.of ℤ)) [IsFinite f] [IsDominant f]
    (hX : X.NormalStalks)
    (hsep : letI := Scheme.functionFieldMapAlgebra f
      Algebra.IsSeparable (Spec (.of ℤ)).functionField X.functionField)
    (hunram : ∀ x : X, Order.coheight x = 1 →
      (f.stalkMap x).hom.FormallyUnramified) : Etale f :=
  f.etale_of_unramified_coheight_one_of_regularStalks
    hX (Scheme.regularStalks_spec ℤ) hsep hunram

end AglibTest.ZariskiNagataPurityScheme
