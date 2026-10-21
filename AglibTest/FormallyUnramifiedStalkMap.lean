/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

import Aglib.AlgebraicGeometry.Morphisms.FormallyUnramified.StalkMap

/-! The coordinate/stalk comparison has no finite, normal, or integral hypotheses. -/

open CategoryTheory AlgebraicGeometry

universe u

namespace AglibTest.FormallyUnramifiedStalkMap

variable {X Y : Scheme.{u}} (f : X ⟶ Y)
  (U : Y.Opens) (hU : IsAffineOpen U) (V : X.Opens) (hV : IsAffineOpen V)
  (hVU : V ≤ f ⁻¹ᵁ U)

example (x : V)
    (h : letI := (f.appLE U V hVU).hom.toAlgebra
      Algebra.IsUnramifiedAt Γ(Y, U) (hV.primeIdealOf x).asIdeal) :
    (f.stalkMap x).hom.FormallyUnramified :=
  (f.isUnramifiedAt_iff_stalkMap_formallyUnramified U hU V hV hVU x).mp h

example (x : V) (h : (f.stalkMap x).hom.FormallyUnramified) :
    letI := (f.appLE U V hVU).hom.toAlgebra
    Algebra.IsUnramifiedAt Γ(Y, U) (hV.primeIdealOf x).asIdeal :=
  (f.isUnramifiedAt_iff_stalkMap_formallyUnramified U hU V hV hVU x).mpr h

/-- Empty charts do not acquire an artificial domain or nonempty condition. -/
example [IsEmpty V] : ∀ x : V,
    letI := (f.appLE U V hVU).hom.toAlgebra
    Algebra.IsUnramifiedAt Γ(Y, U) (hV.primeIdealOf x).asIdeal ↔
      (f.stalkMap x).hom.FormallyUnramified :=
  fun x => f.isUnramifiedAt_iff_stalkMap_formallyUnramified U hU V hV hVU x

end AglibTest.FormallyUnramifiedStalkMap
