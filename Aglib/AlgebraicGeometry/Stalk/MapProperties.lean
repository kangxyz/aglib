/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.RingTheory.Localization.Submodule
public import Mathlib.RingTheory.LocalRing.ResidueField.Basic

/-!
# Properties of actual scheme stalk maps

The maximal-ideal comparison holds for every scheme map. Source-stalk
Noetherianity requires only local finite type and Noetherianity of the target
stalk; no global Noetherian or etale hypothesis is imposed.

Source: Aglib/AlgebraicGeometry/Morphisms/Etale/StalkMap.lean:42–62 at
451aeda6b8bb5b44402b574dd6cf60f912360f8c. Statements and proofs are unchanged.
-/

@[expose] public section

noncomputable section

open CategoryTheory AlgebraicGeometry IsLocalRing

universe u

namespace AlgebraicGeometry.Scheme

variable {X Y : Scheme.{u}}

/-- The maximal ideal of the actual source stalk lies over that of the target
stalk, for the algebra defined by the actual stalk map. -/
theorem stalkMap_maximalIdeal_liesOver (f : X ⟶ Y) (x : X) :
    let := (f.stalkMap x).hom.toAlgebra
    (maximalIdeal (X.presheaf.stalk x)).LiesOver
      (maximalIdeal (Y.presheaf.stalk (f x))) := by
  let := (f.stalkMap x).hom.toAlgebra
  let : IsLocalHom (algebraMap (Y.presheaf.stalk (f x)) (X.presheaf.stalk x)) :=
    f.toLRSHom.prop x
  infer_instance

/-- Essential finite type of the actual stalk map transports Noetherianity
from the target stalk; no global Noetherian hypothesis is required. -/
theorem isNoetherianRing_stalk_of_locallyOfFiniteType (f : X ⟶ Y)
    [LocallyOfFiniteType f] (x : X)
    [IsNoetherianRing (Y.presheaf.stalk (f x))] :
    IsNoetherianRing (X.presheaf.stalk x) := by
  let := (f.stalkMap x).hom.toAlgebra
  let : Algebra.EssFiniteType (Y.presheaf.stalk (f x)) (X.presheaf.stalk x) :=
    LocallyOfFiniteType.stalkMap f x
  exact Algebra.EssFiniteType.isNoetherianRing (Y.presheaf.stalk (f x)) (X.presheaf.stalk x)

end AlgebraicGeometry.Scheme
