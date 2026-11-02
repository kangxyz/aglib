/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.CategoryTheory.Galois.FiberCompatibleReflection
public import Aglib.AlgebraicGeometry.Morphisms.FiniteEtale.GenericFiber
public import Aglib.AlgebraicGeometry.Morphisms.FiniteEtale.GaloisInstances

/-! # Galois reflection for the actual generic restriction

Normality supplies full faithfulness of the original generic restriction.
The fibre comparison and the actual map on automorphisms reflect Galoisness
and retain the original deck-group order.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.PreGaloisCategory

namespace AlgebraicGeometry.Scheme.FiniteEtale

universe u

variable (X : Scheme.{u}) [IsIntegral X]
  [∀ x : X, IsIntegrallyClosed (X.presheaf.stalk x)]
  (Y : Scheme.FiniteEtale X) [ConnectedSpace Y.obj.left]
  [IsGalois ((baseChange (X.fromSpecStalk (genericPoint X))).obj Y)]

/-- Galoisness of the literal generic restriction reflects to the original cover. -/
theorem isGalois_of_generic_baseChange : IsGalois Y := by
  let g := X.fromSpecStalk (genericPoint X)
  let s := algebraicClosureResiduePoint (Spec X.functionField)
    (Classical.choice (inferInstance : Nonempty (Spec X.functionField)))
  let : IsConnected Y := Connectedness.categoricalConnected_of_connectedSpace Y
  exact isGalois_of_fiberCompatible_of_fullyFaithful
    (fiberToFinite (s ≫ g)) (fiberToFinite s) (baseChange g)
    (fiberToFiniteBaseChangeIso g s) Y

/-- The generic restriction has exactly the original deck-group order. -/
theorem card_aut_generic_baseChange :
    Nat.card (Aut ((baseChange (X.fromSpecStalk (genericPoint X))).obj Y)) =
      Nat.card (Aut Y) := by
  let : IsGalois Y := isGalois_of_generic_baseChange X Y
  let g := X.fromSpecStalk (genericPoint X)
  let s := algebraicClosureResiduePoint (Spec X.functionField)
    (Classical.choice (inferInstance : Nonempty (Spec X.functionField)))
  exact card_aut_obj_of_fiberCompatible
    (fiberToFinite (s ≫ g)) (fiberToFinite s) (baseChange g)
    (fiberToFiniteBaseChangeIso g s) Y

end AlgebraicGeometry.Scheme.FiniteEtale
