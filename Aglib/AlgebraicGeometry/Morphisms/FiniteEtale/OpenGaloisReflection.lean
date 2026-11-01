/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Morphisms.FiniteEtale.GenericGaloisReflection
public import Aglib.AlgebraicGeometry.Morphisms.FiniteEtale.BaseChange.Isomorphism
public import Aglib.AlgebraicGeometry.FunctionField.AffineCharts

/-! # Reflection from an original nonempty open restriction

Full faithfulness is obtained by cancelling the actual generic restriction
from its natural base-change comparison. The original fibre comparison then
reflects Galoisness and preserves deck order, without another generic model.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.PreGaloisCategory

namespace AlgebraicGeometry.Scheme.FiniteEtale

universe u

variable {X U : Scheme.{u}} [IsIntegral X] [IsIntegral U]
  [∀ x : X, IsIntegrallyClosed (X.presheaf.stalk x)]
  (j : U ⟶ X) [IsOpenImmersion j]

/-- Actual open restriction is full and faithful over a normal integral target. -/
theorem baseChange_open_full_faithful : (baseChange j).Full ∧ (baseChange j).Faithful := by
  let : IsDominant j := Scheme.isDominant_of_isOpenImmersion j
  let : ∀ z : U, IsIntegrallyClosed (U.presheaf.stalk z) := fun z =>
    IsIntegrallyClosed.of_equiv (asIso (j.stalkMap z)).commRingCatIsoToRingEquiv
  let s := Spec.map (CommRingCat.ofHom (functionFieldMap j))
  let : IsIso (CommRingCat.ofHom (functionFieldMap j)) := FunctionField.fieldMap_isIso j
  let : IsIso s := inferInstance
  let : (baseChange s).Full := baseChange_full_of_isIso s
  let : (baseChange s).Faithful := baseChange_faithful_of_isIso s
  let γU := U.fromSpecStalk (genericPoint U)
  let γX := X.fromSpecStalk (genericPoint X)
  let e : baseChange j ⋙ baseChange γU ≅ baseChange γX ⋙ baseChange s :=
    (baseChangeComp j γU).symm ≪≫
      eqToIso (congrArg baseChange (fromSpecStalk_genericPoint_naturality j)) ≪≫
      baseChangeComp γX s
  exact ⟨Functor.Full.of_comp_faithful_iso e, Functor.Faithful.of_comp_iso e⟩

include j

variable (Y : Scheme.FiniteEtale X) [ConnectedSpace Y.obj.left]
  [IsGalois ((baseChange j).obj Y)]

/-- Galoisness on the original open restriction reflects to the original cover. -/
theorem isGalois_of_open_baseChange : IsGalois Y := by
  let : (baseChange j).Full := (baseChange_open_full_faithful j).1
  let : (baseChange j).Faithful := (baseChange_open_full_faithful j).2
  let s := algebraicClosureResiduePoint U
    (Classical.choice (inferInstance : Nonempty U))
  let : IsConnected Y := Connectedness.categoricalConnected_of_connectedSpace Y
  exact isGalois_of_fiberCompatible_of_fullyFaithful
    (fiberToFinite (s ≫ j)) (fiberToFinite s) (baseChange j)
    (fiberToFiniteBaseChangeIso j s) Y

/-- The unchanged open restriction has the same original deck-group order. -/
theorem card_aut_open_baseChange :
    Nat.card (Aut ((baseChange j).obj Y)) = Nat.card (Aut Y) := by
  let : IsGalois Y := isGalois_of_open_baseChange j Y
  let s := algebraicClosureResiduePoint U
    (Classical.choice (inferInstance : Nonempty U))
  exact card_aut_obj_of_fiberCompatible
    (fiberToFinite (s ≫ j)) (fiberToFinite s) (baseChange j)
    (fiberToFiniteBaseChangeIso j s) Y

end AlgebraicGeometry.Scheme.FiniteEtale
