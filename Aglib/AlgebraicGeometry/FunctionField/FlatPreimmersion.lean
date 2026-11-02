/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.FunctionField.Map
public import Aglib.AlgebraicGeometry.Stalk.FlatBaseChange

/-!
# Actual function fields of dominant flat preimmersions

The original generic-stalk map is invertible. This proof is extracted once
from `Descent.LocalModification.GenericNormalization`, with its public name
and complete telescope preserved. No normalization or surface theory is used.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits TopologicalSpace

universe u

namespace AlgebraicGeometry.Scheme

/-- A dominant flat preimmersion identifies the original generic stalks,
and hence its actual function-field homomorphism. -/
theorem functionFieldMap_isIso_of_flat_preimmersion
    {Y X : Scheme.{u}} [IsIntegral Y] [IsIntegral X]
    (g : Y ⟶ X) [IsDominant g] [Flat g] [IsPreimmersion g] :
    IsIso (CommRingCat.ofHom (Scheme.functionFieldMap g)) := by
  let : IsIso (g.stalkMap (genericPoint Y)) :=
    Hom.isIso_stalkMap_of_flat_of_surjectiveOnStalks g (genericPoint Y)
  change IsIso (X.presheaf.stalkSpecializes _ ≫ g.stalkMap (genericPoint Y))
  have he : X.presheaf.stalkSpecializes
      (specializes_of_eq (Scheme.map_genericPoint_of_isDominant Y g)) =
      (X.presheaf.stalkCongr (.of_eq
        (Scheme.map_genericPoint_of_isDominant Y g).symm)).hom := rfl
  rw [he]
  infer_instance

end AlgebraicGeometry.Scheme
