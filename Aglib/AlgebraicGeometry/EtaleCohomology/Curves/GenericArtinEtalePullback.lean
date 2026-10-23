/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.Curves.GenericArtin
public import Aglib.AlgebraicGeometry.Stalk.FlatBaseChange
public import Aglib.AlgebraicGeometry.Morphisms.Etale.QuasiFinite

/-!
# Actual etale pullbacks of generic Artin components

A quasi-compact etale test has an actual Artinian pullback over each generic
stalk spectrum. Its original projection to the test induces isomorphisms on
all stalks, by the native flat-preimmersion theorem. No reducedness or
function-field replacement enters this comparison.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace

namespace AlgebraicGeometry.Scheme.EtaleCohomology.Curves

universe u

variable {U X : Scheme.{u}} (f : U ⟶ X) (η : genericPoints X)

/-- The actual pullback of one generic infinitesimal component to the etale test. -/
abbrev genericEtaleComponent : Scheme.{u} := pullback f (X.fromSpecStalk η.val)

/-- The actual projection to the test is a flat preimmersion. -/
theorem genericEtaleComponent_flat : Flat (pullback.fst f (X.fromSpecStalk η.val)) := by
  let : Flat (X.fromSpecStalk η.val) := Scheme.fromSpecStalk_flat X η.val
  infer_instance

/-- Each original projection stalk map is an isomorphism, including nilpotents. -/
theorem genericEtaleComponent_stalkMap_isIso (p : genericEtaleComponent f η) :
    IsIso ((pullback.fst f (X.fromSpecStalk η.val)).stalkMap p) := by
  let : Flat (pullback.fst f (X.fromSpecStalk η.val)) := genericEtaleComponent_flat f η
  exact Scheme.Hom.isIso_stalkMap_of_flat_of_surjectiveOnStalks _ p

/-- Original test stalk and actual generic pullback stalk, via the projection's own map. -/
def genericEtaleComponentStalkIso (p : genericEtaleComponent f η) :
    U.presheaf.stalk ((pullback.fst f (X.fromSpecStalk η.val)) p) ≅
      (genericEtaleComponent f η).presheaf.stalk p := by
  let := genericEtaleComponent_stalkMap_isIso f η p
  exact asIso ((pullback.fst f (X.fromSpecStalk η.val)).stalkMap p)

/-- Quasi-compact etale generic pullbacks are Artinian, not merely reduced finite fibres. -/
theorem genericEtaleComponent_isArtinian [IsLocallyNoetherian X] [Etale f]
    [QuasiCompact f] : IsArtinianScheme (genericEtaleComponent f η) := by
  let : IsLocallyArtinian (Spec (X.presheaf.stalk η.val)) :=
    Scheme.isLocallyArtinianScheme_Spec.mpr (genericStalk_isArtinian X η)
  exact {
    toIsLocallyArtinian := IsLocallyArtinian.of_locallyQuasiFinite
      (pullback.snd f (X.fromSpecStalk η.val))
    toCompactSpace := QuasiCompact.compactSpace_of_compactSpace
      (pullback.snd f (X.fromSpecStalk η.val)) }

/-- The actual generic pullback has finitely many infinitesimal points. -/
theorem genericEtaleComponent_finite [IsLocallyNoetherian X] [Etale f] [QuasiCompact f] :
    Finite (genericEtaleComponent f η) := by
  let := genericEtaleComponent_isArtinian f η
  infer_instance

end AlgebraicGeometry.Scheme.EtaleCohomology.Curves
