/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Morphisms.FiniteEtale.Lifting
public import Aglib.AlgebraicGeometry.Morphisms.FiniteEtale.ResidueFiber
public import Aglib.AlgebraicGeometry.Morphisms.Etale.StalkMap
public import Aglib.AlgebraicGeometry.Properties.Regular.Basic
public import Aglib.AlgebraicGeometry.Properties.Normal.Components
public import Aglib.RingTheory.RegularLocalRing.Normal

/-!
# Geometry of the unchanged finite-etale covering source

Actual etale stalk comparison and regular-local algebra supply the original
regularity and normal-stalk conclusions. On a locally Noetherian target,
connectedness of the same covering scheme then gives integrality. The literal
source residue fibre is connected when the supplied actual comparison
preserves connectedness. No generic connectedness, model existence or purity
statement is inferred.

Source: unmarked slices `GeneralLift:321–341` and `SourceModel:115–193` in
`R5Lab.AlgebraicGeometry.Curves.LocalModels.CyclicCovers`, R5
`f8a3314ddecffcada2ec721d26d56a937bed9690`, SHA-256 respectively
`e62cfc4cb7711bac753202a8bcf27fbf4f11a52cf87ccf144ffb6df9b5671075` and
`bb898d7efd9798cb5657bffab1cf0ad44d163ab82a1823b05aa0daad889c2fae`.
Proved native suppliers replace the source's universal etale-regularity,
regular-local-normality and normal-component-openness inputs on the same stalks.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u

namespace AlgebraicGeometry.Scheme.FiniteEtale.Lifting

variable {Y : Scheme.{u}} (C : FiniteEtale Y)

/-- Etaleness transports the given target's regularity to the actual source
stalks by the existing stalk-map theorem. -/
theorem regularStalks (hY : RegularStalks Y) : RegularStalks C.obj.left := by
  intro x
  let : IsRegularLocalRing (Y.presheaf.stalk (C.obj.hom x)) := hY _
  exact Scheme.isRegularLocalRing_stalk_of_etale C.obj.hom x

/-- The same regular source stalks are domains and integrally closed by the
proved regular-local ring theorems. -/
theorem normalStalks (hY : RegularStalks Y) : NormalStalks C.obj.left := by
  intro x
  let : IsRegularLocalRing (C.obj.left.presheaf.stalk x) := regularStalks C hY x
  exact ⟨IsRegularLocalRing.isDomain_of_regularLocal _,
    IsRegularLocalRing.isIntegrallyClosed_of_regularLocal _⟩

/-- A connected cover of the same locally Noetherian regular target is
integral, without changing the covering scheme. -/
theorem isIntegral [IsLocallyNoetherian Y] [ConnectedSpace C.obj.left]
    (hY : RegularStalks Y) : IsIntegral C.obj.left := by
  let : IsLocallyNoetherian C.obj.left :=
    LocallyOfFiniteType.isLocallyNoetherian C.obj.hom
  exact Scheme.isIntegral_of_connected_normalStalks_actual _ (normalStalks C hY)

end AlgebraicGeometry.Scheme.FiniteEtale.Lifting

namespace AlgebraicGeometry.Scheme.LocalRing.ResidueFiber

variable {R : Type u} [CommRing R] [IsLocalRing R] {X Y : Scheme.{u}}
  (πX : X ⟶ Spec (.of R)) (πY : Y ⟶ Spec (.of R))
  (p : X ⟶ Y) [IsFinite p] [Etale p] (hp : p ≫ πY = πX)
  [(Scheme.FiniteEtale.baseChange (projection πY)).IsEquivalence]
  [ConnectedSpace X]

include πY p hp in
/-- The original source's literal residue fibre is connected by the actual
restriction equivalence and the same two-projection comparison. -/
theorem connectedSpace_of_equivalence : ConnectedSpace (obj πX) := by
  let C : Scheme.FiniteEtale Y := Scheme.FiniteEtale.mk p
  let : ConnectedSpace C.obj.left := by
    change ConnectedSpace X
    infer_instance
  have h := Scheme.FiniteEtale.Lifting.connectedSpace_obj (projection πY) C
  change ConnectedSpace (pullback p (projection πY) : Scheme.{u}) at h
  exact (comparisonIso πX πY p hp).hom.homeomorph.connectedSpace_iff.mpr h

end AlgebraicGeometry.Scheme.LocalRing.ResidueFiber
