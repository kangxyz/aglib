/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Properties.Regular.Basic
public import Mathlib.AlgebraicGeometry.Geometrically.Basic
public import Mathlib.AlgebraicGeometry.Pullbacks

/-!
# Geometrically regular fibers

A morphism is geometrically regular when every base change to a field has regular stalks.
This is a property of the geometric fibers; flatness is a separate hypothesis.

The generic stalk condition does not assert that the base-changed schemes are locally
Noetherian. Under a locally finite-type hypothesis, all these field base changes are locally
Noetherian, so this condition agrees with geometrically regular fibers in the usual sense.
-/

@[expose] public section

open CategoryTheory Limits

namespace AlgebraicGeometry

universe u

variable {X Y Z S : Scheme.{u}} (f : X ⟶ S) (g : Y ⟶ S)

/-- A morphism has geometrically regular fibers if every base change to a field has
regular actual local rings. -/
@[mk_iff]
class GeometricallyRegular (f : X ⟶ Y) : Prop where
  geometrically_regularStalks : geometrically Scheme.RegularStalks f

lemma GeometricallyRegular.eq_geometrically :
    @GeometricallyRegular = geometrically Scheme.RegularStalks := by
  ext
  exact geometricallyRegular_iff _

instance : MorphismProperty.IsStableUnderBaseChange @GeometricallyRegular :=
  GeometricallyRegular.eq_geometrically ▸ inferInstance

set_option backward.isDefEq.respectTransparency.types false in
instance [GeometricallyRegular g] : GeometricallyRegular (pullback.fst f g) :=
  MorphismProperty.pullback_fst f g inferInstance

set_option backward.isDefEq.respectTransparency.types false in
instance [GeometricallyRegular f] : GeometricallyRegular (pullback.snd f g) :=
  MorphismProperty.pullback_snd f g inferInstance

instance (V : S.Opens) [GeometricallyRegular f] : GeometricallyRegular (f ∣_ V) :=
  MorphismProperty.of_isPullback (isPullback_morphismRestrict ..).flip inferInstance

set_option backward.isDefEq.respectTransparency.types false in
instance (s : S) [GeometricallyRegular f] :
    GeometricallyRegular (f.fiberToSpecResidueField s) :=
  MorphismProperty.pullback_snd _ _ inferInstance

/-- Geometric regularity is equivalent to geometric regularity of all residue-field fibers. -/
lemma GeometricallyRegular.iff_forall_fiberToSpecResidueField (f : X ⟶ Y) :
    GeometricallyRegular f ↔ ∀ y, GeometricallyRegular (f.fiberToSpecResidueField y) := by
  refine ⟨fun h y ↦ ⟨?_⟩, fun h ↦ ⟨?_⟩⟩
  · exact (geometrically_iff_forall_fiberToSpecResidueField.mp
      h.geometrically_regularStalks) y
  · exact geometrically_iff_forall_fiberToSpecResidueField.mpr fun y ↦
      (h y).geometrically_regularStalks

/-- Every ordinary fiber of a geometrically regular morphism has regular actual stalks. -/
theorem GeometricallyRegular.regularStalks_fiber (f : X ⟶ Y) [GeometricallyRegular f]
    (y : Y) : Scheme.RegularStalks (f.fiber y) :=
  fiber_of_geometrically (GeometricallyRegular.geometrically_regularStalks (f := f)) y

/-- Restricting the source to an open subscheme preserves geometric regularity. -/
theorem GeometricallyRegular.comp_isOpenImmersion (i : X ⟶ Y) (f : Y ⟶ Z)
    [IsOpenImmersion i] [GeometricallyRegular f] : GeometricallyRegular (i ≫ f) := by
  rw [geometricallyRegular_iff, geometrically_iff_of_isClosedUnderIsomorphisms]
  intro K _ y
  let j : pullback (i ≫ f) y ⟶ pullback f y :=
    pullback.map (i ≫ f) y f y i (𝟙 _) (𝟙 _) (by simp) (by simp)
  have h : Scheme.RegularStalks (pullback f y) :=
    pullback_of_geometrically (GeometricallyRegular.geometrically_regularStalks (f := f)) K y
  exact h.of_isOpenImmersion j

end AlgebraicGeometry
