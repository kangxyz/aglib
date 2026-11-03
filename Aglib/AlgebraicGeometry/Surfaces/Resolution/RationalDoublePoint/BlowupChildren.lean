/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Surfaces.Resolution.RationalDoublePoint.BlowupSingularPoints
public import Aglib.AlgebraicGeometry.Surfaces.Resolution.RationalDoublePoint.PrefixResidue
public import Aglib.AlgebraicGeometry.Surfaces.RationalSingularities.Gorenstein.RationalPropagation
public import Aglib.AlgebraicGeometry.Surfaces.Birational.StalkNagata

/-!
# Actual singular child rings of rational surface models

The child is the original scheme stalk, with its original residue map.
Nagata follows by localizing an actual finite-type birational affine chart.
Universal rationality is the genuine stalk-propagation theorem. Neither
completeness nor finiteness over the base is asserted for the child ring.
-/

@[expose] public noncomputable section

open CategoryTheory TopologicalSpace

universe u

namespace AlgebraicGeometry.Scheme.RationalSingularities

/-- Every actual stalk of a finite-type birational integral model over a
Nagata surface base is Nagata, using its original adapted affine chart. -/
theorem stalk_isNagataRing_of_birational_surface
    (A : Type u) [CommRing A] [IsDomain A]
    (hA : IsNagataRing.{u, 0} A) (hdA : ringKrullDim A ≤ 2)
    {X : Scheme.{u}} [IsIntegral X]
    (f : X ⟶ Spec (.of A)) [LocallyOfFiniteType f] [IsDominant f]
    (hff : IsIso (CommRingCat.ofHom (functionFieldMap f))) (x : X) :
    IsNagataRing.{u, 0} (X.presheaf.stalk x) := by
  exact Scheme.stalk_isNagataRing_of_birational_surface A hA hdA f hff x

/-- A closed point on a proper model of a local base maps to the actual
closed point of that base. No residue-field identification is chosen. -/
theorem map_closedPoint_of_isProper
    (A : Type u) [CommRing A] [IsLocalRing A]
    {X : Scheme.{u}} (f : X ⟶ Spec (.of A)) [IsProper f]
    (x : X) (hx : IsClosed ({x} : Set X)) : f x = IsLocalRing.closedPoint A := by
  have hc : IsClosed ({f x} : Set (Spec (.of A))) := by
    simpa only [Set.image_singleton] using f.isClosedMap {x} hx
  have hm : (f x).asIdeal.IsMaximal :=
    (PrimeSpectrum.isClosed_singleton_iff_isMaximal (f x)).mp hc
  apply PrimeSpectrum.ext
  exact IsLocalRing.eq_maximalIdeal hm

/-- The singular actual stalk of a rational proper normal birational model
is a normal Noetherian Nagata local domain of dimension two and is itself
universally rational. Its original residue extension is finite. -/
theorem singular_stalk_properties_of_rational_model
    (A : Type u) [CommRing A] [IsDomain A] [IsLocalRing A] [IsNoetherianRing A]
    (hA : IsNagataRing.{u, 0} A) (hdA : ringKrullDim A = 2)
    (hRat : NormalModificationH1Vanishing A)
    {X : Scheme.{u}} [IsIntegral X]
    (f : X ⟶ Spec (.of A)) [IsProper f] [IsDominant f]
    (hX : NormalStalks X)
    (hff : IsIso (CommRingCat.ofHom (functionFieldMap f)))
    (x : X) (hx : ¬ IsRegularLocalRing (X.presheaf.stalk x)) :
    IsDomain (X.presheaf.stalk x) ∧ IsIntegrallyClosed (X.presheaf.stalk x) ∧
      IsNoetherianRing (X.presheaf.stalk x) ∧ IsNagataRing.{u, 0} (X.presheaf.stalk x) ∧
      ringKrullDim (X.presheaf.stalk x) = 2 ∧ IsClosed ({x} : Set X) ∧
      x ≠ genericPoint X ∧ f x = IsLocalRing.closedPoint A ∧
      (f.residueFieldMap x).hom.Finite ∧
      (letI : IsDomain (X.presheaf.stalk x) := (hX x).1
       NormalModificationH1Vanishing (X.presheaf.stalk x)) := by
  let : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian f
  have hdX : topologicalKrullDim X ≤ 2 :=
    Cohomology.actualModel_dimension_of_nagata f hA hdA.le hff
  have hclosed := isClosed_singleton_of_singular_of_normal_dimension_le_two X hX hdX x hx
  have hdim := stalk_dimension_eq_two_of_singular_of_normal_dimension_le_two X hX hdX x hx
  have hne : x ≠ genericPoint X := by
    intro he
    subst x
    change ¬ IsRegularLocalRing X.functionField at hx
    exact hx inferInstance
  refine ⟨(hX x).1, (hX x).2, inferInstance,
    stalk_isNagataRing_of_birational_surface A hA hdA.le f hff x,
    hdim, hclosed, hne, map_closedPoint_of_isProper A f x hclosed,
    NormalizedPointDomination.residueFieldMap_finite_of_closedPoint f x hclosed, ?_⟩
  exact normalModificationH1Vanishing_stalk_of_normalModificationH1Vanishing
    A hA hdA hRat f hX hff x hclosed hne

namespace MaximalIdealBlowup

/-- Actual singular children of the ordinary blowup of a complete rational
normal local surface have all local rational/Nagata surface properties.
The children are not assumed complete or finite over the original base. -/
theorem singular_child_properties_of_complete
    (A : Type u) [CommRing A] [IsLocalRing A] [IsDomain A]
    [IsNoetherianRing A] [IsIntegrallyClosed A]
    [IsAdicComplete (IsLocalRing.maximalIdeal A) A]
    (hd : ringKrullDim A = 2) (hRat : NormalModificationH1Vanishing A)
    (x : source A hd) (hx : ¬ IsRegularLocalRing ((source A hd).presheaf.stalk x)) :
    IsDomain ((source A hd).presheaf.stalk x) ∧
      IsIntegrallyClosed ((source A hd).presheaf.stalk x) ∧
      IsNoetherianRing ((source A hd).presheaf.stalk x) ∧
      IsNagataRing.{u, 0} ((source A hd).presheaf.stalk x) ∧
      ringKrullDim ((source A hd).presheaf.stalk x) = 2 ∧
      IsClosed ({x} : Set (source A hd)) ∧ x ≠ genericPoint (source A hd) ∧
      map A hd x = IsLocalRing.closedPoint A ∧
      ((map A hd).residueFieldMap x).hom.Finite ∧
      NormalModificationH1Vanishing ((source A hd).presheaf.stalk x) := by
  let : Ring.KrullDimLE 2 A := Ring.krullDimLE_iff.mpr hd.le
  have hN : IsNagataRing.{u, 0} A := IsNagataRing.of_complete_local_dimLE_two A
  exact singular_stalk_properties_of_rational_model A hN hd hRat (map A hd)
    (ordinary_normalStalks A hd hN hRat) (map_fieldMap_isIso A hd) x hx

end MaximalIdealBlowup
end AlgebraicGeometry.Scheme.RationalSingularities
