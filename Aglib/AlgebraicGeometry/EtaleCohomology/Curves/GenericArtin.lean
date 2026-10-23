/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.Picard.LocalRing
public import Mathlib.AlgebraicGeometry.Artinian
public import Mathlib.AlgebraicGeometry.Stalk
public import Mathlib.AlgebraicGeometry.Limits

/-!
# Actual generic Artin loci

The generic locus is the coproduct of spectra of the original stalk rings at
component-generic points. It retains generic nilpotents and does not identify
this ring with a localization at all nonzerodivisors. No reducedness,
irreducibility, smoothness or perfectness hypothesis is used.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace
open GroupCohomology.Kummer.Coefficients GroupCohomology.Kummer.CoefficientBaseChange

namespace AlgebraicGeometry.Scheme.EtaleCohomology.Curves

universe u w

variable (X : Scheme.{u})

/-- A component-generic point is maximal in the scheme's specialization order. -/
theorem genericPoint_isMax (η : genericPoints X) : IsMax η.val := by
  intro x hx
  change η.val ⤳ x
  exact specializes_iff_closure_subset.mpr
    (η.property.2 isIrreducible_singleton.closure hx.closure_subset)

/-- The actual stalk ring at a component-generic point has dimension zero. -/
theorem genericStalk_krullDimLE_zero (η : genericPoints X) :
    Ring.KrullDimLE 0 (X.presheaf.stalk η.val) :=
  krullDimLE_of_coheight_le (Order.coheight_eq_zero.mpr (genericPoint_isMax X η)).le

/-- A locally Noetherian scheme has Artin local rings at its component-generic points. -/
instance genericStalk_isArtinian [IsLocallyNoetherian X] (η : genericPoints X) :
    IsArtinianRing (X.presheaf.stalk η.val) :=
  isArtinianRing_iff_krullDimLE_zero.mpr (genericStalk_krullDimLE_zero X η)

/-- There are finitely many component-generic points on a Noetherian scheme. -/
instance genericPoints_finite [IsNoetherian X] : Finite (genericPoints X) :=
  (genericPoints.finite NoetherianSpace.finite_irreducibleComponents).to_subtype

/-- One genuine generic infinitesimal neighborhood, using its original stalk. -/
abbrev genericArtinComponent (η : genericPoints X) : Scheme.{u} :=
  Spec (X.presheaf.stalk η.val)

/-- The actual coproduct of all component-generic infinitesimal neighborhoods. -/
def genericArtinLocus : Scheme.{u} :=
  ∐ (genericArtinComponent X)

/-- Its original scheme map to X, induced by the canonical stalk morphisms. -/
def genericArtinMap : genericArtinLocus X ⟶ X :=
  Sigma.desc (fun η : genericPoints X => X.fromSpecStalk η.val)

/-- Restriction on each component is exactly the original stalk morphism. -/
@[simp, reassoc]
theorem genericArtinMap_component (η : genericPoints X) :
    Sigma.ι (genericArtinComponent X) η ≫ genericArtinMap X = X.fromSpecStalk η.val :=
  Sigma.ι_comp_desc _ _

/-- The image of a generic infinitesimal neighborhood is its actual generic point. -/
theorem genericArtinComponent_range (η : genericPoints X) :
    Set.range (X.fromSpecStalk η.val) = {η.val} := by
  rw [Scheme.range_fromSpecStalk]
  ext x
  change (x ⤳ η.val) ↔ x = η.val
  constructor
  · intro hx
    exact (hx.antisymm (genericPoint_isMax X η hx)).eq
  · rintro rfl
    exact specializes_rfl

/-- Literal restriction of function units to the generic Artin locus. -/
def genericArtinUnit : gm X ⟶ (directImage (genericArtinMap X)).obj (gm (genericArtinLocus X)) :=
  gmUnit (genericArtinMap X)

/-- Original multiplicative H1 vanishes on every generic Artin component. -/
instance genericArtinComponent_gmH1_subsingleton (η : genericPoints X)
    [HasExt.{w} (AbelianSheaf.{u, u + 1} (genericArtinComponent X η))] :
    Subsingleton (Sheaf.H.{w} (gm (genericArtinComponent X η)) 1) :=
  Picard.gmH1_subsingleton_of_isLocalRing (X.presheaf.stalk η.val)

end AlgebraicGeometry.Scheme.EtaleCohomology.Curves
