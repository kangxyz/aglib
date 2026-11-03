/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Surfaces.Birational.IsomorphismLocus
public import Aglib.RingTheory.DiscreteValuationRing.DimensionOne

/-!
# Original singular points on normal surfaces

Normal Noetherian local rings of dimension at most one are regular.
The original coheight bound makes nonclosed points on a normal surface
regular. Actual singular points are therefore closed and their original
stalks have dimension two. These four generic bodies have one lower owner;
complete-base finite singular sets remain in their existing higher consumer.
-/

@[expose] public noncomputable section

open CategoryTheory TopologicalSpace

universe u

namespace AlgebraicGeometry.Scheme

/-- Normality and dimension at most one imply regularity of the actual stalk. -/
theorem regular_at_of_normal_of_stalk_dimension_le_one
    (X : Scheme.{u}) [IsLocallyNoetherian X] (hX : NormalStalks X) (x : X)
    (hd : ringKrullDim (X.presheaf.stalk x) ≤ 1) :
    IsRegularLocalRing (X.presheaf.stalk x) := by
  let R := X.presheaf.stalk x
  let : IsDomain R := (hX x).1
  let : IsIntegrallyClosed R := (hX x).2
  by_cases hf : IsField R
  · let := hf.toField
    exact inferInstanceAs (IsRegularLocalRing R)
  · let : IsDiscreteValuationRing R :=
      IsDiscreteValuationRing.of_isIntegrallyClosed_of_dimLE_one R hd hf
    exact inferInstanceAs (IsRegularLocalRing R)

/-- Every nonclosed point of a normal Noetherian surface is regular, without
any Jacobson, separatedness or global coefficient-field hypothesis. -/
theorem regular_at_nonclosed_of_normal_dimension_le_two
    (X : Scheme.{u}) [IsLocallyNoetherian X] (hX : NormalStalks X)
    (hdim : topologicalKrullDim X ≤ 2) (x : X)
    (hx : ¬ IsClosed ({x} : Set X)) : IsRegularLocalRing (X.presheaf.stalk x) := by
  have hc := coheight_le_one_of_not_isClosed_singleton_of_dimension_le_two X hdim x hx
  let : Ring.KrullDimLE 1 (X.presheaf.stalk x) := krullDimLE_of_coheight_le hc
  exact regular_at_of_normal_of_stalk_dimension_le_one X hX x
    (Ring.krullDimLE_iff.mp inferInstance)

/-- A singular point on the original normal surface is a closed scheme point. -/
theorem isClosed_singleton_of_singular_of_normal_dimension_le_two
    (X : Scheme.{u}) [IsLocallyNoetherian X] (hX : NormalStalks X)
    (hdim : topologicalKrullDim X ≤ 2) (x : X)
    (hx : ¬ IsRegularLocalRing (X.presheaf.stalk x)) : IsClosed ({x} : Set X) := by
  by_contra hn
  exact hx (regular_at_nonclosed_of_normal_dimension_le_two X hX hdim x hn)

/-- A singular actual stalk on a normal surface has dimension exactly two. -/
theorem stalk_dimension_eq_two_of_singular_of_normal_dimension_le_two
    (X : Scheme.{u}) [IsLocallyNoetherian X] (hX : NormalStalks X)
    (hdim : topologicalKrullDim X ≤ 2) (x : X)
    (hx : ¬ IsRegularLocalRing (X.presheaf.stalk x)) :
    ringKrullDim (X.presheaf.stalk x) = 2 := by
  have hle : ringKrullDim (X.presheaf.stalk x) ≤ 2 :=
    (le_iSup (fun y : X => ringKrullDim (X.presheaf.stalk y)) x).trans
      ((topologicalKrullDim_eq_iSup_stalk X).symm.le.trans hdim)
  by_contra hne
  have hlt : ringKrullDim (X.presheaf.stalk x) < 2 := lt_of_le_of_ne hle hne
  have hsmall : ringKrullDim (X.presheaf.stalk x) ≤ 1 :=
    (ENat.WithBot.lt_add_one_iff (m := 1)).mp (by
      convert hlt using 1
      norm_num)
  exact hx (regular_at_of_normal_of_stalk_dimension_le_one X hX x hsmall)

end AlgebraicGeometry.Scheme
