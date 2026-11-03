/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Blowup.Arc.MarkedPath
public import Aglib.AlgebraicGeometry.Surfaces.Birational.NormalizedPointDomination.ResidueTranscendence

/-!
# Original residue extensions along a closed-point blowup path

Every original transition has finite residue extension because the blowdown
is locally of finite type and its selected source point is closed. The
original finite-prefix map is therefore finite on residue fields, even
before a marked tail has been reached. No prefix residue isomorphism is
inferred from a marking on a later tail.
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry IsLocalRing

universe u

namespace AlgebraicGeometry.Scheme.Blowup.Arc

/-- Transporting the target point of the original stalk map preserves the
finite residue extension at a closed source point. -/
theorem pointLocalRingMap_residue_finite
    {X Y : Scheme.{u}} (f : X ⟶ Y) [LocallyOfFiniteType f]
    (x : X) (hx : IsClosed ({x} : Set X)) (y : Y) (h : f x = y) :
    (ResidueField.map (pointLocalRingMap f x y h).hom).Finite := by
  subst y
  have hid : (pointStalkIso Y (rfl : f x = f x)).inv =
      𝟙 (Y.presheaf.stalk (f x)) := by
    change Y.presheaf.stalkSpecializes (specializes_refl (f x)) = _
    exact TopCat.Presheaf.stalkSpecializes_refl Y.presheaf (f x)
  change (ResidueField.map
    (((pointStalkIso Y (rfl : f x = f x)).inv ≫ f.stalkMap x).hom)).Finite
  have hfinite := NormalizedPointDomination.residueFieldMap_finite_of_closedPoint f x hx
  change (ResidueField.map (f.stalkMap x).hom).Finite at hfinite
  simpa only [hid, Category.id_comp] using hfinite

namespace ClosedPointBlowupPath

variable (P : ClosedPointBlowupPath.{u})

/-- Each actual ordinary blowdown has a finite original residue extension at
its selected closed source point, without an unchanged-residue assumption. -/
theorem transition_residue_finite (n : ℕ) :
    (ResidueField.map (P.transition n).hom).Finite := by
  let : IsProper (P.down n) := (P.datum n).isProper_of_isLocallyNoetherian
  exact pointLocalRingMap_residue_finite (P.down n) (P.point (n + 1))
    (P.point_closed (n + 1)) (P.point n) (P.point_down n)

/-- Finiteness belongs to the original full-prefix residue map, including
all transitions before a subsequently chosen marked tail. -/
theorem scalar_residue_finite (n : ℕ) :
    (ResidueField.map (P.scalar n).hom).Finite :=
  P.scalar_residue_finite_of_transition P.transition_residue_finite n

/-- The original complete-base marked-tail theorem needs no additional
prefix residue hypothesis: closedness and finite type supply it. The
actual tail marking, normality and dimension hypotheses remain explicit. -/
theorem exists_regular_marked_tail_of_complete_base
    (r : ℕ) (M : (P.tail r).Marking)
    [IsAdicComplete (maximalIdeal (P.localRing 0)) (P.localRing 0)]
    [IsIntegrallyClosed (P.localRing r)]
    (hd0 : ringKrullDim (P.localRing 0) = 2)
    (hdr : ringKrullDim (P.localRing r) = 2) :
    ∃ n : ℕ, IsRegularLocalRing (P.localRing (r + n)) :=
  P.exists_regular_tail_of_complete_base r M hd0 hdr (P.scalar_residue_finite r)

end ClosedPointBlowupPath
end AlgebraicGeometry.Scheme.Blowup.Arc
