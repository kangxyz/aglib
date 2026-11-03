/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Surfaces.RationalSingularities.RegularTarget
public import Aglib.AlgebraicGeometry.Surfaces.Resolution.RationalDoublePoint.BlowupChildren
public import Aglib.AlgebraicGeometry.Surfaces.Birational.NormalizedPointDomination.AffineBase

/-!
# Actual rational domination of a supplied regular model

Original finite-type birational charts over a genuine Nagata base supply
Nagata of the regular target stalk. The existing normalized-point domination
then produces its actual chain and comparison, with universal H1 vanishing
at every singular original terminal stalk. The terminal is normal, not
asserted regular. No resolution-existence theorem is used.
-/

@[expose] public noncomputable section

open CategoryTheory TopologicalSpace

universe u

namespace AlgebraicGeometry.Scheme.RationalSingularities

/-- Genuine Nagata base geometry discharges the original target-stalk
hypothesis for rationality of an actual singular comparison-source stalk. -/
theorem normalModificationH1Vanishing_stalk_over_regular_model
    (A : Type u) [CommRing A] [IsDomain A]
    (hA : IsNagataRing.{u, 0} A) (hdA : ringKrullDim A ≤ 2)
    {T Y : Scheme.{u}} [IsIntegral T] [IsIntegral Y]
    (q : Y ⟶ Spec (.of A)) [IsProper q] [IsDominant q]
    (hY : RegularStalks Y)
    (hqff : IsIso (CommRingCat.ofHom (functionFieldMap q)))
    (a : T ⟶ Y) [IsProper a] [IsDominant a] (hT : NormalStalks T)
    (haff : IsIso (CommRingCat.ofHom (functionFieldMap a)))
    (x : T) (hx : ¬ IsRegularLocalRing (T.presheaf.stalk x)) :
    letI : IsDomain (T.presheaf.stalk x) := (hT x).1
    NormalModificationH1Vanishing (T.presheaf.stalk x) := by
  let : IsNoetherianRing A := hA.isNoetherianRing
  let : IsLocallyNoetherian Y := LocallyOfFiniteType.isLocallyNoetherian q
  have hdY : topologicalKrullDim Y ≤ 2 :=
    Cohomology.actualModel_dimension_of_nagata q hA hdA hqff
  have hdStalk : SurfaceDimensionAtMostTwo Y := by
    intro y
    rw [topologicalKrullDim_eq_iSup_stalk] at hdY
    exact (le_iSup (fun z : Y => ringKrullDim (Y.presheaf.stalk z)) y).trans hdY
  exact normalModificationH1Vanishing_stalk_of_regular_target a hT hY hdStalk haff x hx
    (stalk_isNagataRing_of_birational_surface A hA hdA q hqff (a x))

end AlgebraicGeometry.Scheme.RationalSingularities

namespace AlgebraicGeometry.Scheme.NormalizedPointDomination

/-- A supplied regular proper birational model over a normal Nagata base
of dimension at most two is dominated by the actual normalized-point chain,
whose singular original terminal stalks have universal H1 vanishing.
Terminal regularity and resolution existence are not conclusions. -/
theorem exists_rational_domination_of_regular_model
    (A : Type u) [CommRing A] [IsDomain A] [IsIntegrallyClosed A]
    (hA : IsNagataRing.{u, 0} A) (hdA : ringKrullDim A ≤ 2)
    {Y : Scheme.{u}} [IsIntegral Y]
    (q : Y ⟶ Spec (.of A)) [IsProper q] [IsDominant q]
    (hY : RegularStalks Y)
    (hqff : IsIso (CommRingCat.ofHom (functionFieldMap q))) :
    ∃ (T : Scheme.{u}) (beta : T ⟶ Spec (.of A)) (a : T ⟶ Y) (hT : IsIntegral T),
      letI := hT
      ∃ (hbeta : IsDominant beta) (ha : IsDominant a),
        letI := hbeta
        letI := ha
        ∃ (_ : Blowup.NormalizedPointBlowupChain beta),
          a ≫ q = beta ∧ NormalStalks T ∧ IsNoetherian T ∧ topologicalKrullDim T ≤ 2 ∧
            IsProper beta ∧ IsProper a ∧
            IsIso (CommRingCat.ofHom (functionFieldMap beta)) ∧
            IsIso (CommRingCat.ofHom (functionFieldMap a)) ∧
            ∀ x : T, ¬ IsRegularLocalRing (T.presheaf.stalk x) →
              RationalSingularities.NormalModificationH1Vanishing (T.presheaf.stalk x) := by
  obtain ⟨T, beta, a, hT, hbeta, ha, c, htriangle, hTN, hTNoeth, hdT, hbetaP, haP,
    hbetaff, haff⟩ := exists_domination_of_nagata_base A hA hdA q hqff
  let : IsIntegral T := hT
  let : IsDominant beta := hbeta
  let : IsDominant a := ha
  let : IsProper a := haP
  refine ⟨T, beta, a, hT, hbeta, ha, c, htriangle, hTN, hTNoeth, hdT,
    hbetaP, haP, hbetaff, haff, ?_⟩
  intro x hx
  exact RationalSingularities.normalModificationH1Vanishing_stalk_over_regular_model
    A hA hdA q hY hqff a hTN haff x hx

end AlgebraicGeometry.Scheme.NormalizedPointDomination
