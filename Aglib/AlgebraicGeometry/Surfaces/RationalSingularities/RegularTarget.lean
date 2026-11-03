/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Stalk.ModelLocalization
public import Aglib.AlgebraicGeometry.FunctionField.LocalSpectrum.BaseChange
public import Aglib.AlgebraicGeometry.Surfaces.RationalSingularities.RingEquiv
public import Aglib.AlgebraicGeometry.Surfaces.RationalSingularities.Gorenstein.RationalPropagation
public import Aglib.AlgebraicGeometry.Normalization.FunctionField.FlatPreimmersion
public import Aglib.AlgebraicGeometry.Morphisms.Proper.BirationalSurface
public import Aglib.AlgebraicGeometry.Properties.Regular.OpenCover
public import Aglib.AlgebraicGeometry.Surfaces.Resolution.RationalDoublePoint.ClosedSingularPoints

/-!
# Rationality of singular original stalks over a regular target

The singular point excludes the original target isomorphism locus, forcing
the actual target stalk to have dimension two. Localize the original proper
birational model at that stalk, derive its normality and dimension, and use
local rationality propagation at the actual closed singular lift. The
original stalk-arrow isomorphism transports vanishing back to the original
source stalk. Nagata of the original target stalk remains explicit; it is
not inferred merely from regularity.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits TopologicalSpace

universe u

namespace AlgebraicGeometry.Scheme.RationalSingularities

/-- A singular original stalk of a normal proper birational model over a
regular surface is universally H1-vanishing when its original target stalk
is Nagata. Closedness is derived on the literal localized model. -/
theorem normalModificationH1Vanishing_stalk_of_regular_target
    {T Y : Scheme.{u}} [IsIntegral T] [IsIntegral Y] [IsLocallyNoetherian Y]
    (a : T ⟶ Y) [IsProper a] [IsDominant a]
    (hT : NormalStalks T) (hY : RegularStalks Y)
    (hdY : SurfaceDimensionAtMostTwo Y)
    (hff : IsIso (CommRingCat.ofHom (functionFieldMap a)))
    (x : T) (hx : ¬ IsRegularLocalRing (T.presheaf.stalk x))
    (hNagata : IsNagataRing.{u, 0} (Y.presheaf.stalk (a x))) :
    letI : IsDomain (T.presheaf.stalk x) := (hT x).1
    NormalModificationH1Vanishing (T.presheaf.stalk x) := by
  let : IsDomain (T.presheaf.stalk x) := (hT x).1
  have hYN : NormalStalks Y := by
    intro y
    let : IsRegularLocalRing (Y.presheaf.stalk y) := hY y
    exact ⟨IsRegularLocalRing.isDomain_of_regularLocal _,
      IsRegularLocalRing.isIntegrallyClosed_of_regularLocal _⟩
  have hout : a x ∉ a.targetIsomorphismLocus := by
    intro hin
    let U := a.targetIsomorphismLocus
    let : IsIso (a ∣_ U) := a.isIso_restrict_targetIsomorphismLocus
    have hU : RegularStalks U.toScheme := hY.of_isOpenImmersion U.ι
    have hV : RegularStalks (a ⁻¹ᵁ U).toScheme := hU.of_isOpenImmersion (a ∣_ U)
    exact hx (RegularStalks.at_image (a ⁻¹ᵁ U).ι hV ⟨x, hin⟩)
  have hd : ringKrullDim (Y.presheaf.stalk (a x)) = 2 :=
    a.ringKrullDim_stalk_eq_two_of_not_mem_targetIsomorphismLocus hff hYN hdY (a x) hout
  let A := Y.presheaf.stalk (a x)
  let : IsRegularLocalRing A := hY (a x)
  let s := Y.fromSpecStalk (a x)
  let P := pullback a s
  let j : P ⟶ T := pullback.fst a s
  let p : P ⟶ Spec A := pullback.snd a s
  let : Flat s := fromSpecStalk_flat Y (a x)
  let : IsIntegral P := isIntegral_pullback_fromSpecStalk a (a x)
  let : IsDominant j := isDominant_pullback_fst_fromSpecStalk a (a x)
  let : IsDominant s := LocalModification.fromSpecStalk_isDominant Y (a x)
  let : IsProper p := inferInstance
  let : IsDominant p := inferInstance
  have hpff : IsIso (CommRingCat.ofHom (functionFieldMap p)) :=
    functionFieldMap_isIso_of_isPullback_fromSpecStalk a (a x) j p
      (IsPullback.of_hasPullback a s) hff
  have hP : NormalStalks P := normalStalks_pullback_fromSpecStalk a (a x) hT
  let : IsLocallyNoetherian P := LocallyOfFiniteType.isLocallyNoetherian p
  have hdP : topologicalKrullDim P ≤ 2 :=
    Cohomology.actualModel_dimension_of_nagata p hNagata hd.le hpff
  obtain ⟨z, hz, _⟩ := Scheme.Pullback.exists_preimage_pullback (f := a) (g := s) x
    (IsLocalRing.closedPoint A)
    (Scheme.fromSpecStalk_closedPoint (X := Y) (x := a x)).symm
  let E : Arrow.mk (a.stalkMap x) ≅ Arrow.mk (p.stalkMap z) :=
    Hom.stalkMapIsoOfIsPullbackOfFlatOfPreimmersion
      (IsPullback.of_hasPullback a s) z x hz
  let e : (T.presheaf.stalk x) ≃+* (P.presheaf.stalk z) :=
    (Arrow.rightFunc.mapIso E).commRingCatIsoToRingEquiv
  have hsing : ¬ IsRegularLocalRing (P.presheaf.stalk z) := by
    intro h
    let : IsRegularLocalRing (P.presheaf.stalk z) := h
    exact hx (IsRegularLocalRing.of_ringEquiv e.symm)
  have hzclosed : IsClosed ({z} : Set P) :=
    isClosed_singleton_of_singular_of_normal_dimension_le_two P hP hdP z hsing
  have hzne : z ≠ genericPoint P := by
    intro he
    subst z
    change ¬ IsRegularLocalRing P.functionField at hsing
    exact hsing inferInstance
  have hRatA : NormalModificationH1Vanishing A :=
    normalModificationH1Vanishing_of_regularLocal A hd
  have hRatP : NormalModificationH1Vanishing (P.presheaf.stalk z) :=
    normalModificationH1Vanishing_stalk_of_normalModificationH1Vanishing
      A hNagata hd hRatA p hP hpff z hzclosed hzne
  exact (normalModificationH1Vanishing_iff_of_ringEquiv e).mpr hRatP

end AlgebraicGeometry.Scheme.RationalSingularities
