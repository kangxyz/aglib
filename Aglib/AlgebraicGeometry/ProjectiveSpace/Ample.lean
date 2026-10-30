/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.ProjectiveSpace.PrincipalOpen
public import Aglib.AlgebraicGeometry.ProjectiveSpace.QuasiProjective
public import Aglib.AlgebraicGeometry.Modules.Invertible.Ample.Basic

/-!
# The original projective twisting line bundle is ample

The intrinsic nonvanishing open of the original homogeneous coordinate
section of `O(1)` is exactly its standard affine coordinate chart. Those
sections witness ampleness of the existing twisting line bundle. Pullback
along a projective closed embedding then supplies an actual ample line
bundle, using the same ampleness predicate and tensor powers.
-/

@[expose] public noncomputable section

open CategoryTheory Opposite TopologicalSpace
open AlgebraicGeometry.Scheme.Modules.Invertible

universe u

namespace AlgebraicGeometry.ProjectiveSpace

variable (R : Type u) [CommRing R] (ι : Type u)

-- The original twisting sheaf and its LineBundle section carrier agree
-- below the default transparency used by the nonvanishing rewrite.
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- The intrinsic nonvanishing open of the actual coordinate section of
`O(1)` is the original standard affine chart. -/
theorem nonvanishingOpen_homogeneousCoordinate (i : ι) :
    nonvanishingOpen (twistingLineBundle R ι 1)
      (homogeneousSection R ι 1 (coordinatePower R ι 1 i)) = coordinateOpen R ι i := by
  have hinter (j : ι) : coordinateOpen R ι j ⊓
      nonvanishingOpen (twistingLineBundle R ι 1)
        (homogeneousSection R ι 1 (coordinatePower R ι 1 i)) =
      coordinateOpen R ι j ⊓ coordinateOpen R ι i := by
    rw [inter_nonvanishingOpen (twistingLineBundle R ι 1) _
      (coordinateOpen R ι j) (twistingLocalIso R ι 1 j)]
    change (ProjectiveSpace R ι).basicOpen
      (twistingSectionsEquiv R ι 1 j le_rfl
        ((twistingSheaf R ι 1).val.map (homOfLE le_top).op
          (homogeneousSection R ι 1 (coordinatePower R ι 1 i)))) = _
    have hc := homogeneousSection_local R ι 1 (coordinatePower R ι 1 i) j
    have hr := coordinateRatioSection_eq_homogeneousChartSection R ι j i
    exact (congrArg (fun s : Γ(ProjectiveSpace R ι, coordinateOpen R ι j) =>
      (ProjectiveSpace R ι).basicOpen s) hc).trans
      ((congrArg (fun s : Γ(ProjectiveSpace R ι, coordinateOpen R ι j) =>
        (ProjectiveSpace R ι).basicOpen s) hr.symm).trans
          (basicOpen_coordinateRatioSection R ι j i))
  calc
    _ = (⨆ j, coordinateOpen R ι j) ⊓ _ := by
      rw [iSup_coordinateOpen_eq_top, top_inf_eq]
    _ = ⨆ j, coordinateOpen R ι j ⊓ coordinateOpen R ι i := by
      rw [iSup_inf_eq]
      exact iSup_congr hinter
    _ = coordinateOpen R ι i := by
      rw [← iSup_inf_eq, iSup_coordinateOpen_eq_top, top_inf_eq]

-- Tensor-power class transport retains the original global section;
-- its native sheaf and module carriers must unfold at this boundary.
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- The actual `O(1)` on finite-coordinate projective space is ample in
the intrinsic affine-nonvanishing-open sense, over every commutative ring. -/
theorem twistingLineBundle_one_isAmple [Finite ι] :
    (twistingLineBundle R ι 1).IsAmple := by
  let L := twistingLineBundle R ι 1
  have hclass : classOf (ProjectiveSpace R ι) L =
      classOf (ProjectiveSpace R ι) (tensorPowerLineBundle (ProjectiveSpace R ι) L 1) := by
    rw [classOf_tensorPower, one_smul]
  obtain ⟨e⟩ := (class_eq_iff (ProjectiveSpace R ι) _ _).mp hclass
  refine ⟨QuasiCompact.compactSpace_of_compactSpace (toSpec R ι), ?_⟩
  intro x
  obtain ⟨i, hi⟩ := Opens.mem_iSup.mp (show x ∈ ⨆ i, coordinateOpen R ι i by
    rw [iSup_coordinateOpen_eq_top]
    trivial)
  let s := homogeneousSection R ι 1 (coordinatePower R ι 1 i)
  refine ⟨1, Nat.zero_lt_one, e.hom.val.app (op ⊤) s, ?_, ?_⟩
  · rw [nonvanishingOpen_iso, nonvanishingOpen_homogeneousCoordinate]
    exact isAffineOpen_coordinateOpen R ι i
  · rw [nonvanishingOpen_iso, nonvanishingOpen_homogeneousCoordinate]
    exact hi

/-- A closed embedding into the original finite-coordinate projective
space supplies an ample line bundle by pulling back its actual `O(1)`. -/
theorem pullback_twistingLineBundle_one_isAmple [Finite ι]
    {X : Scheme.{u}} (i : X ⟶ ProjectiveSpace R ι) [IsClosedImmersion i] :
    (pullbackLineBundle i (twistingLineBundle R ι 1)).IsAmple :=
  (twistingLineBundle_one_isAmple R ι).pullback_of_isAffineHom i

end AlgebraicGeometry.ProjectiveSpace

namespace AlgebraicGeometry

/-- An actual projective scheme over an affine base has an ample line
bundle. Its projective embedding is chosen only inside the proof. -/
theorem IsHProjective.exists_isAmple {R : CommRingCat.{u}} {X : Scheme.{u}}
    (p : X ⟶ Spec R) [IsHProjective p] :
    ∃ L : Scheme.Modules.Invertible.LineBundle X, L.IsAmple := by
  obtain ⟨ι, hι, i, hi, _⟩ := IsHProjective.exists_isClosedImmersion (f := p)
  let := hι
  let := hi
  exact ⟨pullbackLineBundle i (ProjectiveSpace.twistingLineBundle R ι 1),
    ProjectiveSpace.pullback_twistingLineBundle_one_isAmple R ι i⟩

end AlgebraicGeometry
