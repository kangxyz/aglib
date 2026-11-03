/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Cohomology.ClosedImmersion.RightAdjoint.FlatBaseChange.QuotientChart
public import Aglib.AlgebraicGeometry.ProjectiveSpace.BaseChange.ChartPullback
public import Mathlib.AlgebraicGeometry.Cover.Open

/-!
# The original projective field-extension quotient cover

Choose each source quotient chart once, independently of the extension field.
The accepted mapped-ideal construction supplies the target charts and both
Cartesian squares. Native cover transport retains their literal objects and
maps; it does not assume any local canonical-module comparison.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry.ProjectiveSpace

universe u

namespace AlgebraicGeometry.Scheme.Modules

attribute [local instance] MvPolynomial.gradedAlgebra

/-- Select the original source quotient chart once. The extension field is
not a parameter of this choice. -/
def projectiveSourceQuotientChart (k : Type u) [Field k] (ι : Type u)
    {C : Scheme.{u}} (j : C ⟶ ProjectiveSpace k ι) [IsClosedImmersion j] (i : ι) :
    ClosedImmersionAffineQuotientChart j (.of (coordinateRing k ι i))
      ((coordinateAffineOpenCover k ι).f i) :=
  @closedImmersionAffineQuotientChart C (ProjectiveSpace k ι) j inferInstance
    (.of (coordinateRing k ι i)) ((coordinateAffineOpenCover k ι).f i)
    ((coordinateAffineOpenCover k ι).map_prop i)

variable (k K : Type u) [Field k] [Field K] [Algebra k K] (ι : Type u)
    {C : Scheme.{u}} (j : C ⟶ ProjectiveSpace k ι) [IsClosedImmersion j]

/-- The chart algebra is the actual original coordinate ring map, fixed once
for every coordinate and reused by its quotient construction. -/
local instance projectiveCoordinateRingAlgebra (i : ι) :
    Algebra (coordinateRing k ι i) (coordinateRing K ι i) :=
  (coordinateRingMap (algebraMap k K) ι i).toAlgebra

/-- The target quotient chart is obtained from the once-selected source chart,
not from another choice of target ideal. -/
def projectiveBaseChangeQuotientChart (i : ι) :
    ClosedImmersionAffineQuotientChart
      (pullback.snd j (ProjectiveSpace.map (algebraMap k K) ι))
      (.of (coordinateRing K ι i)) ((coordinateAffineOpenCover K ι).f i) :=
  @ClosedImmersionAffineQuotientChart.baseChange
    C (ProjectiveSpace k ι) (ProjectiveSpace K ι) j
    (.of (coordinateRing k ι i)) (.of (coordinateRing K ι i))
    (projectiveCoordinateRingAlgebra k K ι i)
    ((coordinateAffineOpenCover k ι).f i)
    (projectiveSourceQuotientChart k ι j i)
    (ProjectiveSpace.map (algebraMap k K) ι)
    ((coordinateAffineOpenCover K ι).f i)
    (coordinateRingMap_awayι_isPullback (algebraMap k K) ι i)
    ((coordinateAffineOpenCover K ι).map_prop i)

/-- The target ideal is literally the original ideal mapped by the native
coordinate ring homomorphism. -/
@[simp]
theorem projectiveBaseChangeQuotientChart_ideal (i : ι) :
    (projectiveBaseChangeQuotientChart k K ι j i).ideal =
      (projectiveSourceQuotientChart k ι j i).ideal.map
        (coordinateRingMap (algebraMap k K) ι i) := rfl

/-- The original mapped-ideal quotient ring on a coordinate chart. -/
abbrev projectiveBaseChangeQuotientRing (i : ι) : CommRingCat.{u} :=
  .of (coordinateRing K ι i ⧸
    (projectiveSourceQuotientChart k ι j i).ideal.map
      (coordinateRingMap (algebraMap k K) ι i))

/-- Expose the original native quotient action on the literal chart-ring
abbreviation, using the same coordinate algebra as the chart constructor. -/
local instance projectiveBaseChangeQuotientAlgebra (i : ι) :
    Algebra (coordinateRing k ι i ⧸ (projectiveSourceQuotientChart k ι j i).ideal)
      (projectiveBaseChangeQuotientRing k K ι j i) :=
  @Ideal.Quotient.algebraQuotientMapQuotient
    (coordinateRing k ι i) inferInstance (coordinateRing K ι i) inferInstance
    (projectiveSourceQuotientChart k ι j i).ideal
    (projectiveCoordinateRingAlgebra k K ι i)

/-- The literal target chart map into the same native scheme pullback. -/
def projectiveBaseChangeQuotientMap (i : ι) :
    Spec (projectiveBaseChangeQuotientRing k K ι j i) ⟶
      CategoryTheory.Limits.pullback j (ProjectiveSpace.map (algebraMap k K) ι) :=
  (projectiveBaseChangeQuotientChart k K ι j i).sourceMap

/-- The target coordinate chart retains its actual quotient map and square. -/
theorem projectiveBaseChangeQuotientMap_isPullback (i : ι) :
    IsPullback (projectiveBaseChangeQuotientMap k K ι j i)
      (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk
        ((projectiveSourceQuotientChart k ι j i).ideal.map
          (coordinateRingMap (algebraMap k K) ι i)))))
      (pullback.snd j (ProjectiveSpace.map (algebraMap k K) ι))
      ((coordinateAffineOpenCover K ι).f i) :=
  (projectiveBaseChangeQuotientChart k K ι j i).square

/-- Restriction of the original field-change projection retains the native
quotient-source map and the same target chart map. -/
theorem projectiveBaseChangeQuotientMap_projection_isPullback (i : ι) :
    IsPullback
      (Spec.map (CommRingCat.ofHom
        (algebraMap (coordinateRing k ι i ⧸ (projectiveSourceQuotientChart k ι j i).ideal)
          (projectiveBaseChangeQuotientRing k K ι j i))))
      (projectiveBaseChangeQuotientMap k K ι j i)
      (projectiveSourceQuotientChart k ι j i).sourceMap
      (pullback.fst j (ProjectiveSpace.map (algebraMap k K) ι)) :=
  @ClosedImmersionAffineQuotientChart.baseChangeSourceMap_projection_isPullback
    C (ProjectiveSpace k ι) (ProjectiveSpace K ι) j
    (.of (coordinateRing k ι i)) (.of (coordinateRing K ι i))
    (projectiveCoordinateRingAlgebra k K ι i)
    ((coordinateAffineOpenCover k ι).f i)
    (projectiveSourceQuotientChart k ι j i)
    (ProjectiveSpace.map (algebraMap k K) ι)
    ((coordinateAffineOpenCover K ι).f i)
    (coordinateRingMap_awayι_isPullback (algebraMap k K) ι i)

/-- The first projection of the chart is the original quotient-source map. -/
@[reassoc (attr := simp)]
theorem projectiveBaseChangeQuotientMap_fst (i : ι) :
    projectiveBaseChangeQuotientMap k K ι j i ≫
        pullback.fst j (ProjectiveSpace.map (algebraMap k K) ι) =
      Spec.map (CommRingCat.ofHom
        (algebraMap (coordinateRing k ι i ⧸ (projectiveSourceQuotientChart k ι j i).ideal)
          (projectiveBaseChangeQuotientRing k K ι j i))) ≫
        (projectiveSourceQuotientChart k ι j i).sourceMap :=
  (projectiveBaseChangeQuotientMap_projection_isPullback k K ι j i).w.symm

/-- The second projection is the original target quotient map followed by
its original projective coordinate open. -/
@[reassoc (attr := simp)]
theorem projectiveBaseChangeQuotientMap_snd (i : ι) :
    projectiveBaseChangeQuotientMap k K ι j i ≫
        pullback.snd j (ProjectiveSpace.map (algebraMap k K) ι) =
      Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk
        ((projectiveSourceQuotientChart k ι j i).ideal.map
          (coordinateRingMap (algebraMap k K) ι i)))) ≫
        (coordinateAffineOpenCover K ι).f i :=
  (projectiveBaseChangeQuotientMap_isPullback k K ι j i).w

/-- The original quotient chart is the corresponding object of the native
pullback of the target coordinate cover. The iso is derived, not supplied. -/
def projectiveBaseChangeQuotientCoverObjIso (i : ι) :
    Spec (projectiveBaseChangeQuotientRing k K ι j i) ≅
      (((coordinateAffineOpenCover K ι).openCover).pullback₁
        (pullback.snd j (ProjectiveSpace.map (algebraMap k K) ι))).X i :=
  (projectiveBaseChangeQuotientMap_isPullback k K ι j i).isoPullback

/-- Native cover transport keeps the literal mapped-ideal spectra and their
original chart maps. No separate surjectivity or isomorphism premise is used. -/
def projectiveBaseChangeQuotientOpenCover :
    Scheme.OpenCover.{u}
      (CategoryTheory.Limits.pullback j (ProjectiveSpace.map (algebraMap k K) ι)) :=
  Scheme.Cover.copy
    (((coordinateAffineOpenCover K ι).openCover).pullback₁
      (pullback.snd j (ProjectiveSpace.map (algebraMap k K) ι)))
    ι (fun i => Spec (projectiveBaseChangeQuotientRing k K ι j i))
    (projectiveBaseChangeQuotientMap k K ι j) (Equiv.refl ι)
    (projectiveBaseChangeQuotientCoverObjIso k K ι j)
    (fun i => (projectiveBaseChangeQuotientMap_isPullback k K ι j i).isoPullback_hom_fst.symm)

/-- The cover index remains the original projective coordinate index. -/
@[simp]
theorem projectiveBaseChangeQuotientOpenCover_I₀ :
    (projectiveBaseChangeQuotientOpenCover k K ι j).I₀ = ι := rfl

/-- The cover object is literally the original mapped-ideal spectrum. -/
@[simp]
theorem projectiveBaseChangeQuotientOpenCover_X (i : ι) :
    (projectiveBaseChangeQuotientOpenCover k K ι j).X i =
      Spec (projectiveBaseChangeQuotientRing k K ι j i) := rfl

/-- The cover arrow is literally the original target quotient-chart map. -/
@[simp]
theorem projectiveBaseChangeQuotientOpenCover_f (i : ι) :
    (projectiveBaseChangeQuotientOpenCover k K ι j).f i =
      projectiveBaseChangeQuotientMap k K ι j i := rfl

end AlgebraicGeometry.Scheme.Modules
