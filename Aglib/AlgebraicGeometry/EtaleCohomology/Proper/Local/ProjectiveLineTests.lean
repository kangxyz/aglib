/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.Proper.Local.FiniteTests
public import Aglib.AlgebraicGeometry.EtaleCohomology.Curves.StrictlyLocalComparison

/-! # Finite constant direct-image tests on the strictly local projective line

The completed original curve comparison supplies all-degree surjectivity and
degree-zero injectivity for finite constant direct-image coefficients. The
base is an arbitrary henselian local ring with separably closed residue field.
The maps are the actual cohomology pullbacks to its literal closed fibre;
no Noetherian or coefficient-order restriction is added.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Scheme.EtaleCohomology.Proper

universe u eY eP eY' eP'

attribute [local instance] hasSheafifyLarge

variable {R : Type u} [CommRing R]

section LocalRing

variable [IsLocalRing R] {Y : Scheme.{u}} (f : Y ⟶ ProjectiveLine.projectiveP1 R)

/-- The actual native pullback of the finite cover as a morphism over the
literal pullback of the projective line. -/
def finiteResidueMap : Curves.residueFiber f ⟶
    pullback (ProjectiveLine.structureMap R) (LocalRing.residueSpecMap R) :=
  ((Over.pullback (LocalRing.residueSpecMap R)).map
    (Over.homMk f rfl : Over.mk (f ≫ ProjectiveLine.structureMap R) ⟶
      Over.mk (ProjectiveLine.structureMap R))).left

@[reassoc]
theorem finiteResidueMap_fst :
    finiteResidueMap f ≫
        pullback.fst (ProjectiveLine.structureMap R) (LocalRing.residueSpecMap R) =
      pullback.fst (f ≫ ProjectiveLine.structureMap R) (LocalRing.residueSpecMap R) ≫ f := by
  dsimp only [finiteResidueMap, Over.pullback_map_left]
  exact pullback.lift_fst _ _ _

@[reassoc]
theorem finiteResidueMap_snd :
    finiteResidueMap f ≫
        pullback.snd (ProjectiveLine.structureMap R) (LocalRing.residueSpecMap R) =
      Curves.residueFiberStructureMap f := by
  dsimp only [finiteResidueMap, Over.pullback_map_left]
  exact pullback.lift_snd _ _ _

/-- This is the actual Cartesian square for the finite cover and its literal
closed fibre, before the native projective-line base-change isomorphism. -/
theorem finiteResidueMap_isPullback :
    IsPullback
      (pullback.fst (f ≫ ProjectiveLine.structureMap R) (LocalRing.residueSpecMap R))
      (finiteResidueMap f) f
      (pullback.fst (ProjectiveLine.structureMap R) (LocalRing.residueSpecMap R)) := by
  have hOuter := IsPullback.of_hasPullback
    (ProjectiveLine.structureMap R) (LocalRing.residueSpecMap R)
  have hTotal := IsPullback.of_hasPullback
    (f ≫ ProjectiveLine.structureMap R) (LocalRing.residueSpecMap R)
  have hTotal' : IsPullback
      (pullback.fst (f ≫ ProjectiveLine.structureMap R) (LocalRing.residueSpecMap R))
      (finiteResidueMap f ≫
        pullback.snd (ProjectiveLine.structureMap R) (LocalRing.residueSpecMap R))
      (f ≫ ProjectiveLine.structureMap R) (LocalRing.residueSpecMap R) := by
    simpa only [finiteResidueMap_snd] using hTotal
  exact (hTotal'.flip.of_right (finiteResidueMap_fst f) hOuter.flip).flip

end LocalRing

section StrictlyLocal

variable [HenselianLocalRing R]
  {Y : Scheme.{u}} (f : Y ⟶ ProjectiveLine.projectiveP1 R) [IsFinite f]
  [HasExt.{eY} (AbelianSheaf.{u, u + 1} Y)]
  [HasExt.{eP} (AbelianSheaf.{u, u + 1} (ProjectiveLine.projectiveP1 R))]
  [HasExt.{eY'} (AbelianSheaf.{u, u + 1} (Curves.residueFiber f))]
  [HasExt.{eP'} (AbelianSheaf.{u, u + 1}
    (pullback (ProjectiveLine.structureMap R) (LocalRing.residueSpecMap R)))]

/-- Every finite constant direct-image test has surjective original closed-fibre
pullback in every degree over the arbitrary strictly local base. -/
theorem finiteConstantDirectImage_residuePullback_surjective
    [IsSepClosed (IsLocalRing.ResidueField R)]
    (A : Type u) [AddCommGroup A] [Finite A] (q : ℕ) :
    Function.Surjective (cohomologyPullback.{u, eP, eP'}
      (pullback.fst (ProjectiveLine.structureMap R) (LocalRing.residueSpecMap R))
      ((directImage f).obj (ConstantFinite.coefficient A Y)) q) := by
  let i := pullback.fst (f ≫ ProjectiveLine.structureMap R) (LocalRing.residueSpecMap R)
  have hs := Curves.finite_projectiveLine_constantRestriction_surjective f A q
  have hsource : Function.Surjective
      (cohomologyPullback.{u, eY, eY'} i (ConstantFinite.coefficient A Y) q) := by
    intro z
    obtain ⟨x, hx⟩ := hs (Sheaf.H.map
      ((inverseImageConstantIso i).app (ConstantFinite.value A)).hom q z)
    refine ⟨x, (cohomologyMapIso_bijective
      ((inverseImageConstantIso i).app (ConstantFinite.value A)) q).injective ?_⟩
    exact hx
  exact cohomologyPullback_finiteDirectImage_surjective f (finiteResidueMap f)
    (pullback.fst (ProjectiveLine.structureMap R) (LocalRing.residueSpecMap R)) i
    (finiteResidueMap_isPullback f) (ConstantFinite.coefficient A Y) q hsource

/-- The degree-zero original pullback is also injective on the same tests.
Higher injectivity for arbitrary coefficients is a separate devissage. -/
theorem finiteConstantDirectImage_residuePullback_injective_zero
    (A : Type u) [AddCommGroup A] [Finite A] :
    Function.Injective (cohomologyPullback.{u, eP, eP'}
      (pullback.fst (ProjectiveLine.structureMap R) (LocalRing.residueSpecMap R))
      ((directImage f).obj (ConstantFinite.coefficient A Y)) 0) := by
  let i := pullback.fst (f ≫ ProjectiveLine.structureMap R) (LocalRing.residueSpecMap R)
  have hz := (Curves.finite_projectiveLine_constantRestriction_bijective_of_le_one
    A f 0 (by omega)).injective
  have hsource : Function.Injective
      (cohomologyPullback.{u, eY, eY'} i (ConstantFinite.coefficient A Y) 0) := by
    intro a b hab
    apply hz
    change Sheaf.H.map ((inverseImageConstantIso i).app (ConstantFinite.value A)).hom 0
        (cohomologyPullback i (ConstantFinite.coefficient A Y) 0 a) =
      Sheaf.H.map ((inverseImageConstantIso i).app (ConstantFinite.value A)).hom 0
        (cohomologyPullback i (ConstantFinite.coefficient A Y) 0 b)
    rw [hab]
  exact cohomologyPullback_finiteDirectImage_injective f (finiteResidueMap f)
    (pullback.fst (ProjectiveLine.structureMap R) (LocalRing.residueSpecMap R)) i
    (finiteResidueMap_isPullback f) (ConstantFinite.coefficient A Y) 0 hsource

end StrictlyLocal

end AlgebraicGeometry.Scheme.EtaleCohomology.Proper
