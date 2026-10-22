/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Morphisms.Proper.Chow.Projective
public import Aglib.AlgebraicGeometry.Cohomology.GrothendieckExistence.Projective
public import Aglib.AlgebraicGeometry.Cohomology.GrothendieckExistence.FormalPullback

/-!
# Coherent realization on the original Chow modification

Projective existence realizes the actual formal pullback on the same Chow
source. Descent of this coherent sheaf to the proper target is separate.
-/

@[expose] public noncomputable section

open CategoryTheory
open AlgebraicGeometry.ProjectiveSpace
open AlgebraicGeometry.Scheme.Modules
open AlgebraicGeometry.Scheme.Modules.Coherent

universe u

namespace AlgebraicGeometry.Scheme.Cohomology

/-- Every formal coherent system on a proper scheme has a coherent realization
of its original pullback on an actual Chow modification. -/
theorem exists_chowSource_realization
    (A : Type u) [CommRing A] [IsNoetherianRing A]
    (I : Ideal A) [IsAdicComplete I A]
    {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of A)) [IsProper f] :
    letI : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian f
    ∀ F : AdicSystem X (idealThickeningIdealSheaf f I),
    ∃ (Y : Scheme.{u}) (p : Y ⟶ X) (V : X.Opens),
      IsProper p ∧ Surjective p ∧ Dense (V : Set X) ∧ IsIso (p ∣_ V) ∧
      ∃ hY : IsLocallyNoetherian Y,
        letI := hY
        ∃ G : Y.CoherentSheaf,
          Nonempty ((baseIdealPullbackFunctor p f I).obj F ≅
            (completionFunctor Y (idealThickeningIdealSheaf (p ≫ f) I)).obj G) := by
  let : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian f
  intro F
  obtain ⟨Y, p, m, j, V, hp, hps, hj, hbase, hV, hViso⟩ :=
    Chow.exists_projective_modification A f
  let : IsClosedImmersion j := hj
  let hY : IsLocallyNoetherian Y := LocallyOfFiniteType.isLocallyNoetherian j
  let : IsLocallyNoetherian Y := hY
  have he := projectiveCompletionIsEquivalence A I m j
  rw [hbase] at he
  let C := completionFunctor Y (idealThickeningIdealSheaf (p ≫ f) I)
  let : C.IsEquivalence := he
  let P := (baseIdealPullbackFunctor p f I).obj F
  exact ⟨Y, p, V, hp, hps, hV, hViso, hY, C.objPreimage P,
    ⟨(C.objObjPreimageIso P).symm⟩⟩

end AlgebraicGeometry.Scheme.Cohomology
