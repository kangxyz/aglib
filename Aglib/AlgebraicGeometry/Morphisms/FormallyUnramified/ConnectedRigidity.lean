/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.FormallyUnramified
public import Mathlib.AlgebraicGeometry.Morphisms.Separated
public import Mathlib.AlgebraicGeometry.Morphisms.IsIso
public import Mathlib.Topology.Connected.Clopen

/-!
# Connected-source rigidity of unramified lifts

Source: `lean/R5Lab/Aglib/AlgebraicGeometry/Morphisms/FormallyUnramified/ConnectedRigidity.lean`.
Frozen R5 revision: `f8a3314ddecffcada2ec721d26d56a937bed9690`.
SHA-256: `30b82a92daa946bbc62defb5a0ded599173088e8496c7205c10c7bd8281c651e`.
Native objects and proved suppliers replace application provenance and redundant premises.
-/

@[expose] public section


noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory Limits AlgebraicGeometry
universe u

namespace AlgebraicGeometry.Scheme.Hom

/-- Two lifts through a separated unramified morphism from a connected scheme
agree once they agree on any nonempty test scheme. The clopen equalizer argument
proves equality of scheme morphisms, including maps on structure sheaves. -/
theorem eq_of_comp_eq_of_nonempty
    {X Y Z U : Scheme.{u}} (p : X ⟶ Y)
    [IsSeparated p] [FormallyUnramified p] [LocallyOfFiniteType p]
    [ConnectedSpace Z] [Nonempty U] (i : U ⟶ Z)
    (f g : Z ⟶ X) (hfg : f ≫ p = g ≫ p)
    (hi : i ≫ f = i ≫ g) : f = g := by
  let a : Z ⟶ pullback p p := pullback.lift f g hfg
  let j : pullback a (pullback.diagonal p) ⟶ Z := pullback.fst _ _
  have hjopen : IsOpenImmersion j := by dsimp [j]; infer_instance
  have hjclosed : IsClosedImmersion j := by dsimp [j]; infer_instance
  have hia : i ≫ a = (i ≫ f) ≫ pullback.diagonal p := by
    apply pullback.hom_ext
    · simp [a]
    · simpa [a] using hi.symm
  let l : U ⟶ pullback a (pullback.diagonal p) :=
    pullback.lift i (i ≫ f) hia
  have hlj : l ≫ j = i := by simp [l, j]
  have hjclopen : IsClopen (Set.range j) :=
    ⟨j.isClosedEmbedding.isClosed_range, j.isOpenEmbedding.isOpen_range⟩
  have hjrange : Set.range j = Set.univ := hjclopen.eq_univ
    ⟨i (Classical.arbitrary U), l (Classical.arbitrary U),
      congrArg (fun r : U ⟶ Z => r (Classical.arbitrary U)) hlj⟩
  let : Surjective j := ⟨Set.range_eq_univ.mp hjrange⟩
  have : IsIso j :=
    (isIso_iff_isOpenImmersion_and_surjective j).mpr ⟨hjopen, inferInstance⟩
  apply (cancel_epi j).mp
  have hj : j ≫ a = pullback.snd a (pullback.diagonal p) ≫ pullback.diagonal p :=
    pullback.condition
  calc
    j ≫ f = (j ≫ a) ≫ pullback.fst p p := by simp [a]
    _ = (pullback.snd a (pullback.diagonal p) ≫ pullback.diagonal p) ≫
        pullback.fst p p := by rw [hj]
    _ = pullback.snd a (pullback.diagonal p) := by simp
    _ = (pullback.snd a (pullback.diagonal p) ≫ pullback.diagonal p) ≫
        pullback.snd p p := by simp
    _ = (j ≫ a) ≫ pullback.snd p p := by rw [hj]
    _ = j ≫ g := by simp [a]

end AlgebraicGeometry.Scheme.Hom
