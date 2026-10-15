/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Mathlib.AlgebraicGeometry.Morphisms.FormallyUnramified
public import Mathlib.AlgebraicGeometry.Morphisms.Separated
public import Mathlib.AlgebraicGeometry.Geometrically.Connected
public import Mathlib.AlgebraicGeometry.Morphisms.IsIso
public import Mathlib.Topology.Connected.Clopen

/-!
# Section rigidity through a separated unramified scheme morphism

Two lifts over a separated, formally unramified, locally finite-type morphism
agree on a geometrically connected family if they agree on a supplied section.
The conclusion is equality of the actual scheme morphisms; the parameter scheme
has no reducedness or connectedness hypothesis. Only the first general theorem
is selected; no pointed or all-test-object model is imported.

Source: R5Lab/AlgebraicGeometry/FiniteEtale/PointedRigidity.lean
at the private R5 2f9 source, frozen after the native-consumer refactor.
SHA256: 6014707cbe74aac457557e1731bd7ccf40421968789c45e59f1a834360226265
The selected statement, actual map equations and proof are preserved.
-/
@[expose] public section

noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
universe u

namespace AlgebraicGeometry.Scheme.Hom

/-- Lifts through a separated unramified morphism agree on a geometrically
connected family if they agree on a section. The source and parameter are
arbitrary schemes, and the conclusion is equality of scheme morphisms. -/
theorem eq_of_comp_eq_of_section
    {X Y Z T : Scheme.{u}} (p : X ⟶ Y)
    [IsSeparated p] [FormallyUnramified p] [LocallyOfFiniteType p]
    (q : Z ⟶ T) [GeometricallyConnected q]
    (s : T ⟶ Z) (hs : s ≫ q = 𝟙 T)
    (f g : Z ⟶ X) (hfg : f ≫ p = g ≫ p)
    (hsection : s ≫ f = s ≫ g) : f = g := by
  let a : Z ⟶ pullback p p := pullback.lift f g hfg
  let j : pullback a (pullback.diagonal p) ⟶ Z := pullback.fst _ _
  have hjopen : IsOpenImmersion j := by dsimp [j]; infer_instance
  have hjclosed : IsClosedImmersion j := by dsimp [j]; infer_instance
  have hsa : s ≫ a = (s ≫ f) ≫ pullback.diagonal p := by
    apply pullback.hom_ext
    · simp [a]
    · simpa [a] using hsection.symm
  let l : T ⟶ pullback a (pullback.diagonal p) :=
    pullback.lift s (s ≫ f) hsa
  have hlj : l ≫ j = s := by simp [l, j]
  have hjclopen : IsClopen (Set.range j) :=
    ⟨j.isClosedEmbedding.isClosed_range, j.isOpenEmbedding.isOpen_range⟩
  have hjsurj : Surjective j := by
    constructor
    intro z
    have hmeet : ((q ⁻¹' {q z}) ∩ Set.range j).Nonempty := by
      refine ⟨s (q z), ?_, ?_⟩
      · change q (s (q z)) = q z
        exact congrArg (fun r : T ⟶ T => r (q z)) hs
      · exact ⟨l (q z), congrArg (fun r : T ⟶ Z => r (q z)) hlj⟩
    exact (q.isConnected_preimage_singleton (q z)).isPreconnected.subset_isClopen
      hjclopen hmeet (show z ∈ q ⁻¹' {q z} from rfl)
  have : IsIso j :=
    (isIso_iff_isOpenImmersion_and_surjective j).mpr ⟨hjopen, hjsurj⟩
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
