/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Modules.Invertible.Formal.Completion.ClosedFiber
public import Aglib.AlgebraicGeometry.Modules.Invertible.Formal.Completion.ProjectiveLine
public import Aglib.AlgebraicGeometry.Modules.Invertible.Formal.ProperPicard
public import Aglib.AlgebraicGeometry.Modules.Invertible.Formal.ProjectiveLine.Cover
public import Aglib.AlgebraicGeometry.Cover.AffineBinary
public import Aglib.RingTheory.AdicCompletion.NoetherianRing
public import Mathlib.RingTheory.AdicCompletion.LocalRing

/-!
# Completed line bundles with their original ideal-fibre comparison

The actual completion base change inherits the actual two-affine cover.
Proper coherent effectivity over its complete Noetherian coefficient ring
lifts the transported original fibre bundle. The canonical fibre comparison
then recovers the supplied original bundle through its original immersion.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Scheme.Modules.Invertible

universe u

variable {R : Type u} [CommRing R] {X : Scheme.{u}}

/-- Every original ideal-fibre line bundle has an actual completed line
bundle with an actual isomorphism through the original closed-fibre map. -/
theorem exists_completedLineBundle_of_affineBinaryCover [IsNoetherianRing R]
    (A : Scheme.AffineBinaryCover X) (f : X ⟶ Spec (CommRingCat.of R)) [IsProper f]
    (I : Ideal R) (L : LineBundle (idealThickeningSpace f I)) :
    ∃ M : LineBundle (completionBaseChange f I),
      Nonempty ((pullback (completionClosedFiberMap f I)).obj M.val ≅ L.val) := by
  let S := AdicCompletion I R
  let J := I.map (algebraMap R S)
  have : IsNoetherianRing S := AdicCompletion.isNoetherianRing R I
  have : IsAdicComplete J S := AdicCompletion.isAdicComplete_self I I.fg_of_isNoetherianRing
  have : IsProper (completionStructure f I) := by
    change IsProper (Limits.pullback.fst (Spec.algebraMap R S) f)
    exact MorphismProperty.pullback_fst _ _ inferInstance
  let π : completionBaseChange f I ⟶ X := Limits.pullback.snd (Spec.algebraMap R S) f
  have : IsAffineHom π := by
    dsimp only [π]
    exact MorphismProperty.pullback_snd _ _
      (inferInstance : IsAffineHom (Spec.algebraMap R S))
  let e := completionClosedFiberIso f I I.fg_of_isNoetherianRing
  let N := pullbackLineBundle e.inv L
  obtain ⟨M, ⟨eM⟩⟩ := exists_lineBundle_lift_affineBinary_complete
    (A.pullback π) (completionStructure f I) J N
  exact ⟨M, ⟨completionClosedFiberRestrictionIso f I I.fg_of_isNoetherianRing
    M.val L.val eM⟩⟩

/-- The completed lifting statement for the original affine morphism over
the native projective line, retaining its stated structural triangle. -/
theorem exists_completedLineBundle_projectiveLine [IsNoetherianRing R]
    (p : X ⟶ Scheme.ProjectiveLine.projectiveP1 R) [IsAffineHom p]
    (f : X ⟶ Spec (CommRingCat.of R)) [IsProper f]
    (_h : p ≫ Scheme.ProjectiveLine.structureMap R = f)
    (I : Ideal R) (L : LineBundle (idealThickeningSpace f I)) :
    ∃ M : LineBundle (completionBaseChange f I),
      Nonempty ((pullback (completionClosedFiberMap f I)).obj M.val ≅ L.val) :=
  exists_completedLineBundle_of_affineBinaryCover (projectiveLineAffineBinaryCover p) f I L

end AlgebraicGeometry.Scheme.Modules.Invertible
