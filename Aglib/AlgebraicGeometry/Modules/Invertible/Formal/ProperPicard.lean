/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Modules.Invertible.Formal.Algebraization.Effectivity
public import Aglib.AlgebraicGeometry.Modules.Invertible.Formal.BinaryLifting

/-!
# Complete-Noetherian Picard restriction for an affine binary cover

Actual square-zero successor lifting constructs compatible line bundles.
Proper Grothendieck existence algebraizes the original native coherent
system, and the proved positive-thickening criterion makes its actual
coefficient locally rank one. The original geometric restriction recovers
the specified first bundle. No flatness or residue-field hypothesis is used.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory

namespace AlgebraicGeometry.Scheme.Modules.Invertible

universe u
variable {R : Type u} [CommRing R] [IsNoetherianRing R] {X : Scheme.{u}}

section Binary

variable (A : Scheme.AffineBinaryCover X)
  (f : X ⟶ Spec (CommRingCat.of R)) [IsProper f]
  (I : Ideal R) [IsAdicComplete I R]

include A

/-- Every original ideal-fibre bundle lifts on a proper scheme with the
specified affine binary cover over a complete Noetherian base. -/
theorem exists_lineBundle_lift_affineBinary_complete
    (L : LineBundle (idealThickeningSpace f I)) :
    ∃ M : LineBundle X, Nonempty ((pullback (idealThickeningι f I)).obj M.val ≅ L.val) := by
  let P (J : Ideal R) : Prop := ∀ L₀ : LineBundle (idealThickeningSpace f J),
    ∃ M : LineBundle X,
      Nonempty ((pullback (idealThickeningι f J)).obj M.val ≅ L₀.val)
  have h : P (I ^ (0 + 1)) := by
    intro L₀
    let S := affineBinaryCompatibleSystem A f I L₀
    exact ⟨S.algebraizedLineBundle, ⟨S.algebraizedLineBundleReductionIso 0⟩⟩
  have hI : I ^ (0 + 1) = I := by simp
  exact ((congrArg P hI).mp h) L

/-- Surjectivity of the original Picard restriction map for an actual
affine binary cover over a complete Noetherian base. -/
theorem pullbackClass_affineBinary_complete_surjective :
    Function.Surjective (pullbackClass (idealThickeningι f I)) := by
  intro a
  induction a using Quotient.inductionOn with
  | h L =>
    obtain ⟨M, ⟨e⟩⟩ := exists_lineBundle_lift_affineBinary_complete A f I L
    exact ⟨classOf X M, Quotient.sound ⟨e⟩⟩

end Binary

variable
  (p : X ⟶ Scheme.ProjectiveLine.projectiveP1 R) [IsAffineHom p]
  (f : X ⟶ Spec (CommRingCat.of R)) [IsProper f]
  (I : Ideal R) [IsAdicComplete I R]

include p

/-- Every actual line bundle on the ideal closed fibre lifts on a proper
scheme affine over the projective line over a complete Noetherian base. -/
theorem exists_lineBundle_lift_projectiveLine_complete
    (L : LineBundle (idealThickeningSpace f I)) :
    ∃ M : LineBundle X, Nonempty ((pullback (idealThickeningι f I)).obj M.val ≅ L.val) := by
  exact exists_lineBundle_lift_affineBinary_complete (projectiveLineAffineBinaryCover p) f I L

/-- Surjectivity of the actual Picard restriction map on the ideal closed
fibre. This complete-Noetherian theorem has no separably closed residue premise. -/
theorem pullbackClass_projectiveLine_complete_surjective :
    Function.Surjective (pullbackClass (idealThickeningι f I)) := by
  intro a
  induction a using Quotient.inductionOn with
  | h L =>
    obtain ⟨M, ⟨e⟩⟩ := exists_lineBundle_lift_projectiveLine_complete p f I L
    exact ⟨classOf X M, Quotient.sound ⟨e⟩⟩

end AlgebraicGeometry.Scheme.Modules.Invertible
