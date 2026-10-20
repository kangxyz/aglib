/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Morphisms.Proper.BirationalInterfaces
public import Mathlib.AlgebraicGeometry.Morphisms.IsIso

/-!
# Proper birational recognition from nongeneric DVR stalks

The proved consumer retains the proper-birational DVR isomorphism-locus family as an input.
One actual DVR stalk supplies a nonempty open containing the generic point; the same family
handles every other point. No assertion that an arbitrary scheme has these stalks is made.

Source: `R5Lab/Aglib/AlgebraicGeometry/Morphisms/Proper/DVRRecognition.lean`,
R5 revision `f8a3314ddecffcada2ec721d26d56a937bed9690`, SHA-256
`51e179852e32d9753eb642fb5ba5970ffe76604ef55cd3668c4cddfbc4059f59`.
-/

@[expose] public section

noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory

namespace AlgebraicGeometry.Scheme.Hom

universe u

/-- The original morphism is an isomorphism under the supplied locus theorem family
and the displayed DVR conditions on the original target stalks. -/
lemma isIso_of_dvr_off_generic (H : Scheme.ProperBirationalDVRIsomorphismLocus.{u})
    {X Y : Scheme.{u}} [IsIntegral X] [IsIntegral Y] [IsLocallyNoetherian Y]
    (f : X ⟶ Y) [IsProper f] [IsDominant f]
    (hf : IsIso (CommRingCat.ofHom (Scheme.functionFieldMap f)))
    (z₀ : Y) [IsDiscreteValuationRing (Y.presheaf.stalk z₀)]
    (hdvr : ∀ z : Y, z ≠ genericPoint Y →
      IsDiscreteValuationRing (Y.presheaf.stalk z)) : IsIso f := by
  obtain ⟨U, hz₀, hU⟩ := H X Y f hf z₀
  have hgeneric : genericPoint Y ∈ U :=
    ((genericPoint_spec Y).mem_open_set_iff U.isOpen).mpr (by
      simpa only [Set.univ_inter] using (show (U : Set Y).Nonempty from ⟨z₀, hz₀⟩))
  apply IsZariskiLocalAtTarget.of_forall_exists_morphismRestrict
    (P := MorphismProperty.isomorphisms Scheme)
  intro z
  by_cases hz : z = genericPoint Y
  · exact ⟨U, hz ▸ hgeneric, hU⟩
  · have := hdvr z hz
    exact H X Y f hf z

end AlgebraicGeometry.Scheme.Hom
