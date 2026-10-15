/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Mathlib.Algebra.Homology.ShortComplex.ShortExact
public import Mathlib.CategoryTheory.MorphismProperty.Retract

/-!
# Short exactness under retractions

Short exactness descends along an actual retraction of short complexes. Homology
is carried through the original homology functor; both endpoint arrows remain the
original retract arrows. Only zero morphisms and a category with homology are required.
-/


/-!
Source: `Quillen/Algebra/Homology/ShortComplex/Retract.lean` at LOCAL Quillen
`189a8e779f0c68b2dfc6f8195daebb3e684a5905`.
Selection: whole_general_prerequisite; source ranges [[1, 50]].
Actual objects, maps, universes and hypotheses are preserved.
-/

@[expose] public section

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

open CategoryTheory CategoryTheory.Limits
namespace CategoryTheory.ShortComplex

variable {C : Type*} [Category* C] [HasZeroMorphisms C] [CategoryWithHomology C]
    {S T : ShortComplex C}

/-- Short exactness descends along the actual retraction of short complexes. -/
theorem shortExact_of_retract (h : Retract S T) (hT : T.ShortExact) : S.ShortExact where
  exact := by
    rw [S.exact_iff_isZero_homology, IsZero.iff_id_eq_zero]
    let r := h.map (homologyFunctor C)
    change 𝟙 ((homologyFunctor C).obj S) = 0
    rw [← r.retract]
    have hz := (T.exact_iff_isZero_homology).mp hT.exact
    have hr : r.r = 0 := hz.eq_of_src _ _
    rw [hr, comp_zero]
  mono_f := by
    let h' := h.map (fFunctor (C := C))
    have := hT.mono_f
    exact (MorphismProperty.monomorphisms C).of_retract h' inferInstance
  epi_g := by
    let h' := h.map (gFunctor (C := C))
    have := hT.epi_g
    exact (MorphismProperty.epimorphisms C).of_retract h' inferInstance

end CategoryTheory.ShortComplex
