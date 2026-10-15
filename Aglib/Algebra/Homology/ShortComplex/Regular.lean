/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.Algebra.Homology.ShortComplex.Adjunction
public import Aglib.CategoryTheory.Limits.Shapes.RegularKernel
public import Aglib.CategoryTheory.Abelian.Regular
public import Mathlib.CategoryTheory.Adjunction.Limits

/-!
# Canonical homology comparison for a regular outgoing differential

If the outgoing differential admits an actual generalized inverse, any
additive functor preserving cokernels preserves both homology data of the
displayed short complex. Consequently the original adjunction mate on
homology is invertible. A projective target and projective outgoing
cokernel supply the generalized inverse; the first two objects need not
be projective.
-/

@[expose] public section

noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits

namespace CategoryTheory.ShortComplex

variable {C : Type*} [Category* C] [Abelian C] {S : ShortComplex C}

/-- A generalized inverse of the original outgoing differential descends to its actual
right-homology-data arrow through the original opcycles projection. -/
theorem RightHomologyData.generalizedInverse_g' (h : S.RightHomologyData)
    (s : S.X₃ ⟶ S.X₂) (hs : S.g ≫ s ≫ S.g = S.g) :
    h.g' ≫ (s ≫ h.p) ≫ h.g' = h.g' := by
  apply (cancel_epi h.p).mp
  simpa only [Category.assoc, h.p_g'_assoc, h.p_g'] using hs

/-- With projective last object and outgoing cokernel, original homology is projective
exactly when the original opcycles are projective. -/
theorem projective_homology_iff_projective_opcycles_of_projective_cokernel
    (S : ShortComplex C) [Projective S.X₃] [Projective (cokernel S.g)] :
    Projective S.homology ↔ Projective S.opcycles := by
  obtain ⟨s, hs⟩ := Abelian.exists_generalizedInverse_of_projective_cokernel S.g
  have hs' := S.rightHomologyData.generalizedInverse_g' s hs
  change S.fromOpcycles ≫ (s ≫ S.pOpcycles) ≫ S.fromOpcycles = S.fromOpcycles at hs'
  let e : S.homology ≅ kernel S.fromOpcycles :=
    S.homologyIsKernel.conePointUniqueUpToIso (limit.isLimit _)
  exact (Projective.iso_iff e).trans
    (Abelian.projective_kernel_iff_of_generalizedInverse S.fromOpcycles
      (s ≫ S.pOpcycles) hs')

end CategoryTheory.ShortComplex

namespace CategoryTheory.Functor

variable {C D : Type*} [Category* C] [Category* D] [Abelian C] [Abelian D]
    (F : C ⥤ D) [F.Additive] [PreservesColimitsOfShape WalkingParallelPair F]
    (S : ShortComplex C)

/-- Cokernel preservation and a generalized inverse of the original outgoing differential
give pointwise preservation of left homology. -/
theorem preservesLeftHomologyOf_of_generalizedInverse
    (s : S.X₃ ⟶ S.X₂) (hs : S.g ≫ s ≫ S.g = S.g) : F.PreservesLeftHomologyOf S :=
  ⟨fun _ => {
    g := preservesKernel_of_generalizedInverse F S.g s hs
    f' := by infer_instance }⟩

/-- The same hypotheses preserve the actual right homology data as well. -/
theorem preservesRightHomologyOf_of_generalizedInverse
    (s : S.X₃ ⟶ S.X₂) (hs : S.g ≫ s ≫ S.g = S.g) : F.PreservesRightHomologyOf S := by
  refine ⟨fun h => { f := by infer_instance, g' := ?_ }⟩
  exact preservesKernel_of_generalizedInverse F h.g' (s ≫ h.p)
    (h.generalizedInverse_g' s hs)

end CategoryTheory.Functor

namespace CategoryTheory.Adjunction

variable {C D : Type*} [Category* C] [Category* D] [Abelian C] [Abelian D]
    {F : C ⥤ D} {G : D ⥤ C} [F.Additive] [G.Additive] [G.PreservesHomology]

/-- A generalized inverse of the original outgoing differential makes the canonical
homology mate invertible, without exactness of the left adjoint. -/
theorem homologyComparison_isIso_of_generalizedInverse (adj : F ⊣ G)
    (S : ShortComplex C) (s : S.X₃ ⟶ S.X₂) (hs : S.g ≫ s ≫ S.g = S.g) :
    IsIso (adj.homologyComparison S) := by
  let : F.IsLeftAdjoint := adj.isLeftAdjoint
  let : PreservesFiniteColimits G := Functor.preservesFiniteColimits_of_preservesHomology G
  let : F.PreservesLeftHomologyOf S := F.preservesLeftHomologyOf_of_generalizedInverse S s hs
  let : F.PreservesRightHomologyOf S := F.preservesRightHomologyOf_of_generalizedInverse S s hs
  let : (F ⋙ G).PreservesLeftHomologyOf S :=
    (F ⋙ G).preservesLeftHomologyOf_of_generalizedInverse S s hs
  let : (F ⋙ G).PreservesRightHomologyOf S :=
    (F ⋙ G).preservesRightHomologyOf_of_generalizedInverse S s hs
  rw [adj.homologyComparison_eq_mapHomologyIso_inv S]
  infer_instance

/-- A projective last object and projective outgoing cokernel suffice for invertibility
of the original homology mate. No projectivity of the first two objects is needed. -/
theorem homologyComparison_isIso_of_projective_cokernel (adj : F ⊣ G)
    (S : ShortComplex C) [Projective S.X₃] [Projective (cokernel S.g)] :
    IsIso (adj.homologyComparison S) := by
  obtain ⟨s, hs⟩ := Abelian.exists_generalizedInverse_of_projective_cokernel S.g
  exact adj.homologyComparison_isIso_of_generalizedInverse S s hs

end CategoryTheory.Adjunction
