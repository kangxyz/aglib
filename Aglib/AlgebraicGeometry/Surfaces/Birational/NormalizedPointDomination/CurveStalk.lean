/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Surfaces.Birational.NormalizedPointDomination.CurveImage

/-!
# Original stalk isomorphisms at surviving curve generic points

The codimension-one isomorphism neighborhood gives an isomorphism of the
original stalk map itself. This is the DVR identification needed to keep
one selected valuation during normalized-point elimination.
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory TopologicalSpace

namespace AlgebraicGeometry.Scheme

universe u

/-- At a point over the actual target isomorphism locus, the original stalk
map is an isomorphism. -/
theorem Hom.isIso_stalkMap_of_mem_targetIsomorphismLocus
    {X Y : Scheme.{u}} (f : X ⟶ Y) (x : X) (hx : f x ∈ f.targetIsomorphismLocus) :
    IsIso (f.stalkMap x) := by
  let U := f.targetIsomorphismLocus
  let : IsIso (f ∣_ U) := f.isIso_restrict_targetIsomorphismLocus
  exact ((MorphismProperty.isomorphisms CommRingCat).arrow_mk_iso_iff
    (morphismRestrictStalkMap f U ⟨x, hx⟩)).mp inferInstance

/-- A noncollapsed actual irreducible closed subset meets the codimension-one
isomorphism locus at its original generic point. Thus the original stalk
map, rather than an abstract DVR equivalence, is invertible there. -/
theorem Hom.isIso_stalkMap_genericPoint_of_not_subsingleton_image
    {X Y : Scheme.{u}} [IsIntegral X] [IsIntegral Y] [IsLocallyNoetherian Y]
    (f : X ⟶ Y) [IsProper f] [IsDominant f]
    (hff : IsIso (CommRingCat.ofHom (functionFieldMap f)))
    (hY : NormalStalks Y) (hdY : topologicalKrullDim Y ≤ 2)
    (C : IrreducibleCloseds X) (hC : ¬ (f '' (C : Set X)).Subsingleton) :
    IsIso (f.stalkMap C.isIrreducible.genericPoint) := by
  let c := C.isIrreducible.genericPoint
  have hc := f.isGenericPoint_irreducibleClosedImage C
  have hnc : ¬ IsClosed ({f c} : Set Y) := by
    intro hclosed
    apply hC
    have himage : f '' (C : Set X) = {f c} := hc.def.symm.trans hclosed.closure_eq
    rw [himage]
    exact Set.subsingleton_singleton
  obtain ⟨U, hcU, hU⟩ :=
    exists_isIso_restrict_of_isProper_birational_at_nonclosed_point f hff hY hdY (f c) hnc
  exact f.isIso_stalkMap_of_mem_targetIsomorphismLocus c
    (f.le_targetIsomorphismLocus U hU hcU)

end AlgebraicGeometry.Scheme
