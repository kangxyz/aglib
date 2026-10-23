/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Cover.AffineBinary
public import Mathlib.AlgebraicGeometry.AffineTransitionLimit

/-!
# Descent of actual affine binary covers

The two affine opens descend through the native finite-cover theorem. The
original affine intersection is the limit of the intersection opens, so
eventual affineness supplies the intersection at one later actual stage.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits TopologicalSpace

namespace AlgebraicGeometry.Scheme.AffineBinaryCover

universe u

/-- Both original opens and their affine intersection descend to an actual
stage of a qcqs inverse limit with affine transitions. -/
theorem exists_model_of_isLimit
    {I : Type u} [Category.{u} I] [IsCofiltered I]
    (D : I ⥤ Scheme.{u})
    [∀ {j k} (q : j ⟶ k), IsAffineHom (D.map q)]
    [∀ j, CompactSpace (D.obj j)] [∀ j, QuasiSeparatedSpace (D.obj j)]
    (c : Cone D) (hc : IsLimit c) (A : AffineBinaryCover c.pt) :
    ∃ (i : I) (B : AffineBinaryCover (D.obj i)),
      c.π.app i ⁻¹ᵁ B.first = A.first ∧ c.π.app i ⁻¹ᵁ B.second = A.second := by
  obtain ⟨i, V, hV, hVa⟩ :=
    Scheme.exists_isOpenCover_and_isAffine_of_finite D c hc A.opens A.isOpenCover A.affine
  let T := V false ⊓ V true
  have hT : IsAffineOpen (c.π.app i ⁻¹ᵁ T) := by
    change IsAffineOpen (c.π.app i ⁻¹ᵁ V false ⊓ c.π.app i ⁻¹ᵁ V true)
    rw [← (hVa false).2, ← (hVa true).2]
    exact A.affineIntersection
  have (j : Over i) : CompactSpace ((opensDiagram D i T).obj j) := by
    apply isCompact_iff_compactSpace.mp
    exact QuasiSeparatedSpace.inter_isCompact _ _
      (D.map j.hom ⁻¹ᵁ V false).isOpen ((hVa false).1.preimage (D.map j.hom)).isCompact
      (D.map j.hom ⁻¹ᵁ V true).isOpen ((hVa true).1.preimage (D.map j.hom)).isCompact
  have (j : Over i) : QuasiSeparatedSpace ((opensDiagram D i T).obj j) :=
    (isQuasiSeparated_iff_quasiSeparatedSpace _ (D.map j.hom ⁻¹ᵁ T).isOpen).mp
      (.of_quasiSeparatedSpace _)
  have : IsAffine (opensCone D c i T).pt := hT
  obtain ⟨j, hj⟩ := Scheme.exists_isAffine_of_isLimit
    (opensDiagram D i T) (opensCone D c i T) (isLimitOpensCone D c hc i T)
  have hcover : V false ⊔ V true = ⊤ := by
    apply top_le_iff.mp
    intro x _
    obtain ⟨b, hb⟩ := hV.exists_mem x
    cases b
    · exact Or.inl hb
    · exact Or.inr hb
  let B : AffineBinaryCover (D.obj j.left) := {
    first := D.map j.hom ⁻¹ᵁ V false
    second := D.map j.hom ⁻¹ᵁ V true
    affineFirst := (hVa false).1.preimage (D.map j.hom)
    affineSecond := (hVa true).1.preimage (D.map j.hom)
    affineIntersection := hj
    covers := by rw [← Hom.preimage_sup, hcover, Hom.preimage_top] }
  refine ⟨j.left, B, ?_, ?_⟩
  · change c.π.app j.left ⁻¹ᵁ (D.map j.hom ⁻¹ᵁ V false) = A.first
    rw [← Hom.comp_preimage, c.w j.hom]
    exact (hVa false).2.symm
  · change c.π.app j.left ⁻¹ᵁ (D.map j.hom ⁻¹ᵁ V true) = A.second
    rw [← Hom.comp_preimage, c.w j.hom]
    exact (hVa true).2.symm

end AlgebraicGeometry.Scheme.AffineBinaryCover
