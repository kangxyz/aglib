/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Descent.FinitePresentation.Gluing
public import Aglib.AlgebraicGeometry.Limits.Clopen
public import Aglib.AlgebraicGeometry.Limits.ClosedRange
public import Mathlib.AlgebraicGeometry.Morphisms.Immersion

/-!
# Eventual closedness of the original quasi-compact immersion

If the pullback of a quasi-compact immersion to a qcqs affine-transition
limit is closed, its actual pullback at a later stage is already closed.
The proof uses the open factor in the native schematic image. It does not
assert that formation of schematic images commutes with base change.
-/

@[expose] public section

noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

open CategoryTheory CategoryTheory.Limits TopologicalSpace

universe u

namespace AlgebraicGeometry.Scheme

variable {I : Type u} [Category.{u} I] [IsCofiltered I]
  (D : I ⥤ Scheme.{u}) (c : Cone D) (hc : IsLimit c)
  [∀ {i j} (q : i ⟶ j), IsAffineHom (D.map q)]
  [∀ i, CompactSpace (D.obj i)] [∀ i, QuasiSeparatedSpace (D.obj i)]

include hc in
/-- A specified quasi-compact immersion which is closed after passage to
the limit is closed after one actual stage base change. -/
theorem exists_isClosedImmersion_pullback_fst_of_isLimit (i : I)
    {X : Scheme.{u}} (f : X ⟶ D.obj i) [IsImmersion f] [QuasiCompact f]
    [IsClosedImmersion (pullback.fst (c.π.app i) f)] :
    ∃ j : Over i, IsClosedImmersion (pullback.fst (D.map j.hom) f) := by
  let : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace f
  let U : f.image.Opens := f.toImage.opensRange
  have hU : IsCompact (U : Set f.image) := isCompact_range f.toImage.continuous
  let j₀ : Over i := Over.mk (𝟙 i)
  let U₀ : ((baseChangeDiagram D i f.imageι).obj j₀).Opens :=
    pullback.snd (D.map j₀.hom) f.imageι ⁻¹ᵁ U
  have hU₀ : IsCompact (U₀ : Set ((baseChangeDiagram D i f.imageι).obj j₀)) :=
    QuasiCompact.isCompact_preimage _ U.isOpen hU
  have hclosed : IsClosed (pullback.snd (c.π.app i) f.imageι ⁻¹' Set.range f.toImage) := by
    apply (Pullback.isClosed_preimage_range_comp_iff f.toImage f.imageι (c.π.app i)).mp
    rw [Hom.toImage_imageι, ← Pullback.range_fst]
    exact (pullback.fst (c.π.app i) f).isClosedEmbedding.isClosed_range
  have hclosed₀ : IsClosed
      (((baseChangeCone D c i f.imageι).π.app j₀ ⁻¹ᵁ U₀ :
        (pullback (c.π.app i) f.imageι).Opens) :
          Set (pullback (C := Scheme) (c.π.app i) f.imageι)) := by
    dsimp only [U₀]
    rw [← Hom.comp_preimage, baseChangeCone_π_app_snd]
    exact hclosed
  obtain ⟨j, q, hj⟩ := exists_isClosed_preimage_of_isLimit
    (baseChangeDiagram D i f.imageι) (baseChangeCone D c i f.imageι)
    (isLimitBaseChangeCone D c hc i f.imageι) U₀ hU₀ hclosed₀
  dsimp only [U₀] at hj
  rw [← Hom.comp_preimage, baseChangeDiagram_map_snd] at hj
  change IsClosed (pullback.snd (D.map j.hom) f.imageι ⁻¹' Set.range f.toImage) at hj
  refine ⟨j, IsClosedImmersion.of_isPreimmersion _ ?_⟩
  rw [Pullback.range_fst]
  simpa only [Hom.toImage_imageι] using
    (Pullback.isClosed_preimage_range_comp_iff f.toImage f.imageι (D.map j.hom)).mpr hj

end AlgebraicGeometry.Scheme
