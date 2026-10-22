/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Mathlib.AlgebraicGeometry.AffineTransitionLimit

/-!
# Descending the quasi-affine overlap in affine-open extension

A quasi-compact quasi-affine open of an affine-transition limit with
quasi-separated stages descends to an actual quasi-compact quasi-affine open
at a stage. The preimage equality
retains the original open; no independently chosen replacement is used.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits TopologicalSpace

namespace AlgebraicGeometry.Scheme.FinitePresentationEnvelope

universe u

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- A specified quasi-affine compact open descends as a quasi-affine compact
open along an actual affine-transition inverse limit with quasi-separated stages. -/
theorem exists_quasiAffine_open_preimage_eq
    {I : Type u} [Category.{u} I] [IsCofiltered I]
    (D : I ⥤ Scheme.{u})
    [∀ {i j} (g : i ⟶ j), IsAffineHom (D.map g)]
    [∀ i, QuasiSeparatedSpace (D.obj i)]
    (c : Cone D) (hc : IsLimit c)
    (W : c.pt.Opens) (hW : IsCompact (W : Set c.pt)) [IsQuasiAffine W.toScheme] :
    ∃ (i : I) (U : (D.obj i).Opens), IsCompact (U : Set (D.obj i)) ∧
      c.π.app i ⁻¹ᵁ U = W ∧ IsQuasiAffine U.toScheme := by
  obtain ⟨i, U, hU, he⟩ := AlgebraicGeometry.exists_preimage_eq D c hc W hW
  have (j : Over i) : CompactSpace ((AlgebraicGeometry.opensDiagram D i U).obj j) :=
    isCompact_iff_compactSpace.mp
      (QuasiCompact.isCompact_preimage (f := D.map j.hom) (U : Set (D.obj i)) U.isOpen hU)
  have (j : Over i) : QuasiSeparatedSpace
      ((AlgebraicGeometry.opensDiagram D i U).obj j) := by
    exact (isQuasiSeparated_iff_quasiSeparatedSpace _ (D.map j.hom ⁻¹ᵁ U).2).mp
      (.of_quasiSeparatedSpace _)
  have : IsQuasiAffine (AlgebraicGeometry.opensCone D c i U).pt := by
    change IsQuasiAffine (c.π.app i ⁻¹ᵁ U).toScheme
    rw [he]
    infer_instance
  obtain ⟨j, hj⟩ := Scheme.exists_isQuasiAffine_of_isLimit
    (AlgebraicGeometry.opensDiagram D i U) (AlgebraicGeometry.opensCone D c i U)
    (AlgebraicGeometry.isLimitOpensCone D c hc i U)
  refine ⟨j.left, D.map j.hom ⁻¹ᵁ U,
    QuasiCompact.isCompact_preimage (f := D.map j.hom) (U : Set (D.obj i)) U.isOpen hU, ?_, hj⟩
  simpa only [← Scheme.Hom.comp_preimage, c.w] using he

end AlgebraicGeometry.Scheme.FinitePresentationEnvelope
