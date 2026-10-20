/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.SchemeTheoreticallyDominant
public import Mathlib.AlgebraicGeometry.Properties

/-!
# Integrality of the actual schematic image

Source: `R5Lab.Aglib.AlgebraicGeometry.SchemeTheoreticImage.Integral`.
R5 packet revision: `f8a3314ddecffcada2ec721d26d56a937bed9690`.
Source SHA-256: `2d171fac9d228e37eca27cf96c315325d849ac172692096b8b1eee5e4ff69932`.
Actual objects, maps, universes and hypotheses are retained.
Native declaration ownership replaces the source application namespaces.
-/

@[expose] public section

noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace Opposite Order
universe u
namespace AlgebraicGeometry.Scheme

/-- The actual schematic image of a quasi-compact map from an integral scheme
is integral. -/
theorem schemeImage_isIntegral {U Z : Scheme.{u}} [IsIntegral U]
    (f : U ⟶ Z) [QuasiCompact f] : IsIntegral f.image := by
  have hred (V : Z.affineOpens) : IsReduced (Spec (f.ker.subschemeCover.X V)) := by
    let : _root_.IsReduced Γ(f.image, f.imageι ⁻¹ᵁ V.1) :=
      isReduced_of_injective (f.toImage.app (f.imageι ⁻¹ᵁ V.1)).hom
        (f.toImage_app_injective V)
    let : _root_.IsReduced (Γ(Z, V.1) ⧸ f.ker.ideal V) :=
      isReduced_of_injective (f.ker.subschemeObjIso V).inv.hom
        (f.ker.subschemeObjIso V).symm.commRingCatIsoToRingEquiv.injective
    exact inferInstanceAs (IsReduced (Spec (.of (Γ(Z, V.1) ⧸ f.ker.ideal V))))
  let : ∀ i, IsReduced (f.ker.subschemeCover.openCover.X i) := hred
  let : IsReduced f.image := IsReduced.of_openCover _ f.ker.subschemeCover.openCover
  have hi := ((IrreducibleSpace.isIrreducible_univ U).image f.toImage
    f.toImage.continuous.continuousOn).closure
  rw [Set.image_univ, f.toImage.denseRange.closure_range] at hi
  let : IrreducibleSpace f.image := (irreducibleSpace_def _).mpr hi
  exact isIntegral_of_irreducibleSpace_of_isReduced _


end AlgebraicGeometry.Scheme
