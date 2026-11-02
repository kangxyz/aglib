/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Spec.AffineSectionAlgebra
public import Aglib.AlgebraicGeometry.Morphisms.Finite.FunctionField

/-! # Original finite algebra above the same affine section chart

The source ring is the sections of the actual inverse-image open. Existing
`LocalNormAlgebra.chartAlgebra` supplies its single native `ν.app V` action;
this leaf adds the original section triangle without recreating that algebra.
-/

@[expose] public noncomputable section

open CategoryTheory

namespace AlgebraicGeometry.Scheme

universe u

variable {A : Type u} [CommRing A] [IsLocalRing A] {X Y : Scheme.{u}}

/-- The original lifted section's closed point lies in the actual inverse-image open. -/
theorem affineFiniteSection_closed_mem (ν : Y ⟶ X) (s : Spec (.of A) ⟶ X)
    (a : Spec (.of A) ⟶ Y) (ha : a ≫ ν = s) (V : X.Opens)
    (hc : s (IsLocalRing.closedPoint A) ∈ V) :
    a (IsLocalRing.closedPoint A) ∈ ν ⁻¹ᵁ V := by
  change (a ≫ ν) (IsLocalRing.closedPoint A) ∈ V
  rw [ha]
  exact hc

/-- The same finite inverse-image chart has its actual coefficient square. -/
theorem affineFiniteSection_spec (ν : Y ⟶ X) [IsFinite ν]
    {V : X.Opens} (hV : IsAffineOpen V) :
    Spec.map (ν.app V) ≫ hV.fromSpec = (hV.preimage ν).fromSpec ≫ ν := by
  simpa only [Scheme.Hom.appLE_eq_app] using
    IsAffineOpen.SpecMap_appLE_fromSpec ν hV (hV.preimage ν) le_rfl

/-- The original lifted section retains its whole ring-map triangle on the same chart. -/
theorem affineFiniteSectionRetraction_comp (ν : Y ⟶ X) [IsFinite ν]
    (s : Spec (.of A) ⟶ X) (a : Spec (.of A) ⟶ Y) (ha : a ≫ ν = s)
    {V : X.Opens} (hV : IsAffineOpen V) (hc : s (IsLocalRing.closedPoint A) ∈ V) :
    (affineLocalSectionRetraction a (ν ⁻¹ᵁ V)
      (affineFiniteSection_closed_mem ν s a ha V hc)).comp (ν.app V).hom =
        affineLocalSectionRetraction s V hc := by
  have h : CommRingCat.ofHom
      ((affineLocalSectionRetraction a (ν ⁻¹ᵁ V)
        (affineFiniteSection_closed_mem ν s a ha V hc)).comp (ν.app V).hom) =
      CommRingCat.ofHom (affineLocalSectionRetraction s V hc) := by
    apply Spec.map_injective
    apply (cancel_mono hV.fromSpec).mp
    rw [CommRingCat.ofHom_comp, CommRingCat.ofHom_hom, Spec.map_comp, Category.assoc,
      affineFiniteSection_spec ν hV, ← Category.assoc,
      affineLocalSectionRetraction_spec a (hV.preimage ν), ha,
      affineLocalSectionRetraction_spec s hV hc]
  exact congrArg CommRingCat.Hom.hom h

end AlgebraicGeometry.Scheme
