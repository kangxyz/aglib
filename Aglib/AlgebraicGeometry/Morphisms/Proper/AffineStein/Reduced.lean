/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Morphisms.Proper.AffineStein.Basic
public import Aglib.AlgebraicGeometry.Morphisms.Proper.ReducedGlobalSections

/-! # The original affine Stein factor for a reduced proper source

Reduced-source structure H0 finiteness supplies the original coefficient ring
map. The two maps are the existing affine Stein maps, not replacement factors.
No general coherent proper-cohomology or higher base-change theorem is imported.
-/

@[expose] public noncomputable section

open CategoryTheory

universe u

namespace AlgebraicGeometry.Scheme.AffineStein

variable {X Y : Scheme.{u}} [IsReduced X] [IsLocallyNoetherian Y]
  (f : X ⟶ Y) [IsProper f] (V : Y.Opens) (hV : IsAffineOpen V)

include hV in
/-- The original affine-open coefficient map is finite for a reduced proper
source over a locally Noetherian target. -/
theorem finite_coefficient_of_isReduced : (f.app V).hom.Finite := by
  let : IsAffine V.toScheme := hV
  let : IsNoetherianRing Γ(Y, V) :=
    IsLocallyNoetherian.component_noetherian (X := Y) ⟨V, hV⟩
  let p := (f ∣_ V) ≫ V.toSpecΓ
  have : IsProper p := by
    change IsProper ((f ∣_ V) ≫ hV.isoSpec.hom)
    infer_instance
  have hb := finite_structuralCoefficients_of_isReduced Γ(Y, V) p
  have hs : ((Scheme.ΓSpecIso Γ(Y, V)).inv ≫ p.appTop) ≫
      (f ⁻¹ᵁ V).topIso.hom = f.app V := by
    rw [structuralCoefficient_square f V, Category.assoc,
      Iso.inv_hom_id, Category.comp_id]
  have hi : (f ⁻¹ᵁ V).topIso.hom.hom.Finite :=
    RingHom.Finite.of_surjective _
      (f ⁻¹ᵁ V).topIso.commRingCatIsoToRingEquiv.surjective
  have hc := hi.comp hb
  change (((Scheme.ΓSpecIso Γ(Y, V)).inv ≫ p.appTop) ≫
    (f ⁻¹ᵁ V).topIso.hom).hom.Finite at hc
  rw [hs] at hc
  exact hc

/-- The unchanged second affine Stein map is finite under reducedness. -/
theorem finiteMap_isFinite_of_isReduced : IsFinite (finiteMap f V hV) := by
  let : IsFinite (Spec.map (f.app V)) :=
    (IsFinite.SpecMap_iff (f.app V)).mpr (finite_coefficient_of_isReduced f V hV)
  dsimp only [finiteMap]
  infer_instance

include hV in
/-- The unchanged first affine Stein map is proper under reducedness. -/
theorem first_isProper_of_isReduced : IsProper (first f V) := by
  let : IsFinite (finiteMap f V hV) := finiteMap_isFinite_of_isReduced f V hV
  have : IsProper (first f V ≫ finiteMap f V hV) := by
    rw [factorization]
    infer_instance
  exact IsProper.of_comp (first f V) (finiteMap f V hV)

end AlgebraicGeometry.Scheme.AffineStein
