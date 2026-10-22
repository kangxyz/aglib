/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.ProjectiveSpace.Segre.ChartRing
public import Aglib.AlgebraicGeometry.ProjectiveSpace.PulledCoordinates

/-!
# Original product-coordinate sections

The product coordinate functions are defined on the actual inverse-image
intersections of two projective morphisms. Their coefficients come from the
original structural map, and their overlap and basic-open equations are
calculated before specializing the source to a scheme pullback.
-/

@[expose] public noncomputable section

open CategoryTheory Opposite MvPolynomial
open AlgebraicGeometry.Scheme.Modules.Invertible

universe u
attribute [local instance] MvPolynomial.gradedAlgebra

namespace AlgebraicGeometry.ProjectiveSpace.Segre

variable {R : Type u} [CommRing R] {Y : Scheme.{u}}

/-- Original base-ring constants restricted to the indicated source open. -/
def structuralCoefficient (b : Y ⟶ Spec (CommRingCat.of R)) (U : Y.Opens) : R →+* Γ(Y, U) :=
  (sectionRestrict Y le_top).comp (b.appTop.hom.comp (Scheme.ΓSpecIso (.of R)).inv.hom)

@[simp]
theorem structuralCoefficient_restrict (b : Y ⟶ Spec (CommRingCat.of R))
    {U V : Y.Opens} (h : V ≤ U) (r : R) :
    sectionRestrict Y h (structuralCoefficient b U r) = structuralCoefficient b V r := by
  simp only [structuralCoefficient, RingHom.comp_apply, sectionRestrict_comp]

/-- The original local coefficient map induces exactly the original structural map. -/
theorem structuralCoefficient_toSpec (b : Y ⟶ Spec (CommRingCat.of R)) (U : Y.Opens) :
    U.toSpecΓ ≫ Spec.map (CommRingCat.ofHom (structuralCoefficient b U)) = U.ι ≫ b := by
  change U.toSpecΓ ≫ Spec.map ((Scheme.ΓSpecIso (.of R)).inv ≫ b.appTop ≫
    Y.presheaf.map (homOfLE le_top).op) = _
  rw [Spec.map_comp, Spec.map_comp]
  simp only [← Category.assoc]
  rw [Scheme.Opens.toSpecΓ_SpecMap_presheaf_map_top]
  simp only [Category.assoc]
  rw [← Scheme.toSpecΓ_naturality_assoc]
  simp only [toSpecΓ_SpecMap_ΓSpecIso_inv, Category.comp_id]

variable {ι κ : Type u} (f : Y ⟶ ProjectiveSpace R ι) (g : Y ⟶ ProjectiveSpace R κ)

/-- The original common inverse-image coordinate chart. -/
abbrev sourceOpen (a : ι × κ) : Y.Opens :=
  f ⁻¹ᵁ coordinateOpen R ι a.1 ⊓ g ⁻¹ᵁ coordinateOpen R κ a.2

/-- Product of the actual factor ratios on their common source chart. -/
def sectionValue (a k : ι × κ) : Γ(Y, sourceOpen f g a) :=
  ratioOn f a.1 k.1 (sourceOpen f g a) inf_le_left *
    ratioOn g a.2 k.2 (sourceOpen f g a) inf_le_right

@[simp]
theorem sectionValue_self (a : ι × κ) : sectionValue f g a a = 1 := by
  simp only [sectionValue, ratioOn_self, mul_one]

/-- Evaluation of the target chart ring in the original product-coordinate sections. -/
def sectionChartHom (a : ι × κ) :
    coordinateRing R (ι × κ) a →+* Γ(Y, sourceOpen f g a) :=
  normalizedChartEval R a (structuralCoefficient (f ≫ toSpec R ι) (sourceOpen f g a))
    (sectionValue f g a)

@[simp]
theorem sectionChartHom_coefficient (a : ι × κ) (r : R) :
    sectionChartHom f g a (coordinateRingCoefficient R (ι × κ) a r) =
      structuralCoefficient (f ≫ toSpec R ι) (sourceOpen f g a) r := by
  simp only [sectionChartHom, normalizedChartEval_coefficient]

@[simp]
theorem sectionChartHom_ratio (a k : ι × κ) :
    sectionChartHom f g a (coordinateRatio R (ι × κ) a k) = sectionValue f g a k :=
  normalizedChartEval_ratio R a _ _ (sectionValue_self f g a) k

/-- Both original coordinate covers pull back to a cover of their common source. -/
theorem iSup_sourceOpen_eq_top : (⨆ a, sourceOpen f g a) = ⊤ := by
  apply top_unique
  intro x _
  obtain ⟨a, ha⟩ := TopologicalSpace.Opens.mem_iSup.mp
    (show f x ∈ ⨆ a, coordinateOpen R ι a by rw [iSup_coordinateOpen_eq_top]; trivial)
  obtain ⟨b, hb⟩ := TopologicalSpace.Opens.mem_iSup.mp
    (show g x ∈ ⨆ b, coordinateOpen R κ b by rw [iSup_coordinateOpen_eq_top]; trivial)
  exact TopologicalSpace.Opens.mem_iSup.mpr ⟨(a, b), ha, hb⟩

/-- The exact product-coordinate basic open in the original source. -/
theorem basicOpen_sectionValue (a b : ι × κ) :
    Y.basicOpen (sectionValue f g a b) = sourceOpen f g a ⊓ sourceOpen f g b := by
  rw [sectionValue, Scheme.basicOpen_mul, basicOpen_ratioOn, basicOpen_ratioOn]
  dsimp only [sourceOpen]
  ac_rfl

/-- Product-coordinate ratios obey the actual multiplicative overlap equation. -/
theorem sectionValue_overlap (a b k : ι × κ) :
    sectionRestrict Y (inf_le_left : sourceOpen f g a ⊓ sourceOpen f g b ≤ sourceOpen f g a)
        (sectionValue f g a k) =
      sectionRestrict Y inf_le_left (sectionValue f g a b) *
        sectionRestrict Y inf_le_right (sectionValue f g b k) := by
  simp only [sectionValue, map_mul, ratioOn_restrict]
  rw [ratioOn_mul f a.1 b.1 k.1 _
    (inf_le_left.trans inf_le_left) (inf_le_right.trans inf_le_left),
    ratioOn_mul g a.2 b.2 k.2 _
    (inf_le_left.trans inf_le_right) (inf_le_right.trans inf_le_right)]
  ring

end AlgebraicGeometry.ProjectiveSpace.Segre
