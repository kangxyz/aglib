/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Mathlib.AlgebraicGeometry.Properties
public import Mathlib.AlgebraicGeometry.Stalk

/-! # Original section algebra of one actual affine neighbourhood

The coefficient action and retraction are the original `appLE` maps composed
with the native `ΓSpecIso`. One chosen affine open containing the image of the
closed point contains the entire local section. No new scheme model is selected.
-/

@[expose] public noncomputable section

open CategoryTheory

namespace AlgebraicGeometry.Scheme

universe u

variable {A : Type u} [CommRing A] {X : Scheme.{u}}

/-- The original coefficient map on the actual open's section ring. -/
def affineSectionCoefficientMap (p : X ⟶ Spec (.of A)) (V : X.Opens) : A →+* Γ(X, V) :=
  ((ΓSpecIso (.of A)).inv ≫ p.appLE ⊤ V (by simp)).hom

/-- The original chart structure map is the spectrum of the original coefficient map. -/
theorem affineSectionCoefficientMap_spec (p : X ⟶ Spec (.of A))
    {V : X.Opens} (hV : IsAffineOpen V) :
    Spec.map (CommRingCat.ofHom (affineSectionCoefficientMap p V)) = hV.fromSpec ≫ p := by
  rw [← IsAffineOpen.SpecMap_appLE_fromSpec p (isAffineOpen_top _) hV (by simp),
    IsAffineOpen.fromSpec_top, Scheme.isoSpec_Spec_inv, ← Spec.map_comp]
  rfl

/-- Smoothness belongs to that same original coefficient map. -/
theorem affineSectionCoefficientMap_smooth (p : X ⟶ Spec (.of A)) [Smooth p]
    {V : X.Opens} (hV : IsAffineOpen V) : (affineSectionCoefficientMap p V).Smooth := by
  have h : Smooth (Spec.map (CommRingCat.ofHom (affineSectionCoefficientMap p V))) := by
    rw [affineSectionCoefficientMap_spec p hV]
    infer_instance
  exact HasRingHomProperty.Spec_iff.mp h

variable [IsLocalRing A]

/-- An open containing the closed point image contains the entire original local section. -/
theorem localSection_range_subset (s : Spec (.of A) ⟶ X) (V : X.Opens)
    (hV : s (IsLocalRing.closedPoint A) ∈ V) : Set.range s ⊆ (V : Set X) := by
  rintro _ ⟨x, rfl⟩
  exact ((IsLocalRing.specializes_closedPoint x).map s.continuous).mem_open V.isOpen hV

/-- The original section has the whole source as the inverse image of this open. -/
theorem localSection_top_le_preimage (s : Spec (.of A) ⟶ X) (V : X.Opens)
    (hc : s (IsLocalRing.closedPoint A) ∈ V) : ⊤ ≤ s ⁻¹ᵁ V :=
  fun x _ => localSection_range_subset s V hc ⟨x, rfl⟩

/-- The original local-section map on the same actual open's section ring. -/
def affineLocalSectionRetraction (s : Spec (.of A) ⟶ X) (V : X.Opens)
    (hV : s (IsLocalRing.closedPoint A) ∈ V) : Γ(X, V) →+* A :=
  (s.appLE V ⊤ (localSection_top_le_preimage s V hV) ≫
    (ΓSpecIso (.of A)).hom).hom

/-- The spectrum of the original retraction recovers the given section through the same chart. -/
theorem affineLocalSectionRetraction_spec (s : Spec (.of A) ⟶ X)
    {V : X.Opens} (hV : IsAffineOpen V) (hc : s (IsLocalRing.closedPoint A) ∈ V) :
    Spec.map (CommRingCat.ofHom (affineLocalSectionRetraction s V hc)) ≫ hV.fromSpec = s := by
  change Spec.map (_ ≫ (ΓSpecIso (.of A)).hom) ≫ hV.fromSpec = s
  rw [Spec.map_comp, Category.assoc,
    IsAffineOpen.SpecMap_appLE_fromSpec s hV (isAffineOpen_top _),
    IsAffineOpen.fromSpec_top, Scheme.isoSpec_Spec_inv, ← Category.assoc,
    ← Spec.map_comp, Iso.inv_hom_id, Spec.map_id, Category.id_comp]

/-- The whole original section identity gives the whole original coefficient retraction. -/
theorem affineLocalSectionRetraction_comp
    (p : X ⟶ Spec (.of A)) (s : Spec (.of A) ⟶ X) (hs : s ≫ p = 𝟙 _)
    {V : X.Opens} (hV : IsAffineOpen V) (hc : s (IsLocalRing.closedPoint A) ∈ V) :
    (affineLocalSectionRetraction s V hc).comp (affineSectionCoefficientMap p V) =
      RingHom.id A := by
  have h : CommRingCat.ofHom
      ((affineLocalSectionRetraction s V hc).comp (affineSectionCoefficientMap p V)) =
        𝟙 (CommRingCat.of A) := by
    apply Spec.map_injective
    rw [CommRingCat.ofHom_comp, Spec.map_comp, affineSectionCoefficientMap_spec p hV,
      ← Category.assoc, affineLocalSectionRetraction_spec s hV hc, hs, Spec.map_id]
  exact congrArg CommRingCat.Hom.hom h

/-- The original retraction as an algebra map for the single original coefficient action. -/
def affineSectionAugmentation
    (p : X ⟶ Spec (.of A)) (s : Spec (.of A) ⟶ X) (hs : s ≫ p = 𝟙 _)
    {V : X.Opens} (hV : IsAffineOpen V) (hc : s (IsLocalRing.closedPoint A) ∈ V) :
    letI : Algebra A Γ(X, V) := (affineSectionCoefficientMap p V).toAlgebra
    Γ(X, V) →ₐ[A] A := by
  let : Algebra A Γ(X, V) := (affineSectionCoefficientMap p V).toAlgebra
  exact { affineLocalSectionRetraction s V hc with
    commutes' a := RingHom.congr_fun (affineLocalSectionRetraction_comp p s hs hV hc) a }

/-- Integrality and the actual section point give a domain on the chosen open. -/
theorem affineSection_isDomain [IsIntegral X] (s : Spec (.of A) ⟶ X)
    (V : X.Opens) (hc : s (IsLocalRing.closedPoint A) ∈ V) : IsDomain Γ(X, V) := by
  let : Nonempty V := ⟨⟨s (IsLocalRing.closedPoint A), hc⟩⟩
  infer_instance

end AlgebraicGeometry.Scheme
