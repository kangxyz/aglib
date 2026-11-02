/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Spec.HartogsEtaleSectionExtension
public import Aglib.AlgebraicGeometry.Spec.ScalarMapFaithfulness
public import Aglib.AlgebraicGeometry.Morphisms.FiniteEtale.SectionLifting

/-! # Hartogs extension retaining the prescribed affine section

Fullness on the original open lifts the prescribed section. Injective scalars
on its original inverse image retain the whole affine triangle after extension.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Scheme

universe u

/-- The original affine section lands in the etale locus when its restriction
lifts by finite-etale fullness and both ambient scalar maps satisfy Hartogs. -/
theorem etaleAt_prescribedSection_of_hartogs
    {A B C : Type u} [CommRing A] [CommRing B] [CommRing C]
    (τ : B →+* C) (W : (Spec (.of B)).Opens)
    (ζ : Spec (.of A) ⟶ Spec (.of B))
    (a : Spec (.of A) ⟶ Spec (.of C))
    (ha : a ≫ Spec.map (CommRingCat.ofHom τ) = ζ)
    [IsFinite (Spec.map (CommRingCat.ofHom τ) ∣_ W)]
    [Etale (Spec.map (CommRingCat.ofHom τ) ∣_ W)]
    [QuasiCompact (Spec.map (CommRingCat.ofHom τ) ⁻¹ᵁ W).ι]
    [QuasiSeparated (Spec.map (CommRingCat.ofHom τ) ⁻¹ᵁ W).ι]
    [(FiniteEtale.baseChange (ζ ∣_ W)).Full]
    (hW : Function.Bijective (affineScalarMap W.ι))
    (hV : Function.Bijective
      (affineScalarMap (Spec.map (CommRingCat.ofHom τ) ⁻¹ᵁ W).ι))
    (hU : Function.Injective (affineScalarMap (ζ ⁻¹ᵁ W).ι)) :
    ∀ x : Spec (.of A), (Spec.map (CommRingCat.ofHom τ)).etaleAt (a x) := by
  let f := Spec.map (CommRingCat.ofHom τ)
  let U := ζ ⁻¹ᵁ W
  let V := f ⁻¹ᵁ W
  have hUV : U ≤ a ⁻¹ᵁ V := by
    change ζ ⁻¹ᵁ W ≤ a ⁻¹ᵁ (f ⁻¹ᵁ W)
    rw [← Hom.comp_preimage, ha]
  let a₀ : U.toScheme ⟶ V.toScheme := a.resLE V U hUV
  have ha₀ : a₀ ≫ (f ∣_ W) = ζ ∣_ W := by
    apply (cancel_mono W.ι).mp
    rw [Category.assoc, morphismRestrict_ι, ← Category.assoc,
      Hom.resLE_comp_ι, Category.assoc, ha, morphismRestrict_ι]
  obtain ⟨s, hs, hpres⟩ := FiniteEtale.exists_section_of_baseChange_full
    (ζ ∣_ W) (FiniteEtale.mk (f ∣_ W)) a₀ ha₀
  obtain ⟨t, _, ht, _, het⟩ := exists_open_section_of_hartogsScalar
    W.ι V.ι τ (f ∣_ W) (morphismRestrict_ι f W) hW hV s hs
  have hmatch : ζ ≫ t = a := by
    apply affine_hom_ext_of_scalar_injective U.ι hU
    calc
      U.ι ≫ (ζ ≫ t) = (ζ ∣_ W) ≫ (W.ι ≫ t) := by
        rw [← Category.assoc, ← morphismRestrict_ι, Category.assoc]
      _ = (ζ ∣_ W) ≫ (s ≫ V.ι) := by rw [ht]
      _ = a₀ ≫ V.ι := by rw [← Category.assoc, hpres]
      _ = U.ι ≫ a := Hom.resLE_comp_ι a hUV
  intro x
  have hx := het (ζ x)
  have he := congrArg (fun g : Spec (.of A) ⟶ Spec (.of C) => g x) hmatch
  exact he ▸ hx

end AlgebraicGeometry.Scheme
