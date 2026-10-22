/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Blowup.BoundarySeparation.Locality
public import Aglib.AlgebraicGeometry.IdealSheaf.PowerContainment

/-!
# Actual boundary ideals from relative closedness

For a quasi-compact immersion whose image is closed over the larger protected
open, the ideals in Conrad's boundary-separation argument can be constructed.
The first ideal is the vanishing ideal of the closure of the protected boundary.
The second is a positive power of the vanishing ideal of the part of that
closure outside the larger open. Noetherianity of the ambient scheme supplies
one uniform exponent for the actual scheme-theoretic containment.
-/

@[expose] public noncomputable section
set_option autoImplicit false
open CategoryTheory Limits TopologicalSpace AlgebraicGeometry
universe u

namespace AlgebraicGeometry.Scheme.Blowup

/-- Relative closedness supplies actual ideals satisfying all hypotheses of
boundary separation, including the containment in the original kernel plus the
square of the first ideal. Only the ambient scheme `Z` must be Noetherian. -/
theorem exists_boundary_ideals {X Z Y : Scheme.{u}} [IsNoetherian Z]
    (p : Z ⟶ X) (f : Y ⟶ Z) [IsImmersion f] [QuasiCompact f]
    (U V : X.Opens) (_hUV : U ≤ V) (hfU : Set.range (f ≫ p) ⊆ U)
    (hclosed : IsClosed ((p ⁻¹ᵁ V).ι ⁻¹' Set.range f)) :
    ∃ I₁ I₂ : X.IdealSheafData,
      ((V : Set X) \ (U : Set X) ⊆ I₁.support) ∧
      ((I₁.support : Set X) ⊆ (U : Set X)ᶜ) ∧
      ((I₂.support : Set X) ⊆ (I₁.support : Set X) ∩ (V : Set X)ᶜ) ∧
      I₂.comap p ≤ (I₁ ^ 2).comap p ⊔ f.ker := by
  let K := Scheme.IdealSheafData.vanishingIdeal
    (Closeds.closure ((V : Set X) \ (U : Set X)))
  have hK : (V : Set X) \ (U : Set X) ⊆ K.support := by
    change (V : Set X) \ (U : Set X) ⊆ closure ((V : Set X) \ (U : Set X))
    exact subset_closure
  have hKU : (K.support : Set X) ⊆ (U : Set X)ᶜ := by
    change closure ((V : Set X) \ (U : Set X)) ⊆ (U : Set X)ᶜ
    exact closure_minimal (fun _ hx => hx.2) U.isOpen.isClosed_compl
  let L := Scheme.IdealSheafData.vanishingIdeal
    (⟨(K.support : Set X) ∩ (V : Set X)ᶜ,
      K.support.isClosed.inter V.isOpen.isClosed_compl⟩ : Closeds X)
  have hL : (L.support : Set X) = (K.support : Set X) ∩ (V : Set X)ᶜ := rfl
  let W := p ⁻¹ᵁ V
  have hclosure : W.ι ⁻¹' closure (Set.range f) = W.ι ⁻¹' Set.range f := by
    rw [W.ι.isOpenEmbedding.isOpenMap.preimage_closure_eq_closure_preimage W.ι.continuous]
    exact hclosed.closure_eq
  have hsupp : ((K ^ 2).comap p ⊔ f.ker).support ≤ (L.comap p).support := by
    intro z hz
    rw [Scheme.IdealSheafData.support_sup] at hz
    have hzK : p z ∈ K.support := by
      have h := hz.1
      rw [Scheme.IdealSheafData.support_comap, K.support_pow 2 (by decide)] at h
      exact h
    rw [Scheme.IdealSheafData.support_comap]
    change p z ∈ (L.support : Set X)
    rw [hL]
    refine ⟨hzK, ?_⟩
    intro hzV
    have hzclosure : z ∈ closure (Set.range f) := by
      simpa only [f.support_ker] using hz.2
    have hzrange : z ∈ Set.range f := by
      change (⟨z, hzV⟩ : W.toScheme) ∈ W.ι ⁻¹' Set.range f
      rw [← hclosure]
      exact hzclosure
    obtain ⟨y, hy⟩ := hzrange
    have hzU : p z ∈ U := by
      rw [← hy]
      exact hfU ⟨y, rfl⟩
    exact hKU hzK hzU
  obtain ⟨n, hn, hle, hs⟩ :=
    Scheme.IdealSheafData.exists_pos_pow_comap_le_of_support_le
      p L ((K ^ 2).comap p ⊔ f.ker) hsupp
  refine ⟨K, L ^ n, hK, hKU, ?_, hle⟩
  rw [hs]
  exact hL.le

/-- Actual ideal choice and the canonical proper boundary blowup, with no
ideal-containment supplier. The relative closedness hypothesis concerns the
image of the original immersion over `V`, not an asserted base-change identity
for schematic image. -/
theorem exists_canonical_boundary_separation {X Z Y : Scheme.{u}}
    [IsLocallyNoetherian X] [IsNoetherian Z]
    (p : Z ⟶ X) (f : Y ⟶ Z) [IsImmersion f] [QuasiCompact f]
    (U V : X.Opens) (hUV : U ≤ V) (hfU : Set.range (f ≫ p) ⊆ U)
    (hclosed : IsClosed ((p ⁻¹ᵁ V).ι ⁻¹' Set.range f)) :
    ∃ I₁ I₂ : X.IdealSheafData,
      ((V : Set X) \ (U : Set X) ⊆ I₁.support) ∧
      ((I₁.support : Set X) ⊆ (U : Set X)ᶜ) ∧
      ((I₂.support : Set X) ⊆ (I₁.support : Set X) ∩ (V : Set X)ᶜ) ∧
      (I₂.comap p ≤ (I₁ ^ 2).comap p ⊔ f.ker) ∧
      let B := blowupDatum (I₁ ⊔ I₂)
      IsProper B.map ∧ IsIso (B.map ∣_ V) ∧
        Disjoint
          (closure (Set.range (pullback.snd f (pullback.fst p B.map))))
          (pullback.snd p B.map ⁻¹'
            closure (B.map ⁻¹' ((V : Set X) \ (U : Set X)))) := by
  obtain ⟨I₁, I₂, hI₁, hI₁U, hI₂, hcontain⟩ :=
    exists_boundary_ideals p f U V hUV hfU hclosed
  exact ⟨I₁, I₂, hI₁, hI₁U, hI₂, hcontain,
    canonical_boundary_separation p f U V hUV hfU I₁ I₂ hI₁ hI₁U hI₂ hcontain⟩

end AlgebraicGeometry.Scheme.Blowup
