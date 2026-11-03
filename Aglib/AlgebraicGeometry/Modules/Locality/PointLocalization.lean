/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Modules.Pullback.FlatStalk
public import Aglib.AlgebraicGeometry.Stalk.FlatBaseChange
public import Mathlib.AlgebraicGeometry.PullbackCarrier

/-!
# Detecting module epimorphisms at a point and away from it

The original local-spectrum pullback of a scheme morphism and the inverse
image of the complementary open jointly detect zero module sheaves and
module epimorphisms. Both maps and the actual Cartesian square are retained;
no globally surjective localization, finiteness or coherence is asserted.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Scheme.Modules

variable {X Y T : Scheme.{u}} (x : X) (hx : IsClosed ({x} : Set X))
  (a : T ⟶ Y) (p : T ⟶ Spec (X.presheaf.stalk x)) (f : Y ⟶ X)
  (h : IsPullback a p f (X.fromSpecStalk x))

include h

private theorem isZero_of_localization_and_away (M : Y.Modules)
    (hlocal : IsZero ((pullback a).obj M))
    (haway : IsZero ((pullback
      (f ⁻¹ᵁ (⟨({x} : Set X)ᶜ, hx.isOpen_compl⟩ : X.Opens)).ι).obj M)) : IsZero M := by
  let U : X.Opens := ⟨({x} : Set X)ᶜ, hx.isOpen_compl⟩
  let : Flat (X.fromSpecStalk x) := Scheme.fromSpecStalk_flat X x
  let : Flat a := MorphismProperty.of_isPullback h.flip inferInstance
  apply (isZero_iff_stalks M).mpr
  intro y
  by_cases hy : f y = x
  · obtain ⟨t, ht, _⟩ := Scheme.exists_preimage_of_isPullback h y
      (IsLocalRing.closedPoint (X.presheaf.stalk x))
      (hy.trans (Scheme.fromSpecStalk_closedPoint (X := X) (x := x)).symm)
    have htzero := stalk_isZero_of_flat_pullback a M hlocal t
    exact ht ▸ htzero
  · let yU : (f ⁻¹ᵁ U).toScheme := ⟨y, hy⟩
    exact stalk_isZero_of_flat_pullback (f ⁻¹ᵁ U).ι M haway yU

/-- The original local-spectrum square and complementary open detect
an epimorphism of arbitrary module sheaves on the same original source. -/
theorem epi_of_localization_and_away {M N : Y.Modules} (φ : M ⟶ N)
    [Epi ((pullback a).map φ)]
    [Epi ((pullback (f ⁻¹ᵁ (⟨({x} : Set X)ᶜ, hx.isOpen_compl⟩ : X.Opens)).ι).map φ)] :
    Epi φ := by
  apply Preadditive.epi_of_isZero_cokernel
  apply isZero_of_localization_and_away x hx a p f h (cokernel φ)
  · exact (isZero_cokernel_of_epi ((pullback a).map φ)).of_iso
      (PreservesCokernel.iso (pullback a) φ)
  · exact (isZero_cokernel_of_epi
      ((pullback
        (f ⁻¹ᵁ (⟨({x} : Set X)ᶜ, hx.isOpen_compl⟩ : X.Opens)).ι).map φ)).of_iso
        (PreservesCokernel.iso
          (pullback (f ⁻¹ᵁ (⟨({x} : Set X)ᶜ, hx.isOpen_compl⟩ : X.Opens)).ι) φ)

end AlgebraicGeometry.Scheme.Modules
