/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.RationalMap.QuasiDomination.ReverseIdentification
public import Aglib.AlgebraicGeometry.RationalMap.QuasiDomination.ReverseGraph
public import Aglib.AlgebraicGeometry.RationalMap.QuasiDomination.Basic
public import Aglib.AlgebraicGeometry.Blowup.AdmissibleSequence.OpenExtension

/-!
# Extending the actual reverse modification into the ambient model

This is the sequence-level reverse quasi-domination construction. The reverse
domain is first identified with the actual replayed sequence, which then
extends from the original open model by Cartesian open extension. The larger
closed graph is retained. No finite sequence is replaced by a single blowup.
-/

@[expose] public noncomputable section

open CategoryTheory Limits

universe u

namespace AlgebraicGeometry.Scheme.QuasiDomination

/-- The reverse map is an actual admissible sequence and extends to the ambient
model. Relative separatedness is used to recover its triangle from the original
schematically dense source; properness uses the actual proper modification. -/
theorem exists_reverse_open_extension
    {X T V W Y S : Scheme.{u}} [IsLocallyNoetherian X]
    (U : X.Opens) (β : T ⟶ X) (hβ : Blowup.AdmissibleSequence U β)
    (pX : X ⟶ S) [IsSeparated pX] (pY : Y ⟶ S)
    (φ : V ⟶ X) [LocallyOfFiniteType φ]
    (v : V ⟶ Y) [IsOpenImmersion v] [QuasiCompact v]
    (hφ : φ ≫ pX = v ≫ pY)
    [IsClosedImmersion (pullback.lift φ v hφ)]
    (u : U.toScheme ⟶ V) [IsOpenImmersion u] [QuasiCompact u]
    [IsSchemeTheoreticallyDominant u] (hu : u ≫ φ = U.ι)
    (j : W ⟶ T) (ψ : W ⟶ V)
    (wS : j ≫ (β ≫ pX) = ψ ≫ (v ≫ pY))
    [IsClosedImmersion (pullback.lift j ψ wS)]
    (k : U.toScheme ⟶ W) [IsSchemeTheoreticallyDominant k]
    (hkj : k ≫ j ≫ β = U.ι) (hkψ : k ≫ ψ = u) :
    ∃ (Yn : Scheme.{u}) (δ : Yn ⟶ Y) (r : W ⟶ Yn),
      Blowup.AdmissibleSequence (u ≫ v).opensRange δ ∧
      IsPullback r ψ δ v ∧ IsOpenImmersion r ∧ IsProper ψ ∧
      Blowup.AdmissibleSequence u.opensRange ψ ∧
      IsClosedImmersion (pullback.lift j (ψ ≫ v)
        (wS.trans (Category.assoc ψ v pY).symm)) := by
  have w : j ≫ β = ψ ≫ φ := by
    apply hom_ext_of_schemeTheoreticallyDominant k pX
    · simpa only [Category.assoc] using
        wS.trans (congrArg (fun z ↦ ψ ≫ z) hφ.symm)
    · calc
        k ≫ (j ≫ β) = U.ι := hkj
        _ = (k ≫ ψ) ≫ φ := ((congrArg (fun z ↦ z ≫ φ) hkψ).trans hu).symm
        _ = k ≫ (ψ ≫ φ) := Category.assoc _ _ _
  let : IsProper β := hβ.isProper
  let : IsClosedImmersion (pullback.lift j ψ w) :=
    isClosedImmersion_reverseGraph β φ pX (v ≫ pY) hφ j ψ w wS
  let : IsProper ψ :=
    isProper_of_reverse_closedGraph β φ pX (v ≫ pY) hφ j ψ w wS
  obtain ⟨Vn, γ, a, t, e, _, _, _, _, _, _, hψ⟩ :=
    exists_reverse_domain_identification U β hβ φ u hu j ψ w k hkj hkψ
  let UY := (u ≫ v).opensRange
  have hψ' : Blowup.AdmissibleSequence (v ⁻¹ᵁ UY) ψ := by
    simpa only [UY, Hom.opensRange_comp, Hom.preimage_image_eq] using hψ
  obtain ⟨Yn, δ, r, hδ, hr⟩ := hψ'.exists_open_extension v UY
  let : IsOpenImmersion r := MorphismProperty.of_isPullback hr.flip inferInstance
  refine ⟨Yn, δ, r, hδ, hr, inferInstance, inferInstance, hψ, ?_⟩
  exact isClosedImmersion_enlargedReverseGraph β φ pX pY v hφ j ψ w
    (wS.trans (Category.assoc ψ v pY).symm)

end AlgebraicGeometry.Scheme.QuasiDomination
