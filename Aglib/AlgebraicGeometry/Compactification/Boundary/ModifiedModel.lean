/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Blowup.AdmissibleSequence.Density
public import Aglib.AlgebraicGeometry.Morphisms.IsIso.OpenLift
public import Aglib.AlgebraicGeometry.Morphisms.IsIso.OpenRestriction

/-!
# Protected models after ambient modification

The unchanged proper model over a protected open is transported using the
actual restriction isomorphism. Schematic density comes from the recorded
admissible sequence, never from an arbitrary proper comparison.
-/

@[expose] public noncomputable section
set_option autoImplicit false
open CategoryTheory Limits
universe u

namespace AlgebraicGeometry.Scheme.Compactification

/-- Transport a proper open model and its original dense source through an
actual ambient admissible sequence. -/
theorem protected_model_transfer
    {X Y Y' : Scheme.{u}} (V : Y.Opens)
    [QuasiCompact V.ι] [IsSchemeTheoreticallyDominant V.ι]
    (q : V.toScheme ⟶ X) [IsProper q]
    (W : X.Opens) [IsIso (q ∣_ W)]
    (s : W.toScheme ⟶ V.toScheme) [IsSchemeTheoreticallyDominant s]
    (hs : s ≫ q = W.ι)
    (β : Y' ⟶ Y) (hβ : Blowup.AdmissibleSequence V β) :
    letI : IsIso (β ∣_ V) := hβ.restrict_isIso
    let q' := (β ∣_ V) ≫ q
    IsProper q' ∧ IsIso (q' ∣_ W) ∧
      IsSchemeTheoreticallyDominant (s ≫ inv (β ∣_ V) ≫ (β ⁻¹ᵁ V).ι) ∧
      (letI : IsIso (q' ∣_ W) := by
        dsimp only [q']
        exact Scheme.Hom.isIso_restrict_comp (β ∣_ V) q W
       s ≫ inv (β ∣_ V) = inv (q' ∣_ W) ≫ (q' ⁻¹ᵁ W).ι) := by
  let : IsIso (β ∣_ V) := hβ.restrict_isIso
  dsimp only
  let : IsSchemeTheoreticallyDominant (β ⁻¹ᵁ V).ι :=
    hβ.preimage_open_isSchemeTheoreticallyDominant
  let : IsIso (((β ∣_ V) ≫ q) ∣_ W) := by
    exact Scheme.Hom.isIso_restrict_comp (β ∣_ V) q W
  refine ⟨inferInstance, inferInstance, inferInstance, ?_⟩
  apply Scheme.Hom.eq_inv_restrict_comp
  rw [Category.assoc, IsIso.inv_hom_id_assoc]
  exact hs

end AlgebraicGeometry.Scheme.Compactification
