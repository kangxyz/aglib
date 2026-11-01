/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Morphisms.FiniteEtale.BaseChange.Isomorphism
public import Mathlib.AlgebraicGeometry.Restrict

/-! # Finite-etale restriction through an original ambient isomorphism

The native restriction isomorphism and actual base-change composition transport
full faithfulness without selecting another category of covers.
-/

@[expose] public noncomputable section

open CategoryTheory

namespace AlgebraicGeometry.Scheme.FiniteEtale

universe u

/-- Full faithfulness on the actual inverse-image open transports across an ambient iso. -/
def restrictionFullyFaithfulCompIso {X Y Z : Scheme.{u}}
    (f : X ⟶ Y) (g : Y ⟶ Z) [IsIso g] (W : Z.Opens)
    (hf : (baseChange (f ∣_ g ⁻¹ᵁ W)).FullyFaithful) :
    (baseChange ((f ≫ g) ∣_ W)).FullyFaithful := by
  have hg : g ∣_ W = (g.preimageIso W).hom := by
    apply (cancel_mono W.ι).mp
    rw [morphismRestrict_ι, Hom.preimageIso_hom_ι]
  let : IsIso (g ∣_ W) := by rw [hg]; infer_instance
  let : (baseChange (g ∣_ W)).Full := baseChange_full_of_isIso _
  let : (baseChange (g ∣_ W)).Faithful := baseChange_faithful_of_isIso _
  let hgf := (Functor.FullyFaithful.ofFullyFaithful (baseChange (g ∣_ W))).comp hf
  let hc := hgf.ofIso (baseChangeComp (g ∣_ W) (f ∣_ g ⁻¹ᵁ W)).symm
  exact hc.ofIso (eqToIso (congrArg baseChange (morphismRestrict_comp f g W).symm))

end AlgebraicGeometry.Scheme.FiniteEtale
