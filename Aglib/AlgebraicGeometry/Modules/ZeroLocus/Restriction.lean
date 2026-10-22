/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Modules.Invertible.ZeroLocus.Uniqueness
public import Mathlib.AlgebraicGeometry.IdealSheaf.Functorial

/-! # Actual image ideals under open restriction -/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

universe u
open CategoryTheory Opposite

namespace AlgebraicGeometry.Scheme.Modules.Hom

/-- Restricting the actual map to the structure module restricts its image ideal.
This statement uses the structural ring isomorphism of an open immersion. -/
theorem imageIdealData_restrict {U X : Scheme.{u}}
    (j : U ⟶ X) [IsOpenImmersion j] {M : X.Modules} [M.IsQuasicoherent]
    (φ : M ⟶ SheafOfModules.unit X.ringCatSheaf) :
    imageIdealData ((restrictFunctor j).map φ ≫ (restrictUnitIso j).hom) =
      (imageIdealData φ).comap j := by
  apply Scheme.IdealSheafData.ext
  funext V
  rw [imageIdealData_eq _ (imageIdealLocalizes_of_isQuasicoherent _) V,
    Scheme.IdealSheafData.ideal_comap_of_isOpenImmersion,
    imageIdealData_eq φ (imageIdealLocalizes_of_isQuasicoherent φ)]
  ext a
  change (∃ m, (j.appIso V.val).hom (φ.val.app (op (j ''ᵁ V.val)) m) = a) ↔
    ∃ m, φ.val.app (op (j ''ᵁ V.val)) m = (j.appIso V.val).inv a
  constructor
  · rintro ⟨m, hm⟩
    refine ⟨m, ?_⟩
    have h := congrArg (fun a => (j.appIso V.val).inv a) hm
    simpa only [Iso.hom_inv_id_apply] using h
  · rintro ⟨m, hm⟩
    refine ⟨m, ?_⟩
    rw [hm]
    exact (j.appIso V.val).inv_hom_id_apply a

end AlgebraicGeometry.Scheme.Modules.Hom
