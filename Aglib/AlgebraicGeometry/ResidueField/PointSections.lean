/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Mathlib.AlgebraicGeometry.ResidueField

/-!
# Original stalk and residue-point section maps

The four generic point-section laws are moved once from
`Cohomology/Proper/FibreIdempotents`. Its original names remain thin facades.
The affine evaluation kernel is the original chart prime, through the actual
germ and residue quotient. No properness, closed-point, or Noetherian premise
is used, and no alternate residue field or algebra structure is selected.
-/

@[expose] public noncomputable section

open CategoryTheory Opposite TopologicalSpace

universe u

namespace AlgebraicGeometry.Scheme

variable {Y : Scheme.{u}} (y : Y)

/-- Every neighborhood of a point pulls back to the whole spectrum of its actual stalk. -/
theorem stalkRestriction_le (U : Y.Opens) (hy : y ∈ U) :
    ⊤ ≤ (Y.fromSpecStalk y) ⁻¹ᵁ U :=
  (Scheme.preimage_eq_top_of_closedPoint_mem (Y.fromSpecStalk y)
    (by simpa only [Scheme.fromSpecStalk_closedPoint] using hy)).ge

/-- The original stalk-point section map is the actual germ followed by the Spec comparison. -/
theorem stalkPoint_appLE (U : Y.Opens) (hy : y ∈ U) :
    (Y.fromSpecStalk y).appLE U ⊤ (stalkRestriction_le y U hy) =
      Y.presheaf.germ U y hy ≫ (Scheme.ΓSpecIso (Y.presheaf.stalk y)).inv := by
  rw [Scheme.Hom.appLE, Scheme.fromSpecStalk_app hy, Category.assoc, Category.assoc,
    ← Functor.map_comp]
  have hmap : ((homOfLE le_top).op ≫ (homOfLE (stalkRestriction_le y U hy)).op :
      (op ⊤ : (Spec (Y.presheaf.stalk y)).Opensᵒᵖ) ⟶ op ⊤) = 𝟙 _ :=
    Subsingleton.elim _ _
  rw [hmap, CategoryTheory.Functor.map_id, Category.comp_id]

/-- Every neighborhood pulls back to the whole spectrum of the actual residue field. -/
theorem residueRestriction_le (U : Y.Opens) (hy : y ∈ U) :
    ⊤ ≤ (Y.fromSpecResidueField y) ⁻¹ᵁ U := by
  intro z _
  change Y.fromSpecResidueField y z ∈ U
  rw [Scheme.fromSpecResidueField_apply]
  exact hy

/-- Actual residue-point restriction is the germ, residue map and original Spec comparison. -/
theorem residuePoint_appLE (U : Y.Opens) (hy : y ∈ U) :
    (Y.fromSpecResidueField y).appLE U ⊤ (residueRestriction_le y U hy) =
      Y.presheaf.germ U y hy ≫ Y.residue y ≫
        (Scheme.ΓSpecIso (Y.residueField y)).inv := by
  have hcomp : (Y.fromSpecResidueField y).appLE U ⊤ (residueRestriction_le y U hy) =
      (Y.fromSpecStalk y).appLE U ⊤ (stalkRestriction_le y U hy) ≫
        (Spec.map (Y.residue y)).appTop := by
    change (Spec.map (Y.residue y) ≫ Y.fromSpecStalk y).appLE U ⊤ _ = _
    exact (Scheme.Hom.appLE_comp_appLE (Spec.map (Y.residue y)) (Y.fromSpecStalk y)
      U ⊤ ⊤ (stalkRestriction_le y U hy) (by simp)).symm.trans
        (congrArg (fun k => (Y.fromSpecStalk y).appLE U ⊤
          (stalkRestriction_le y U hy) ≫ k)
            (by simpa only [Scheme.Hom.preimage_top] using
              ((Spec.map (Y.residue y)).appLE_eq_app (U := ⊤))))
  rw [hcomp, stalkPoint_appLE, Category.assoc, ← Scheme.ΓSpecIso_inv_naturality]

/-- The kernel of the original evaluation is exactly the native affine chart prime. -/
theorem ker_evaluation_eq_primeIdealOf {X : Scheme.{u}}
    (x : X) (U : X.affineOpens) (hx : x ∈ U.1) :
    RingHom.ker (X.evaluation U.1 x hx).hom =
      (U.2.primeIdealOf ⟨x, hx⟩).asIdeal := by
  have hp := congrArg (fun p : PrimeSpectrum Γ(X, U) => p.asIdeal)
    (U.2.primeIdealOf_eq_map_closedPoint ⟨x, hx⟩)
  change (U.2.primeIdealOf ⟨x, hx⟩).asIdeal =
    (IsLocalRing.maximalIdeal (X.presheaf.stalk x)).comap
      (X.presheaf.germ U.1 x hx).hom at hp
  change RingHom.ker ((IsLocalRing.residue (X.presheaf.stalk x)).comp
    (X.presheaf.germ U.1 x hx).hom) = _
  rw [← RingHom.comap_ker, IsLocalRing.ker_residue]
  exact hp.symm

end AlgebraicGeometry.Scheme
