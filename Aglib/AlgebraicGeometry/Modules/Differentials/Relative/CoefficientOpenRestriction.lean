/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Modules.Differentials.Relative.Coefficient
public import Aglib.AlgebraicGeometry.Modules.Differentials.Relative.Restriction


/-!
# The original differential coefficient along an open immersion

The original coefficient map is the restriction adjoint of the original
relative-differential restriction isomorphism. The proof checks the actual
derivation generators and original structure-section map; an object
isomorphism alone is not used to identify arrows.
-/

@[expose] public noncomputable section

open CategoryTheory Opposite
open AlgebraicGeometry.Scheme.Modules AlgebraicGeometry.Scheme.Modules.Differentials

universe u

namespace AlgebraicGeometry.Scheme.Modules.Differentials

variable {X U T : Scheme.{u}} (a : X ⟶ T) (j : U ⟶ X) [IsOpenImmersion j]

/-- The original coefficient arrow is the original open-restriction adjoint. -/
theorem differentialCoefficient_restrictAdjoint :
    differentialCoefficient a j =
      (Scheme.Modules.restrictAdjunction j).homEquiv _ _
        (relativeDifferentialRestrictIso a j).hom := by
  apply relativeDifferentialSheaf_hom_ext a _
  intro V z
  rw [differentialCoefficient_d]
  symm
  rw [Adjunction.homEquiv_unit]
  change (relativeDifferentialRestrictIso a j).hom.val.app (op (j ⁻¹ᵁ V.unop))
    ((relativeDifferentialSheaf a).val.map (homOfLE (j.image_preimage_le V.unop)).op
      ((relativeDifferentialDerivation a).d z)) = _
  rw [← relativeDifferentialDerivation_restrict]
  erw [relativeDifferentialRestrictIso_hom_d]
  congr 1
  have h := ConcreteCategory.congr_hom (j.app_appIso_inv V.unop) z
  change (j.appIso (j ⁻¹ᵁ V.unop)).inv (j.app V.unop z) =
    X.presheaf.map (homOfLE (j.image_preimage_le V.unop)).op z at h
  rw [← h]
  exact ConcreteCategory.congr_hom (j.appIso (j ⁻¹ᵁ V.unop)).inv_hom_id (j.app V.unop z)

/-- Original module pullback agrees with original open restriction on differentials. -/
theorem differentialPullback_restrict :
    (Scheme.Modules.restrictFunctorIsoPullback j).hom.app (relativeDifferentialSheaf a) ≫
      differentialPullback a j = (relativeDifferentialRestrictIso a j).hom := by
  let adj := Scheme.Modules.restrictAdjunction j
  let padj := Scheme.Modules.pullbackPushforwardAdjunction j
  let m := relativeDifferentialSheaf a
  let e := (Scheme.Modules.restrictFunctorIsoPullback j).hom.app m
  apply (adj.homEquiv _ _).injective
  have hu := Adjunction.homEquiv_leftAdjointUniq_hom_app adj padj m
  have hn := adj.homEquiv_naturality_right e (differentialPullback a j)
  exact hn.trans
    ((congrArg (fun t => t ≫ (Scheme.Modules.pushforward j).map
      (differentialPullback a j)) hu).trans
      ((Adjunction.homEquiv_unit padj _ _ (differentialPullback a j)).symm.trans
        ((differentialPullback_adjoint a j).trans (differentialCoefficient_restrictAdjoint a j))))

end AlgebraicGeometry.Scheme.Modules.Differentials
