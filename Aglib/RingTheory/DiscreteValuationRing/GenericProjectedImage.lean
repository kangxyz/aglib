/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.RingTheory.DiscreteValuationRing.GenericTensorResidue
public import Mathlib.Algebra.Algebra.Subalgebra.Tower

/-! # The actual generic image over the actual parameter residue field

Restricting the scalars of the existing generic tensor image changes neither
its carrier nor its ring structure. The scalar action is the exact composite
of the canonical parameter residue equivalence with the generic coefficient
embedding, as used by the actual generic source-target residue square.
-/

@[expose] public noncomputable section

open IsLocalRing
open scoped TensorProduct

namespace GenericParameterCentre

variable (R K : Type*) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
  [Field K] [Algebra (ResidueField R) K] (ι : Type*) (p : R) [Fact (Irreducible p)]

attribute [local instance] ParameterLocalization.algebraMap_isLocalHom
attribute [local instance] MvPolynomial.algebraMvPolynomial GenericParameterField.fractionAlgebra
attribute [local instance] Algebra.TensorProduct.rightAlgebra

local notation "k" => ResidueField R
local notation "R₁" => ParameterLocalization.Ring R ι p
local notation "F" => FractionRing (MvPolynomial ι k)
local notation "L" => FractionRing (MvPolynomial ι K)

/-- The original coefficient ring acts on the specified centre field through
its original residue map. -/
local instance projectedCoefficientAlgebra : Algebra R K :=
  ((algebraMap k K).comp (residue R)).toAlgebra
local instance projectedImageCoefficientTower : IsScalarTower R k K :=
  IsScalarTower.of_algebraMap_eq' rfl

/-- The actual parameter residue field acts on its native rational function
field through `ParameterLocalization.residueFieldAlgEquiv`. -/
local instance projectedResidueFieldAlgebra : Algebra (ResidueField R₁) F :=
  (ParameterLocalization.residueFieldAlgEquiv R ι p).toRingHom.toAlgebra

/-- The parameter residue field acts on the generic target through its native
residue equivalence followed by the original fraction-field inclusion. -/
local instance projectedResidueAlgebra : Algebra (ResidueField R₁) L :=
  ((algebraMap F L).comp
    (ParameterLocalization.residueFieldAlgEquiv R ι p).toRingHom).toAlgebra

local instance projectedImageResidueTower : IsScalarTower (ResidueField R₁) F L :=
  IsScalarTower.of_algebraMap_eq' rfl

variable {B : Type*} [CommRing B] [Algebra R B] (g : B →ₐ[R] K)

/-- The existing literal image, now over the actual source parameter residue field. -/
abbrev projectedImage : Subalgebra (ResidueField R₁) L :=
  (image R K ι p g).restrictScalars (ResidueField R₁)

/-- The existing source-to-image map, with unchanged source, carrier and ring operations. -/
def projectedSourceMap : B ⊗[R] R₁ →+* projectedImage R K ι p g :=
  ResidueRange.sourceMap (parameterResidue R ι p) (parameterResidue_surjective R ι p)
    Algebra.TensorProduct.includeRight.toRingHom (tensorPoint R K ι p g).toRingHom
    (tensorPoint_includeRight R K ι p g)

/-- Inclusion of the projected image recovers the actual tensor residue point. -/
@[simp] theorem coe_projectedSourceMap (a : B ⊗[R] R₁) :
    (projectedSourceMap R K ι p g a : L) = tensorPoint R K ι p g a := rfl

/-- Surjectivity comes from the existing literal range, not from an extra hypothesis. -/
theorem projectedSourceMap_surjective :
    Function.Surjective (projectedSourceMap R K ι p g) :=
  ResidueRange.sourceMap_surjective (parameterResidue R ι p)
    (parameterResidue_surjective R ι p) Algebra.TensorProduct.includeRight.toRingHom
    (tensorPoint R K ι p g).toRingHom (tensorPoint_includeRight R K ι p g)

/-- The actual parameter inclusion and actual residue quotient form the coefficient square. -/
theorem projectedSourceMap_comp_algebraMap :
    (projectedSourceMap R K ι p g).comp (algebraMap R₁ (B ⊗[R] R₁)) =
      (algebraMap (ResidueField R₁) (projectedImage R K ι p g)).comp (residue R₁) := by
  apply RingHom.ext
  intro a
  apply Subtype.ext
  exact DFunLike.congr_fun (tensorPoint_includeRight R K ι p g) a

/-- Restricting the target to its literal image leaves the actual centre unchanged. -/
theorem ker_projectedSourceMap :
    RingHom.ker (projectedSourceMap R K ι p g) =
      RingHom.ker (tensorPoint R K ι p g).toRingHom :=
  Ideal.ext fun _ => Subtype.ext_iff

/-- The existing fraction-field theorem applies to the very same image ring. -/
theorem isFractionRing_projectedImage {σ : Type*} (x : σ → B)
    (hx : IntermediateField.adjoin k (Set.range (fun i => g (x i))) = ⊤) :
    IsFractionRing (projectedImage R K ι p g) L :=
  isFractionRing_image R K ι p g x hx

end GenericParameterCentre
