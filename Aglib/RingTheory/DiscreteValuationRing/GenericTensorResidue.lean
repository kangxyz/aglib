/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.RingTheory.DiscreteValuationRing.ParameterResidue
public import Aglib.RingTheory.Kaehler.GenericFieldGenerators
public import Aglib.RingTheory.Kaehler.GenericSeparatingCoordinates
public import Aglib.RingTheory.Localization.ResidueRange

/-! # The actual generic-parameter residue image of the source tensor algebra

The parameter residue map supplies the coefficient field in the image. The
original source tensor ring is not given an action of that residue field.
-/

@[expose] public noncomputable section

open IsLocalRing
open scoped TensorProduct

namespace GenericParameterCentre

variable (R K : Type*) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
  [Field K] [Algebra (ResidueField R) K] (ι : Type*) (p : R) [Fact (Irreducible p)]

attribute [local instance] ParameterLocalization.algebraMap_isLocalHom
attribute [local instance] MvPolynomial.algebraMvPolynomial GenericParameterField.fractionAlgebra

local notation "k" => ResidueField R
local notation "R₁" => ParameterLocalization.Ring R ι p
local notation "F" => FractionRing (MvPolynomial ι k)
local notation "L" => FractionRing (MvPolynomial ι K)

/-- The original DVR acts on the coefficient field through its specified residue extension. -/
local instance genericParameterResidueAlgebra : Algebra R K :=
  ((algebraMap k K).comp (residue R)).toAlgebra
local instance : IsScalarTower R k K := IsScalarTower.of_algebraMap_eq' rfl

/-- The actual parameter residue quotient followed by the canonical residue-field equivalence. -/
def parameterResidue : R₁ →+* F :=
  (ParameterLocalization.residueFieldAlgEquiv R ι p).toRingHom.comp (residue R₁)

/-- Every parameter-field scalar has a preimage in the actual parameter DVR. -/
theorem parameterResidue_surjective : Function.Surjective (parameterResidue R ι p) :=
  (ParameterLocalization.residueFieldAlgEquiv R ι p).surjective.comp residue_surjective

/-- The parameter residue quotient preserves original residue coefficients. -/
@[simp] theorem parameterResidue_algebraMap (r : R) :
    parameterResidue R ι p (algebraMap R R₁ r) = algebraMap k F (residue R r) := by
  change ParameterLocalization.residueFieldAlgEquiv R ι p
    (residue R₁ (algebraMap R R₁ r)) = _
  rw [← ResidueField.algebraMap_residue]
  exact (ParameterLocalization.residueFieldAlgEquiv R ι p).commutes _

/-- Each actual parameter variable has its original generic residue. -/
@[simp] theorem parameterResidue_X (i : ι) :
    parameterResidue R ι p
      (algebraMap (MvPolynomial ι R) R₁ (MvPolynomial.X i)) =
      algebraMap (MvPolynomial ι k) F (MvPolynomial.X i) :=
  ParameterLocalization.residueFieldAlgEquiv_X R ι p i

/-- The actual parameter point in the enlarged coefficient field, over the original base. -/
def parameterPoint : R₁ →ₐ[R] L where
  __ := (algebraMap F L).comp (parameterResidue R ι p)
  commutes' r := by
    change algebraMap F L (parameterResidue R ι p (algebraMap R R₁ r)) = _
    rw [parameterResidue_algebraMap, ← IsScalarTower.algebraMap_apply k F L]
    exact (IsScalarTower.algebraMap_apply R k L r).symm

variable {B : Type*} [CommRing B] [Algebra R B] (g : B →ₐ[R] K)

/-- The source tensor point uses the original coefficient point and the actual parameter residue. -/
def tensorPoint : B ⊗[R] R₁ →ₐ[R] L :=
  Algebra.TensorProduct.lift ((IsScalarTower.toAlgHom R K L).comp g)
    (parameterPoint R K ι p) fun _ _ => Commute.all _ _

/-- The actual tensor point has the expected coefficient formula on pure tensors. -/
@[simp] theorem tensorPoint_tmul (b : B) (a : R₁) :
    tensorPoint R K ι p g (b ⊗ₜ[R] a) =
      algebraMap K L (g b) * algebraMap F L (parameterResidue R ι p a) := rfl

/-- The original source coordinates remain the same coefficient images. -/
theorem tensorPoint_includeLeft (b : B) :
    tensorPoint R K ι p g ((Algebra.TensorProduct.includeLeft : B →ₐ[R] B ⊗[R] R₁) b) =
      algebraMap K L (g b) := by
  change algebraMap K L (g b) * algebraMap F L (parameterResidue R ι p 1) = _
  rw [map_one, map_one, mul_one]

/-- The actual parameter inclusion supplies the scalar triangle for the residue range. -/
theorem tensorPoint_includeRight :
    (tensorPoint R K ι p g).toRingHom.comp Algebra.TensorProduct.includeRight.toRingHom =
      (algebraMap F L).comp (parameterResidue R ι p) := by
  ext a
  change algebraMap K L (g 1) * algebraMap F L (parameterResidue R ι p a) = _
  rw [map_one, map_one, one_mul]
  rfl

/-- The literal image of the actual source tensor point, with its genuine scalar closure. -/
abbrev image : Subalgebra F L :=
  ResidueRange.algebra (parameterResidue R ι p) (parameterResidue_surjective R ι p)
    Algebra.TensorProduct.includeRight.toRingHom (tensorPoint R K ι p g).toRingHom
    (tensorPoint_includeRight R K ι p g)

/-- Actual field-generating source coordinates make the target the fraction field of this image. -/
theorem isFractionRing_image {σ : Type*} (x : σ → B)
    (hx : IntermediateField.adjoin k (Set.range (fun i => g (x i))) = ⊤) :
    IsFractionRing (image R K ι p g) L := by
  apply ResidueRange.isFractionRing _ _ _ _ _
    (fun i => (Algebra.TensorProduct.includeLeft : B →ₐ[R] B ⊗[R] R₁) (x i))
  change IntermediateField.adjoin F (Set.range (fun i => tensorPoint R K ι p g
    ((Algebra.TensorProduct.includeLeft : B →ₐ[R] B ⊗[R] R₁) (x i)))) = ⊤
  simpa only [tensorPoint_includeLeft] using
    GenericParameterField.adjoin_coefficient_generators_eq_top k K ι (fun i => g (x i)) hx

variable {n : Type*} [Fintype n]

/-- The new linear coordinates use the same actual matrix parameter variables
in the source tensor ring, rather than independent target coefficients. -/
def liftedCoordinate (x : n → B) (i : n) :
    B ⊗[R] ParameterLocalization.Ring R (n × n) p :=
  ∑ l, Algebra.TensorProduct.includeRight
      (algebraMap (MvPolynomial (n × n) R) (ParameterLocalization.Ring R (n × n) p)
        (MvPolynomial.X (i, l))) *
      (Algebra.TensorProduct.includeLeft : B →ₐ[R]
        B ⊗[R] ParameterLocalization.Ring R (n × n) p) (x l)

/-- The actual source-coordinate lifts have exactly the already constructed
generic separating coordinates as their residues. -/
theorem tensorPoint_liftedCoordinate (x : n → B) (i : n) :
    tensorPoint R K (n × n) p g (liftedCoordinate R p x i) =
      GenericParameterField.coordinate (ResidueField R) K n (fun l => g (x l)) i := by
  have hright (a : ParameterLocalization.Ring R (n × n) p) :
      tensorPoint R K (n × n) p g
        ((Algebra.TensorProduct.includeRight : ParameterLocalization.Ring R (n × n) p →ₐ[R]
          B ⊗[R] ParameterLocalization.Ring R (n × n) p) a) =
        algebraMap (FractionRing (MvPolynomial (n × n) k))
          (FractionRing (MvPolynomial (n × n) K)) (parameterResidue R (n × n) p a) :=
    DFunLike.congr_fun (tensorPoint_includeRight R K (n × n) p g) a
  simp only [liftedCoordinate, map_sum, map_mul, tensorPoint_includeLeft,
    hright, parameterResidue_X, GenericParameterField.coordinate]

end GenericParameterCentre
