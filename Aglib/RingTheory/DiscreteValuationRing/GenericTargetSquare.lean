/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.RingTheory.DiscreteValuationRing.GenericTargetResidue
public import Aglib.RingTheory.DiscreteValuationRing.GenericTensorResidue
public import Aglib.RingTheory.DiscreteValuationRing.ParameterMap

/-! # The actual generic source-target residue square

The original coefficient and residue maps extend using the same parameters on
both DVRs. The constructed generic centre embedding intertwines the actual
source tensor point and target tensor point, not just abstract field embeddings.
-/

@[expose] public noncomputable section

open IsLocalRing MvPolynomial
open scoped TensorProduct

namespace GenericParameterCentre

variable (R S K ι : Type*) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
  [CommRing S] [IsDomain S] [IsDiscreteValuationRing S] [Algebra R S]
  [IsLocalHom (algebraMap R S)] [Field K] [Algebra (ResidueField R) K]
  [Finite ι] (p : R) [Fact (Irreducible p)]
  [Fact (Irreducible (algebraMap R S p))]

attribute [local instance] ParameterLocalization.algebraMap_isLocalHom
attribute [local instance] MvPolynomial.algebraMvPolynomial GenericParameterField.fractionAlgebra

local notation "k" => ResidueField R
local notation "R₁" => ParameterLocalization.Ring R ι p
local notation "S₁" => ParameterLocalization.Ring S ι (algebraMap R S p)
local notation "F" => FractionRing (MvPolynomial ι k)
local notation "L" => FractionRing (MvPolynomial ι K)

/-- The original coefficient ring acts on the centre field through the given
residue-field algebra and the original residue map. -/
local instance genericTargetCoefficientAlgebra : Algebra R K :=
  ((algebraMap k K).comp (residue R)).toAlgebra
local instance : IsScalarTower R k K := IsScalarTower.of_algebraMap_eq' rfl

/-- The new residue embedding uses the specified old embedding, without new parameters. -/
abbrev targetResidueEmbedding (e : K →ₐ[ResidueField R] ResidueField S) :
    FractionRing (MvPolynomial ι K) →+* ResidueField
      (ParameterLocalization.Ring S ι (algebraMap R S p)) :=
  ParameterLocalization.genericCentreResidueEmbedding S K ι (algebraMap R S p) e.toRingHom

/-- The actual parameter coefficient maps and residue maps form a commutative square. -/
theorem targetResidueEmbedding_parameterPoint (e : K →ₐ[ResidueField R] ResidueField S) (a : R₁) :
    targetResidueEmbedding R S K ι p e (parameterPoint R K ι p a) =
      residue S₁ (ParameterLocalization.parameterMap R S ι p a) := by
  have h : (targetResidueEmbedding R S K ι p e).comp
      (parameterPoint R K ι p).toRingHom =
        (residue S₁).comp (ParameterLocalization.parameterMap R S ι p).toRingHom := by
    apply IsLocalization.ringHom_ext (ParameterLocalization.parameterIdeal R ι p).primeCompl
    apply MvPolynomial.ringHom_ext
    · intro r
      change targetResidueEmbedding R S K ι p e
        (parameterPoint R K ι p (algebraMap R R₁ r)) =
          residue S₁ (ParameterLocalization.parameterMap R S ι p (algebraMap R R₁ r))
      rw [AlgHom.commutes, AlgHom.commutes,
        IsScalarTower.algebraMap_apply R K L,
        ParameterLocalization.genericCentreResidueEmbedding_coefficient]
      change algebraMap (ResidueField S) (ResidueField S₁)
        (e (algebraMap k K (residue R r))) = residue S₁ (algebraMap R S₁ r)
      rw [e.commutes, ResidueField.algebraMap_residue,
        ResidueField.algebraMap_residue, ← IsScalarTower.algebraMap_apply R S S₁]
    · intro i
      change targetResidueEmbedding R S K ι p e
        (algebraMap F L (parameterResidue R ι p
          (algebraMap (MvPolynomial ι R) R₁ (X i)))) =
            residue S₁ (ParameterLocalization.parameterMap R S ι p
              (algebraMap (MvPolynomial ι R) R₁ (X i)))
      rw [parameterResidue_X]
      change targetResidueEmbedding R S K ι p e
        (GenericParameterField.fractionMap k K ι
          (algebraMap (MvPolynomial ι k) F (X i))) = _
      rw [GenericParameterField.fractionMap_X,
        ParameterLocalization.genericCentreResidueEmbedding_X,
        ParameterLocalization.parameterMap_X]
  exact DFunLike.congr_fun h a

/-- The same actual embedding is linear over the actual source parameter residue field.
Both actions are constructed from the canonical residue equivalence and parameter map. -/
def targetResidueAlgEmbedding (e : K →ₐ[ResidueField R] ResidueField S) :
    letI : Algebra R₁ S₁ := (ParameterLocalization.parameterMap R S ι p).toRingHom.toAlgebra
    letI : IsLocalHom (algebraMap R₁ S₁) :=
      ParameterLocalization.parameterMap_isLocalHom R S ι p
    letI : Algebra (ResidueField R₁) L :=
      ((algebraMap F L).comp
        (ParameterLocalization.residueFieldAlgEquiv R ι p).toRingHom).toAlgebra
    L →ₐ[ResidueField R₁] ResidueField S₁ := by
  let : Algebra R₁ S₁ := (ParameterLocalization.parameterMap R S ι p).toRingHom.toAlgebra
  let : IsLocalHom (algebraMap R₁ S₁) :=
    ParameterLocalization.parameterMap_isLocalHom R S ι p
  let : Algebra (ResidueField R₁) L :=
    ((algebraMap F L).comp
      (ParameterLocalization.residueFieldAlgEquiv R ι p).toRingHom).toAlgebra
  refine { targetResidueEmbedding R S K ι p e with commutes' := ?_ }
  intro r
  obtain ⟨a, rfl⟩ := residue_surjective r
  change targetResidueEmbedding R S K ι p e
    (algebraMap F L (ParameterLocalization.residueFieldAlgEquiv R ι p
      (residue R₁ a))) = residue S₁ (ParameterLocalization.parameterMap R S ι p a)
  exact targetResidueEmbedding_parameterPoint R S K ι p e a

variable {B : Type*} [CommRing B] [Algebra R B]
  (g : B →ₐ[R] K) (χ : B →ₐ[R] S)

/-- The actual source tensor maps to the actual target parameter DVR. -/
def tensorTarget : B ⊗[R] R₁ →ₐ[R] S₁ :=
  Algebra.TensorProduct.lift ((IsScalarTower.toAlgHom R S S₁).comp χ)
    (ParameterLocalization.parameterMap R S ι p) fun _ _ => Commute.all _ _

omit [IsLocalHom (algebraMap R S)] in
@[simp] theorem tensorTarget_tmul (b : B) (a : R₁) :
    tensorTarget R S ι p χ (b ⊗ₜ[R] a) =
      algebraMap S S₁ (χ b) * ParameterLocalization.parameterMap R S ι p a := rfl

/-- The original residue square extends to the actual generic tensor source. -/
theorem tensorTarget_residue_square (e : K →ₐ[ResidueField R] ResidueField S)
    (hχ : ∀ b, e (g b) = residue S (χ b)) (x : B ⊗[R] R₁) :
    targetResidueEmbedding R S K ι p e (tensorPoint R K ι p g x) =
      residue S₁ (tensorTarget R S ι p χ x) := by
  induction x using TensorProduct.inductionOn with
  | tmul b a =>
      rw [tensorPoint_tmul, map_mul,
        ParameterLocalization.genericCentreResidueEmbedding_coefficient,
        tensorTarget_tmul, map_mul]
      rw [show e.toRingHom (g b) = residue S (χ b) from hχ b,
        ResidueField.algebraMap_residue]
      congr 1
      exact targetResidueEmbedding_parameterPoint R S K ι p e a
  | add x y hx hy => simp only [map_add, hx, hy]

end GenericParameterCentre
