/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.RingTheory.DiscreteValuationRing.ParameterResidue
public import Aglib.RingTheory.Localization.SeparatingParameters
public import Aglib.RingTheory.Localization.SeparatingParameterField

/-! # Finite separability for the actual projected residue action

The action agrees with the one used by `ProjectedCentre.projectedResidueAlgEmbedding`:
actual fraction evaluation following the canonical parameter residue equivalence.
-/

@[expose] public noncomputable section

open IsLocalRing

namespace ParameterLocalization

attribute [local instance] algebraMap_isLocalHom

variable {R F K ι : Type*} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
  [Field F] [Field K] [Algebra (ResidueField R) F] [Algebra F K]
  [Algebra (ResidueField R) K] [IsScalarTower (ResidueField R) F K]
variable (p : R) [Fact (Irreducible p)]
  (e : ResidueField R ≃+* F) (he : algebraMap (ResidueField R) F = e.toRingHom)
  (D : Subalgebra (ResidueField R) K) (y : ι → D)
  (hy : AlgebraicIndependent F (fun i => (y i : K)))

/-- The two canonical fraction evaluations are literally the same lift, not merely conjugate. -/
theorem projectedFractionMap_eq :
    SeparatingParameterLocalization.fractionMap D y
      (SeparatingParameterField.independent e he (fun i => (y i : K)) hy) =
    SeparatingParameterField.fractionPoint e he (fun i => (y i : K)) hy := rfl

/-- Finite separability for the exact second parameter residue action. -/
theorem projectedResidue_finite_and_isSeparable
    [Module.Finite (IntermediateField.adjoin F (Set.range fun i => (y i : K))) K]
    [Algebra.IsSeparable (IntermediateField.adjoin F (Set.range fun i => (y i : K))) K] :
    letI : Algebra (ResidueField (Ring R ι p)) K :=
      ((SeparatingParameterLocalization.fractionMap D y
        (SeparatingParameterField.independent e he (fun i => (y i : K)) hy)).comp
        (residueFieldAlgEquiv R ι p).toRingHom).toAlgebra
    Module.Finite (ResidueField (Ring R ι p)) K ∧
      Algebra.IsSeparable (ResidueField (Ring R ι p)) K := by
  let G := FractionRing (MvPolynomial ι (ResidueField R))
  let ψ := SeparatingParameterLocalization.fractionMap D y
    (SeparatingParameterField.independent e he (fun i => (y i : K)) hy)
  let φ := (residueFieldAlgEquiv R ι p).toRingEquiv
  let : Algebra G K := ψ.toAlgebra
  have hfinite : Module.Finite G K :=
    (SeparatingParameterField.finite_and_isSeparable e he (fun i => (y i : K)) hy).1
  have hsep : Algebra.IsSeparable G K :=
    (SeparatingParameterField.finite_and_isSeparable e he (fun i => (y i : K)) hy).2
  let := hfinite
  let := hsep
  let : Algebra (ResidueField (Ring R ι p)) G := φ.toRingHom.toAlgebra
  let : Algebra (ResidueField (Ring R ι p)) K := (ψ.comp φ.toRingHom).toAlgebra
  let : IsScalarTower (ResidueField (Ring R ι p)) G K :=
    IsScalarTower.of_algebraMap_eq' rfl
  let : Module.Finite (ResidueField (Ring R ι p)) G :=
    RingHom.Finite.of_surjective φ.toRingHom φ.surjective
  refine ⟨Module.Finite.trans G K, ?_⟩
  exact Algebra.IsSeparable.of_equiv_equiv φ.symm (RingEquiv.refl K) (by
    ext a
    change ψ (φ (φ.symm a)) = ψ a
    rw [φ.apply_symm_apply])

end ParameterLocalization
