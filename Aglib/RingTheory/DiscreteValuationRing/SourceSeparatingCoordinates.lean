/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.RingTheory.DiscreteValuationRing.SourceCentreResidueField
public import Aglib.FieldTheory.SeparablyGenerated.FiniteBasis
public import Aglib.RingTheory.Kaehler.GenericSeparatingBasis

/-! # Separating coordinates for the actual source centre

All field data come from the actual residue field of the source localized at
its centre. The generic coordinates use precisely the original algebra
presentation's generator family, merely reindexed as retained and parameter
rows of one square generic matrix.
-/

@[expose] public noncomputable section

open IsLocalRing

namespace ParameterLocalization.SourceCentre

variable {R S B : Type*}
  [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
  [CommRing S] [IsDomain S] [IsDiscreteValuationRing S]
  [CommRing B] [IsDomain B] [Algebra R B] [Algebra R S]
  [IsLocalHom (algebraMap R S)]

/-- The original fraction-field degree bounds every actual finite independent
centre family. The fraction action is precisely the native action supplied
from the same-uniformizer point, not an independently postulated action. -/
theorem residue_fin_independent_le_source_trdeg
    (p : R) [Fact (Irreducible p)] (χ : B →ₐ[R] S)
    (hpS : Irreducible (algebraMap R S p)) (r : ℕ)
    (hr : letI : FaithfulSMul R B := faithfulSMul_source_of_map_irreducible p χ hpS
      letI : Algebra (FractionRing R) (FractionRing B) :=
        FractionRing.liftAlgebra R (FractionRing B)
      Algebra.trdeg (FractionRing R) (FractionRing B) = (r : Cardinal))
    {d : ℕ} (t : Fin d → ResidueField (LocalSource χ))
    (ht : AlgebraicIndependent (ResidueField R) t) : d ≤ r := by
  let : FaithfulSMul R B := faithfulSMul_source_of_map_irreducible p χ hpS
  let : Algebra (FractionRing R) (FractionRing B) :=
    FractionRing.liftAlgebra R (FractionRing B)
  have h := residue_independent_trdeg_bound p χ hpS t ht
  simpa [hr] using h

/-- The actual source-centre field has a finite separating basis bounded both
by the original fraction-field degree and by the number of original algebra
generators. Its transcendence degree is retained as an equality. -/
theorem exists_residue_fin_separatingBasis
    (p : R) [Fact (Irreducible p)] (χ : B →ₐ[R] S)
    (hpS : Irreducible (algebraMap R S p)) (r : ℕ)
    (hr : letI : FaithfulSMul R B := faithfulSMul_source_of_map_irreducible p χ hpS
      letI : Algebra (FractionRing R) (FractionRing B) :=
        FractionRing.liftAlgebra R (FractionRing B)
      Algebra.trdeg (FractionRing R) (FractionRing B) = (r : Cardinal))
    [Algebra.IsTranscendentalSeparable (ResidueField R) (ResidueField S)]
    {n : Type*} [Fintype n] (P : Algebra.Generators R B n) :
    ∃ (d : ℕ) (t : Fin d → ResidueField (LocalSource χ)),
      IsTranscendenceBasis (ResidueField R) t ∧
        Algebra.trdeg (ResidueField R) (ResidueField (LocalSource χ)) = (d : Cardinal) ∧
        d ≤ r ∧ d ≤ Fintype.card n ∧
        Module.Finite (IntermediateField.adjoin (ResidueField R) (Set.range t))
          (ResidueField (LocalSource χ)) ∧
        Algebra.IsSeparable (IntermediateField.adjoin (ResidueField R) (Set.range t))
          (ResidueField (LocalSource χ)) := by
  let : Algebra.FiniteType R B := P.finiteType
  let : Algebra.EssFiniteType (ResidueField R) (ResidueField (LocalSource χ)) :=
    residue_essFiniteType χ
  let : Algebra.IsSeparablyGenerated (ResidueField R) (ResidueField (LocalSource χ)) :=
    residue_isSeparablyGenerated χ
  obtain ⟨d, t, ht, hdegree, hfinite, hsep⟩ :=
    Algebra.IsSeparablyGenerated.exists_fin_isTranscendenceBasis_and_finite
      (ResidueField R) (ResidueField (LocalSource χ))
  refine ⟨d, t, ht, hdegree,
    residue_fin_independent_le_source_trdeg p χ hpS r hr t ht.1, ?_, hfinite, hsep⟩
  exact ht.fin_le_card_of_adjoin_eq_top
    (fun i => algebraMap B (ResidueField (LocalSource χ)) (P.val i))
    (residue_generators_adjoin_eq_top χ P)

attribute [local instance] MvPolynomial.algebraMvPolynomial GenericParameterField.fractionAlgebra

omit [IsDomain B] in
/-- A genuine separating basis of the actual centre supplies generic
coordinates from the same original presentation, for any chosen parameter
rows. This is the direct consumer of the existing generic-basis theorem. -/
theorem generic_residue_coordinates_of_separatingBasis
    (χ : B →ₐ[R] S) {n : Type*} [Fintype n] (P : Algebra.Generators R B n)
    {d : ℕ} (t : Fin d → ResidueField (LocalSource χ))
    (ht : IsTranscendenceBasis (ResidueField R) t)
    [Algebra.IsSeparable (IntermediateField.adjoin (ResidueField R) (Set.range t))
      (ResidueField (LocalSource χ))] (e : Fin d ↪ n) :
    let k := ResidueField R
    let K := ResidueField (LocalSource χ)
    let F := FractionRing (MvPolynomial (n × n) k)
    let L := FractionRing (MvPolynomial (n × n) K)
    let x := fun i => algebraMap B K (P.val i)
    let y := fun j => GenericParameterField.coordinate k K n x (e j)
    IsTranscendenceBasis F y ∧
      Module.Finite (IntermediateField.adjoin F (Set.range y)) L ∧
      Algebra.IsSeparable (IntermediateField.adjoin F (Set.range y)) L := by
  exact GenericParameterField.generic_coordinates_isTranscendenceBasis_and_finite
    (ResidueField R) (ResidueField (LocalSource χ)) n t ht
    (fun i => algebraMap B (ResidueField (LocalSource χ)) (P.val i))
    (residue_generators_adjoin_eq_top χ P) e

/-- The complete actual-centre witness, with a literal sum index and `Sum.inr`
parameter rows. The retained index is `Fin (card n - d)`. The equivalence
only reindexes the original generators; it neither extends nor replaces them.
All generic coordinates use the same full matrix of indeterminates. -/
theorem exists_sum_generic_residue_coordinates
    (p : R) [Fact (Irreducible p)] (χ : B →ₐ[R] S)
    (hpS : Irreducible (algebraMap R S p)) (r : ℕ)
    (hr : letI : FaithfulSMul R B := faithfulSMul_source_of_map_irreducible p χ hpS
      letI : Algebra (FractionRing R) (FractionRing B) :=
        FractionRing.liftAlgebra R (FractionRing B)
      Algebra.trdeg (FractionRing R) (FractionRing B) = (r : Cardinal))
    [Algebra.IsTranscendentalSeparable (ResidueField R) (ResidueField S)]
    {n : Type*} [Fintype n] (P : Algebra.Generators R B n) :
    ∃ (d : ℕ) (t : Fin d → ResidueField (LocalSource χ))
      (ε : Fin (Fintype.card n - d) ⊕ Fin d ≃ n),
      IsTranscendenceBasis (ResidueField R) t ∧
        Algebra.trdeg (ResidueField R) (ResidueField (LocalSource χ)) = (d : Cardinal) ∧
        d ≤ r ∧ d ≤ Fintype.card n ∧
        Module.Finite (IntermediateField.adjoin (ResidueField R) (Set.range t))
          (ResidueField (LocalSource χ)) ∧
        Algebra.IsSeparable (IntermediateField.adjoin (ResidueField R) (Set.range t))
          (ResidueField (LocalSource χ)) ∧
        let N := Fin (Fintype.card n - d) ⊕ Fin d
        let k := ResidueField R
        let K := ResidueField (LocalSource χ)
        let F := FractionRing (MvPolynomial (N × N) k)
        let L := FractionRing (MvPolynomial (N × N) K)
        let x := fun i : N => algebraMap B K (P.val (ε i))
        let y := fun j : Fin d => GenericParameterField.coordinate k K N x (Sum.inr j)
        IsTranscendenceBasis F y ∧
          Module.Finite (IntermediateField.adjoin F (Set.range y)) L ∧
          Algebra.IsSeparable (IntermediateField.adjoin F (Set.range y)) L := by
  classical
  obtain ⟨d, t, ht, hdegree, hdr, hdn, hfinite, hsep⟩ :=
    exists_residue_fin_separatingBasis p χ hpS r hr P
  let ε : Fin (Fintype.card n - d) ⊕ Fin d ≃ n :=
    Fintype.equivOfCardEq (by simp only [Fintype.card_sum, Fintype.card_fin,
      Nat.sub_add_cancel hdn])
  let := hsep
  refine ⟨d, t, ε, ht, hdegree, hdr, hdn, hfinite, hsep, ?_⟩
  exact generic_residue_coordinates_of_separatingBasis χ (P.reindex ε) t ht
    ⟨Sum.inr, Sum.inr_injective⟩

end ParameterLocalization.SourceCentre
