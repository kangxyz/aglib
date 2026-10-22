/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.RingTheory.DiscreteValuationRing.SourceSeparatingCoordinates
public import Aglib.RingTheory.Kaehler.GenericFittingNonzero
public import Aglib.LinearAlgebra.Matrix.SelectedMinorRows
public import Aglib.RingTheory.DiscreteValuationRing.GenericTensorCentre
public import Aglib.RingTheory.DiscreteValuationRing.GenericTensorRelations
public import Aglib.RingTheory.DiscreteValuationRing.GenericProjectedImage
public import Aglib.RingTheory.DiscreteValuationRing.ParameterProjectedFiniteSeparable
public import Aglib.RingTheory.DiscreteValuationRing.ParameterProjectedStrictDescent
public import Aglib.RingTheory.DiscreteValuationRing.GenericTargetFittingTransport
public import Aglib.RingTheory.DiscreteValuationRing.GenericTargetModificationLift

/-!
# A strict Néron step at an arbitrary centre

Both separability assumptions refer to actual maps: the generic fraction map
and the residual map of the fixed DVR pair. The centre field, separating
coordinates, retained minor, and projected finite-separable action are derived.
The conclusion applies to any fixed actual lift of the original modification.
-/

@[expose] public noncomputable section

open IsLocalRing MvPolynomial
open scoped TensorProduct
open ParameterLocalization ParameterLocalization.SourceCentre GenericParameterCentre

namespace Algebra.NeronModification

attribute [local instance] MvPolynomial.algebraMvPolynomial
  GenericParameterField.fractionAlgebra Algebra.TensorProduct.rightAlgebra
  ParameterLocalization.algebraMap_isLocalHom

variable {R S B : Type*} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
  [CommRing S] [IsDomain S] [IsDiscreteValuationRing S] [Algebra R S]
  [IsLocalHom (algebraMap R S)] [CommRing B] [IsDomain B] [Algebra R B]

/-- Strict improvement for the fixed original centre modification and any fixed
lift. No projected separability, selected minor, or Fitting equality is assumed. -/
theorem fittingIdeal_lt_of_generalCentre
    (p : R) [Fact (Irreducible p)] (χ : B →ₐ[R] S)
    (hinj : Function.Injective χ) (hpS : Irreducible (algebraMap R S p))
    [Algebra.IsTranscendentalSeparable (ResidueField R) (ResidueField S)]
    (hgeneric : letI : FaithfulSMul R B := faithfulSMul_source_of_map_irreducible p χ hpS
      letI : Algebra (FractionRing R) (FractionRing B) :=
        FractionRing.liftAlgebra R (FractionRing B)
      Algebra.IsSeparablyGenerated (FractionRing R) (FractionRing B))
    (r : ℕ)
    (hr : letI : FaithfulSMul R B := faithfulSMul_source_of_map_irreducible p χ hpS
      letI : Algebra (FractionRing R) (FractionRing B) :=
        FractionRing.liftAlgebra R (FractionRing B)
      Algebra.trdeg (FractionRing R) (FractionRing B) = (r : Cardinal))
    {n ν : Type*} [Finite n] [Finite ν] (P₀ : Algebra.Generators R B n)
    (g : ν → B)
    (hgen : Ideal.span (insert (algebraMap R B p) (Set.range g)) = centre χ)
    (hproper : (Module.fittingIdeal B (KaehlerDifferential R B) r).map χ.toRingHom ≠ ⊤)
    (χM : Modification (algebraMap R B p) g →+* S)
    (hχM : χM.comp (of (algebraMap R B p) g) = χ.toRingHom) :
    (Module.fittingIdeal B (KaehlerDifferential R B) r).map χ.toRingHom <
      (Module.fittingIdeal _ (KaehlerDifferential R
        (Modification (algebraMap R B p) g)) r).map χM := by
  classical
  let : Fintype n := Fintype.ofFinite n
  let : Fact (Irreducible (algebraMap R S p)) := ⟨hpS⟩
  let : Algebra.FiniteType R B := P₀.finiteType
  let : FaithfulSMul R B := faithfulSMul_source_of_map_irreducible p χ hpS
  let : Algebra (FractionRing R) (FractionRing B) :=
    FractionRing.liftAlgebra R (FractionRing B)
  let : Algebra.IsSeparablyGenerated (FractionRing R) (FractionRing B) := hgeneric
  have hne := KaehlerDifferential.map_fittingIdeal_ne_bot_of_generic_isSeparablyGenerated
    (F := FractionRing R) (L := FractionRing B) χ hinj r hr
  obtain ⟨d, _t, ε, _ht, _hdegree, hdr, hdn, _hfinite, _hsep, hcoordinates⟩ :=
    exists_sum_generic_residue_coordinates p χ hpS r hr P₀
  let N := Fin (Fintype.card n - d) ⊕ Fin d
  let P : Algebra.Generators R B N := P₀.reindex ε
  let K := ResidueField (LocalSource χ)
  let R₁ := ParameterLocalization.Ring R (N × N) p
  let S₁ := ParameterLocalization.Ring S (N × N) (algebraMap R S p)
  let A := B ⊗[R] R₁
  let F := FractionRing (MvPolynomial (N × N) (ResidueField R))
  let L := FractionRing (MvPolynomial (N × N) K)
  let σ : S →+* S₁ := algebraMap S S₁
  let p₁ : R₁ := algebraMap R R₁ p
  let : IsDiscreteValuationRing R₁ := isDiscreteValuationRing R (N × N) p
  let : IsDiscreteValuationRing S₁ := isDiscreteValuationRing S (N × N) (algebraMap R S p)
  let : Fact (Irreducible p₁) := ⟨uniformizer_irreducible R (N × N) p⟩
  let : Algebra R₁ S₁ := (parameterMap R S (N × N) p).toRingHom.toAlgebra
  let : IsLocalHom (algebraMap R₁ S₁) := parameterMap_isLocalHom R S (N × N) p
  let : Algebra (ResidueField R₁) F := (residueFieldAlgEquiv R (N × N) p).toRingHom.toAlgebra
  let : Algebra (ResidueField R₁) L :=
    ((algebraMap F L).comp (residueFieldAlgEquiv R (N × N) p).toRingHom).toAlgebra
  let : IsScalarTower (ResidueField R₁) F L := IsScalarTower.of_algebraMap_eq' rfl
  have hcoeff₀ (a : R) : algebraMap B K (algebraMap R B a) =
      algebraMap (ResidueField R) K (residue R a) := by
    rw [ResidueField.algebraMap_residue]
    exact (IsScalarTower.algebraMap_apply R B K a).symm
  let : Algebra R K := ((algebraMap (ResidueField R) K).comp (residue R)).toAlgebra
  let g₀ : B →ₐ[R] K :=
    { algebraMap B K with commutes' := hcoeff₀ }
  let e₀ := residueEmbedding χ
  have hsquare₀ (a : B) : e₀ (g₀ a) = residue S (χ a) :=
    residueEmbedding_algebraMap χ a
  have hker₀ : RingHom.ker g₀.toRingHom = centre χ := by
    ext a
    change g₀ a = 0 ↔ χ a ∈ maximalIdeal S
    rw [← residue_eq_zero_iff]
    exact ⟨fun h => by rw [← hsquare₀, h, map_zero],
      fun h => e₀.injective (by
        change e₀ (g₀ a) = e₀ 0
        rw [hsquare₀, h, map_zero])⟩
  let D := projectedImage R K (N × N) p g₀
  let f : A →+* D := projectedSourceMap R K (N × N) p g₀
  have hf := projectedSourceMap_comp_algebraMap R K (N × N) p g₀
  have hs := projectedSourceMap_surjective R K (N × N) p g₀
  let : IsFractionRing D L := isFractionRing_projectedImage R K (N × N) p g₀ P.val
    (residue_generators_adjoin_eq_top χ P)
  let P₁ : Algebra.Generators R₁ A N := tensorGenerators R p P
  let : Algebra.FiniteType R₁ A := P₁.finiteType
  let U := genericMatrix R N p
  have hU : IsUnit U.det := isUnit_det_genericMatrix R N p
  let b : Fin d → A := fun j => (P₁.linearChange U hU).val (.inr j)
  let y : Fin d → D := fun j => f (b j)
  have hyval (j : Fin d) : (y j : L) =
      GenericParameterField.coordinate (ResidueField R) K N
        (fun i => g₀ (P.val i)) (.inr j) := by
    change tensorPoint R K (N × N) p g₀ ((genericGenerators R p P).val (.inr j)) = _
    rw [genericGenerators_val, tensorPoint_liftedCoordinate]
  have hyfun : (fun j => (y j : L)) = fun j =>
      GenericParameterField.coordinate (ResidueField R) K N
        (fun i => g₀ (P.val i)) (.inr j) := funext hyval
  have hcoordinates' : IsTranscendenceBasis F (fun j => (y j : L)) ∧
      Module.Finite (IntermediateField.adjoin F (Set.range fun j => (y j : L))) L ∧
      Algebra.IsSeparable (IntermediateField.adjoin F (Set.range fun j => (y j : L))) L := by
    rw [hyfun]
    exact hcoordinates
  let := hcoordinates'.2.1
  let := hcoordinates'.2.2
  have hy : AlgebraicIndependent (ResidueField R₁) (fun j => (y j : L)) :=
    SeparatingParameterField.independent (residueFieldAlgEquiv R (N × N) p).toRingEquiv
      rfl (fun j => (y j : L)) hcoordinates'.1.1
  have hfinite₂ := projectedResidue_finite_and_isSeparable p₁
    (residueFieldAlgEquiv R (N × N) p).toRingEquiv rfl D y hcoordinates'.1.1
  let χ₁ : A →ₐ[R₁] S₁ := tensorTargetOverParameters R S (N × N) p χ
  let e₁ : L →ₐ[ResidueField R₁] ResidueField S₁ :=
    targetResidueAlgEmbedding R S K (N × N) p e₀
  have hχ₁ (a : A) : e₁ (f a : L) = residue S₁ (χ₁ a) :=
    tensorTarget_residue_square R S K (N × N) p g₀ χ e₀ hsquare₀ a
  have hp₁S : Irreducible (algebraMap R₁ S₁ p₁) := by
    change Irreducible (parameterMap R S (N × N) p (algebraMap R R₁ p))
    rw [parameterMap_uniformizer]
    exact uniformizer_irreducible S (N × N) (algebraMap R S p)
  let g₁ : ν → A := fun j => algebraMap B A (g j)
  have hpA : algebraMap R₁ A p₁ = algebraMap B A (algebraMap R B p) := by
    exact (IsScalarTower.algebraMap_apply R R₁ A p).symm.trans
      (IsScalarTower.algebraMap_apply R B A p)
  have hgen₁ : Ideal.span (insert (algebraMap R₁ A p₁) (Set.range g₁)) = RingHom.ker f := by
    rw [ker_projectedSourceMap, ker_tensorPoint, hker₀, ← hgen, Ideal.map_span]
    simp only [Set.image_insert_eq, ← Set.range_comp, Function.comp_def, hpA]
    rfl
  have hσp : Irreducible (σ (algebraMap R S p)) :=
    uniformizer_irreducible S (N × N) (algebraMap R S p)
  have hσinj := IsDiscreteValuationRing.injective_of_map_irreducible σ hpS hσp
  have hord (I : Ideal S) :=
    IsDiscreteValuationRing.idealOrderIsoENat_map_of_map_irreducible σ hpS hσp I
  let I := (Module.fittingIdeal B (KaehlerDifferential R B) r).map χ.toRingHom
  have hI₁ : (Module.fittingIdeal A (KaehlerDifferential R₁ A) r).map χ₁.toRingHom =
      I.map σ := map_fittingIdeal_tensorTarget p χ r
  have hne₁ : (Module.fittingIdeal A (KaehlerDifferential R₁ A) r).map χ₁.toRingHom ≠ ⊥ := by
    rw [hI₁, ne_eq, Ideal.map_eq_bot_iff_of_injective (f := σ) hσinj]
    exact hne
  have hproper₁ : (Module.fittingIdeal A (KaehlerDifferential R₁ A) r).map χ₁.toRingHom ≠ ⊤ := by
    rw [hI₁]
    intro h
    apply hproper
    apply (IsDiscreteValuationRing.idealOrderIsoENat S).injective
    rw [← hord I, ← hord ⊤, Ideal.map_top, h]
  let c := Nat.card (Fin (Fintype.card n - d)) - (r - Nat.card (Fin d))
  have hc : Fintype.card N - r = c := by
    dsimp [N, c]
    simp only [Nat.card_fin]
    rw [Fintype.card_sum, Fintype.card_fin, Fintype.card_fin, Nat.sub_add_cancel hdn]
    exact (Nat.sub_sub_sub_cancel_right hdr).symm
  let Q : Algebra.Presentation R B N P.ker :=
    { P with relation := Subtype.val
             span_range_relation_eq_ker := by rw [Subtype.range_coe]; exact Ideal.span_eq _ }
  let W : Matrix N P.ker B := fun i f => aeval P.val (pderiv i f.val)
  let J : Matrix P.ker N S := fun f i => χ (aeval P.val (pderiv i f.val))
  have hminorDet (rows : Fin c → P.ker) (cols : Fin c → N) :
      (J.submatrix rows cols).det = χ.toRingHom (W.submatrix cols rows).det := by
    calc
      (J.submatrix rows cols).det =
          ((W.submatrix cols rows).map χ.toRingHom).det := Matrix.det_transpose _
      _ = χ.toRingHom (W.submatrix cols rows).det := (χ.toRingHom.map_det _).symm
  have hJmap : J.minorIdeal c = (W.minorIdeal c).map χ.toRingHom := by
    rw [Matrix.minorIdeal, Matrix.minorIdeal, Ideal.map_span]
    congr 1
    ext x
    constructor
    · rintro ⟨rows, cols, rfl⟩
      exact ⟨(W.submatrix cols rows).det, ⟨cols, rows, rfl⟩, (hminorDet rows cols).symm⟩
    · rintro ⟨x, ⟨cols, rows, rfl⟩, rfl⟩
      exact ⟨rows, cols, hminorDet rows cols⟩
  have hW : (Matrix.of fun (i : N) (j : P.ker) =>
      aeval Q.val (pderiv i (Q.relation j))) = W := by
    ext i j
    rfl
  have hQ : Module.fittingIdeal B (KaehlerDifferential R B) r = W.minorIdeal c := by
    rw [Q.fittingIdeal_kaehler_eq_minorIdeal, hW, Nat.card_eq_fintype_card, hc]
  have hJ : J.minorIdeal c = I :=
    hJmap.trans (congrArg (fun I : Ideal B => I.map χ.toRingHom) hQ).symm
  obtain ⟨rels, cols, δ, hδ, hδdet, hrows, hspan⟩ :=
    J.exists_selected_rows_minorIdeal_eq c (by rw [hJ]; exact hne)
  let retained : Fin c ↪ Fin (Fintype.card n - d)  :=
    Fin.castLEEmb (by simp only [c, Nat.card_fin]; exact Nat.sub_le _ _)
  let retainedN : Fin c ↪ N := retained.trans ⟨Sum.inl, Sum.inl_injective⟩
  obtain ⟨u, hu, hnorm⟩ := exists_tensorRelation_retained_minor_unit R S p P χ rels δ hδ
    hrows cols hδdet retainedN
  have hspan₁ : Ideal.span {σ δ} =
      (Module.fittingIdeal A (KaehlerDifferential R₁ A) r).map χ₁.toRingHom := by
    rw [hI₁, ← hJ, ← hspan, Ideal.map_span, Set.image_singleton]
  obtain ⟨χN, hχN⟩ := exists_lift_tensorTargetOverParameters (ι := N × N) p χ g χM hχM
  let R₂ := ParameterLocalization.Ring R₁ (Fin d) p₁
  let : Algebra (ResidueField R₂) L :=
    ((SeparatingParameterLocalization.fractionMap D y hy).comp
      (residueFieldAlgEquiv R₁ (Fin d) p₁).toRingHom).toAlgebra
  let : Module.Finite (ResidueField R₂) L := hfinite₂.1
  let : Algebra.IsSeparable (ResidueField R₂) L := hfinite₂.2
  have hstrict := ParameterLocalization.ProjectedCentre.fixed_lift_fittingIdeal_lt_of_retained_minor
    p₁ D f hf b hy χ₁ e₁ hχ₁ hp₁S P₁ U hU (fun _ => rfl) hs g₁ hgen₁ r
    (by simpa only [Nat.card_fin] using hdr)
    (fun j => tensorRelation R p P (rels j)) retained (σ δ) u hu hspan₁ hnorm
    hne₁ hproper₁ χN hχN
  -- The comparison uses the original fixed lift, not a newly chosen original point.
  let T (a : A) : Prop := ∃ ψ : Modification a g₁ →+* S₁,
    ψ.comp (of a g₁) = χ₁.toRingHom ∧
      (Module.fittingIdeal A (KaehlerDifferential R₁ A) r).map χ₁.toRingHom <
        (Module.fittingIdeal _ (KaehlerDifferential R₁ (Modification a g₁)) r).map ψ
  have hT : T (algebraMap R₁ A p₁) := ⟨χN, hχN, hstrict⟩
  obtain ⟨χN', hχN', hstrict'⟩ : T (algebraMap B A (algebraMap R B p)) :=
    Eq.mp (congrArg T hpA) hT
  have hnew := map_fittingIdeal_tensorTarget_modification p χ g χM χN' hχM hχN' r
  rw [hI₁, hnew] at hstrict'
  have horders := (IsDiscreteValuationRing.idealOrderIsoENat S₁).strictMono hstrict'
  rw [hord, hord] at horders
  simpa only [OrderIso.symm_apply_apply] using
    (IsDiscreteValuationRing.idealOrderIsoENat S).symm.strictMono horders

end Algebra.NeronModification
