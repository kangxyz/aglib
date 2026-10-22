/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.RingTheory.DiscreteValuationRing.ParameterProjectedFixedStep
public import Aglib.RingTheory.DiscreteValuationRing.ParameterProjectedFittingTransport
public import Aglib.RingTheory.Extension.Generators.RetainedFittingEquality
public import Aglib.RingTheory.Kaehler.PolynomialParametersFitting

/-! # Fixed original centre descent through the actual parameter projection

The old equality is proved from the actual SAME-matrix selected relations. The new
side uses only the polynomial-parameter Fitting inclusion. The modification and
its original point remain fixed; no replacement centre family is chosen.
-/

@[expose] public noncomputable section

open IsLocalRing MvPolynomial Algebra.NeronModification

namespace ParameterLocalization.ProjectedCentre

variable {R S A K ι β ν : Type*} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
  [CommRing S] [IsDomain S] [IsDiscreteValuationRing S] [Algebra R S]
  [IsLocalHom (algebraMap R S)] [CommRing A] [Algebra R A]
  [Field K] [Algebra (ResidueField R) K]
  [Fintype ι] [Fintype β] [DecidableEq ι] [DecidableEq β] [Finite ν]
  (p : R) [Fact (Irreducible p)] (D : Subalgebra (ResidueField R) K)
  (f : A →+* D)
  (hf : f.comp (algebraMap R A) = (algebraMap (ResidueField R) D).comp (residue R))
  (b : ι → A)
  (hy : AlgebraicIndependent (ResidueField R) (fun i => (f (b i) : K)))
  (χ : A →ₐ[R] S) (e : K →ₐ[ResidueField R] ResidueField S)
  (hχ : ∀ a, e (f a) = residue S (χ a))
  (hpS : Irreducible (algebraMap R S p))

local notation "P₀" => MvPolynomial ι R
local notation "R₂" => Ring R ι p
local notation "A'" => Localization (sourceDenominators p b)
local notation "k₂" => ResidueField R₂

omit [Fintype ι] in
local instance [Finite ι] : IsDiscreteValuationRing R₂ := isDiscreteValuationRing R ι p
/-- The fixed parameter DVR acts on the same localized source through the
original parameter scalar map `scalarMap p b`. -/
local instance descentSourceAlgebra : Algebra R₂ A' := (scalarMap p b).toAlgebra

variable [IsFractionRing D K]

include hf e hχ hpS in
/-- Any fixed lift through the SAME original centre modification strictly improves
the original Fitting index. All projection/minor data in this intermediate theorem
are literal data supplied by generic-coordinate normalization in the general step. -/
theorem fixed_lift_fittingIdeal_lt_of_retained_minor :
    letI : Algebra R₂ S :=
      (projectedTargetScalarMap p f b hy χ e hχ).toRingHom.toAlgebra
    letI : IsLocalHom (algebraMap R₂ S) :=
      projectedTargetScalarMap_isLocalHom p D f b hy χ e hχ hpS
    letI : Algebra k₂ K :=
      ((SeparatingParameterLocalization.fractionMap D (fun i => f (b i)) hy).comp
        (residueFieldAlgEquiv R ι p).toRingHom).toAlgebra
    ∀ [Module.Finite k₂ K] [Algebra.IsSeparable k₂ K]
      (P : Algebra.Generators R A (β ⊕ ι))
      (U : Matrix (β ⊕ ι) (β ⊕ ι) R) (hU : IsUnit U.det)
      (_hb : ∀ i, (P.linearChange U hU).val (.inr i) = b i)
      (_hs : Function.Surjective f) (g : ν → A)
      (_hgen : Ideal.span (insert (algebraMap R A p) (Set.range g)) = RingHom.ker f)
      (k : ℕ) (_hk : Nat.card ι ≤ k)
      (rels : Fin (Nat.card β - (k - Nat.card ι)) → P.ker)
      (cols : Fin (Nat.card β - (k - Nat.card ι)) ↪ β)
      (δ h : S) (_hh : IsUnit h)
      (_hδ : Ideal.span {δ} =
        (Module.fittingIdeal A (KaehlerDifferential R A) k).map χ.toRingHom)
      (_hnorm : ((Matrix.of (fun j i => χ (aeval P.val
          (pderiv i (rels j : MvPolynomial (β ⊕ ι) R)))) *
        ((algebraMap R S).mapMatrix U).adjugate).submatrix _root_.id
          (fun i => Sum.inl (cols i))).det = δ * h)
      (_hne : (Module.fittingIdeal A (KaehlerDifferential R A) k).map χ.toRingHom ≠ ⊥)
      (_hproper : (Module.fittingIdeal A (KaehlerDifferential R A) k).map χ.toRingHom ≠ ⊤)
      (χM : Modification (algebraMap R A p) g →+* S)
      (_hχM : χM.comp (of (algebraMap R A p) g) = χ.toRingHom),
    (Module.fittingIdeal A (KaehlerDifferential R A) k).map χ.toRingHom <
      (Module.fittingIdeal _ (KaehlerDifferential R
        (Modification (algebraMap R A p) g)) k).map χM := by
  let : Algebra R₂ S :=
    (projectedTargetScalarMap p f b hy χ e hχ).toRingHom.toAlgebra
  let : IsLocalHom (algebraMap R₂ S) :=
    projectedTargetScalarMap_isLocalHom p D f b hy χ e hχ hpS
  let : Algebra k₂ K :=
    ((SeparatingParameterLocalization.fractionMap D (fun i => f (b i)) hy).comp
      (residueFieldAlgEquiv R ι p).toRingHom).toAlgebra
  intro _ _ P U hU hb hs g hgen k hk rels cols δ h hh hδ hnorm hne hproper χM hχM
  let : Algebra P₀ A := (aeval b).toRingHom.toAlgebra
  let : IsScalarTower R P₀ A :=
    IsScalarTower.of_algebraMap_eq fun r => ((aeval (R := R) b).commutes r).symm
  let : Algebra.FiniteType R A := P.finiteType
  have ha (i) : algebraMap P₀ A (X i) = (P.linearChange U hU).val (.inr i) := by
    change aeval b (X i) = _
    rw [aeval_X, hb]
  have hold := P.map_fittingIdeal_absorb_linearChange_eq U hU ha k hk χ
    rels cols δ h hh hδ hnorm
  have hprojected :
      (Module.fittingIdeal A' (KaehlerDifferential R₂ A') (k - Nat.card ι)).map
        (projectedTargetOverParameters p D f hf b hy χ e hχ).toRingHom =
      (Module.fittingIdeal A (KaehlerDifferential R A) k).map χ.toRingHom :=
    (map_fittingIdeal_projectedTargetMap p D f hf b hy χ e hχ (k - Nat.card ι)).trans hold
  let C : A' → Prop := fun a =>
    ∃ χN : Modification a (fun j => algebraMap A A' (g j)) →ₐ[R₂] S,
      (∀ z, χN (of a (fun j => algebraMap A A' (g j)) z) =
        projectedTargetOverParameters p D f hf b hy χ e hχ z) ∧
      (Module.fittingIdeal A' (KaehlerDifferential R₂ A') (k - Nat.card ι)).map
        (projectedTargetOverParameters p D f hf b hy χ e hχ).toRingHom <
      (Module.fittingIdeal _ (KaehlerDifferential R₂
        (Modification a (fun j => algebraMap A A' (g j)))) (k - Nat.card ι)).map
          χN.toRingHom
  have hstep : C (algebraMap R A' p) :=
    exists_fixed_projected_strict_step p D f hf b hy χ e hχ hpS
      (P.linearChange U hU) hb hs g hgen (k - Nat.card ι)
      (by rw [hprojected]; exact hne) (by rw [hprojected]; exact hproper)
  have hpA : algebraMap R A' p = algebraMap A A' (algebraMap R A p) :=
    IsScalarTower.algebraMap_apply R A A' p
  obtain ⟨χN, hχN, hstrict⟩ := Eq.mp (congrArg C hpA) hstep
  have hnew := map_fittingIdeal_projectedModification p D f hf b hy χ e hχ g
    χM χN.toRingHom hχM (RingHom.ext hχN) hpS (k - Nat.card ι)
  rw [hprojected, hnew] at hstrict
  exact lt_of_lt_of_le hstrict (Ideal.map_mono
    (KaehlerDifferential.fittingIdeal_polynomialParameters_le
      (R := R) (B := Modification (algebraMap R A p) g) (α := ι) k hk))

end ParameterLocalization.ProjectedCentre
