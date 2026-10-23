/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.RingTheory.AdicCompletion.FiniteModule
public import Aglib.RingTheory.LocalRing.SeparatedPrincipal
public import Mathlib.Algebra.Polynomial.Lifts
public import Mathlib.RingTheory.AdjoinRoot
public import Mathlib.RingTheory.AdicCompletion.Noetherian
public import Mathlib.RingTheory.Ideal.GoingUp
public import Mathlib.RingTheory.LocalRing.ResidueField.Basic

/-!
# Monogenic residue extensions of DVRs

A power basis of the specified residue-field extension determines a monic
lift of its minimal polynomial over the original DVR. The literal root
algebra is finite free and local, has the specified residue field, and is
a DVR with the original uniformizer. It is complete when the base is.
No separability or perfectness assumption is imposed.
-/

@[expose] public noncomputable section

open Polynomial IsLocalRing

namespace PowerBasis

section LocalRing

variable (B L : Type*) [CommRing B] [IsLocalRing B] [Field L]
  [Algebra (ResidueField B) L] (b : PowerBasis (ResidueField B) L)

/-- The original local ring acts on the residue extension through its
canonical residue map and the specified residue-field algebra structure. -/
local instance residueLiftAlgebra : Algebra B L :=
  ((algebraMap (ResidueField B) L).comp (residue B)).toAlgebra

local instance residueLiftTower : IsScalarTower B (ResidueField B) L :=
  IsScalarTower.of_algebraMap_eq' rfl

/-- A monic polynomial over the original local ring lifting the actual
minimal polynomial of the chosen residue generator. -/
theorem exists_monic_residueLiftPolynomial :
    ∃ f : B[X], f.map (residue B) = minpoly (ResidueField B) b.gen ∧ f.Monic := by
  obtain ⟨f, hf, _, hmonic⟩ := Polynomial.lifts_and_natDegree_eq_and_monic
    (Polynomial.mem_lifts_of_surjective (residue_surjective (R := B))
      (minpoly (ResidueField B) b.gen))
    (minpoly.monic b.isIntegral_gen)
  exact ⟨f, hf, hmonic⟩

/-- The chosen monic lift, retaining the original residue polynomial. -/
def residueLiftPolynomial : B[X] := (exists_monic_residueLiftPolynomial B L b).choose

theorem residueLiftPolynomial_map :
    (residueLiftPolynomial B L b).map (residue B) = minpoly (ResidueField B) b.gen :=
  (exists_monic_residueLiftPolynomial B L b).choose_spec.1

theorem residueLiftPolynomial_monic : (residueLiftPolynomial B L b).Monic :=
  (exists_monic_residueLiftPolynomial B L b).choose_spec.2

/-- The constructed root algebra, not a supplied local model. -/
abbrev ResidueLiftRing := AdjoinRoot (residueLiftPolynomial B L b)

local notation "D" => ResidueLiftRing B L b
local notation "f" => residueLiftPolynomial B L b

/-- The actual extended maximal ideal defining the closed fibre. -/
def residueLiftClosedIdeal : Ideal D := Ideal.map (AdjoinRoot.of f) (maximalIdeal B)

/-- The root presentation uses the original coefficient map. -/
theorem residueLiftClosedIdeal_eq_map_algebraMap :
    residueLiftClosedIdeal B L b = Ideal.map (algebraMap B D) (maximalIdeal B) := by
  rw [AdjoinRoot.algebraMap_eq]
  rfl

local notation "J" => residueLiftClosedIdeal B L b

/-- The root algebra is free over the original coefficient ring. -/
theorem residueLift_free : Module.Free B D := (residueLiftPolynomial_monic B L b).free_adjoinRoot

/-- The root algebra is finite over the original coefficient ring. -/
theorem residueLift_finite : Module.Finite B D :=
  (residueLiftPolynomial_monic B L b).finite_adjoinRoot

/-- The literal closed fibre is the specified field through the original
coefficient and quotient maps. -/
def residueLiftQuotientEquiv : (D ⧸ J) ≃ₐ[B] L :=
  (AdjoinRoot.quotEquivQuotMap f (maximalIdeal B)).trans
    ((AdjoinRoot.equiv' (Polynomial.map (residue B) f) b
      (by rw [← residueLiftPolynomial_map B L b]; simp only [AdjoinRoot.aeval_eq,
        AdjoinRoot.mk_self])
      (by rw [residueLiftPolynomial_map B L b]; exact minpoly.aeval _ _)).restrictScalars B)

/-- The specified point of the literal root algebra in the residue
extension field. -/
def residueLiftPoint : D →ₐ[B] L :=
  (residueLiftQuotientEquiv B L b).toAlgHom.comp (Ideal.Quotient.mkₐ B J)

theorem residueLiftPoint_algebraMap (a : B) :
    residueLiftPoint B L b (algebraMap B D a) =
      algebraMap (ResidueField B) L (residue B a) :=
  (residueLiftPoint B L b).commutes a

/-- The adjoined root maps to the specified residue generator. -/
@[simp]
theorem residueLiftPoint_root : residueLiftPoint B L b (AdjoinRoot.root f) = b.gen := by
  have hq : AdjoinRoot.quotEquivQuotMap f (maximalIdeal B)
      (Ideal.Quotient.mk J (AdjoinRoot.root f)) =
        AdjoinRoot.root (Polynomial.map (residue B) f) := by
    change AdjoinRoot.quotEquivQuotMap f (maximalIdeal B)
      (Ideal.Quotient.mk (Ideal.map (AdjoinRoot.of f) (maximalIdeal B))
        (AdjoinRoot.mk f X)) = _
    rw [AdjoinRoot.quotEquivQuotMap_apply_mk, Polynomial.map_X]
    rfl
  let e : AdjoinRoot (Polynomial.map (residue B) f) ≃ₐ[ResidueField B] L :=
    AdjoinRoot.equiv' (Polynomial.map (residue B) f) b
      (by rw [← residueLiftPolynomial_map B L b]; simp only [AdjoinRoot.aeval_eq,
        AdjoinRoot.mk_self])
      (by rw [residueLiftPolynomial_map B L b]; exact minpoly.aeval _ _)
  change e (AdjoinRoot.quotEquivQuotMap f (maximalIdeal B)
    (Ideal.Quotient.mk J (AdjoinRoot.root f))) = b.gen
  rw [hq]
  exact AdjoinRoot.liftAlgHom_root (Polynomial.map (residue B) f)
    (Algebra.ofId (ResidueField B) L) b.gen
    (by rw [residueLiftPolynomial_map B L b]; exact minpoly.aeval _ _)

theorem residueLiftPoint_surjective : Function.Surjective (residueLiftPoint B L b) :=
  (residueLiftQuotientEquiv B L b).surjective.comp (Ideal.Quotient.mk_surjective)

theorem ker_residueLiftPoint : RingHom.ker (residueLiftPoint B L b).toRingHom = J := by
  ext x
  change (residueLiftQuotientEquiv B L b) (Ideal.Quotient.mk J x) = 0 ↔ x ∈ J
  rw [map_eq_zero_iff _ (residueLiftQuotientEquiv B L b).injective,
    Ideal.Quotient.eq_zero_iff_mem]

private theorem residueLift_ideal_isMaximal : Ideal.IsMaximal J :=
  Ideal.Quotient.maximal_of_isField J
    ((residueLiftQuotientEquiv B L b).toRingEquiv.isField (Field.toIsField L))

/-- The constructed root algebra is local. Every maximal ideal contracts
to the original maximal ideal by integrality, and its closed fibre is a field. -/
theorem residueLift_isLocalRing : IsLocalRing D := by
  let : Module.Finite B D := residueLift_finite B L b
  have hJ := residueLift_ideal_isMaximal B L b
  apply IsLocalRing.of_unique_max_ideal
  refine ⟨J, hJ, ?_⟩
  intro n hn
  let : n.IsMaximal := hn
  have hnunder : n.under B = maximalIdeal B :=
    IsLocalRing.eq_maximalIdeal (Ideal.isMaximal_under_of_isIntegral_of_isMaximal n)
  have hJn : J ≤ n := by
    rw [residueLiftClosedIdeal_eq_map_algebraMap]
    exact Ideal.map_le_iff_le_comap.mpr hnunder.symm.le
  exact (hJ.eq_of_le hn.ne_top hJn).symm

/-- The actual maximal ideal is the extension of the original maximal ideal. -/
theorem residueLift_maximalIdeal :
    let _ : IsLocalRing D := residueLift_isLocalRing B L b
    maximalIdeal D = J := by
  let : IsLocalRing D := residueLift_isLocalRing B L b
  exact (IsLocalRing.eq_maximalIdeal (residueLift_ideal_isMaximal B L b)).symm

/-- The coefficient map into the constructed local root algebra is local. -/
theorem residueLift_algebraMap_isLocalHom : IsLocalHom (algebraMap B D) := by
  let : IsLocalRing D := residueLift_isLocalRing B L b
  apply ((IsLocalRing.local_hom_TFAE (algebraMap B D)).out 1 3).mpr
  rw [← residueLiftClosedIdeal_eq_map_algebraMap B L b]
  exact (residueLift_maximalIdeal B L b).symm.le

/-- The residue marking is induced by the actual quotient and the chosen
power basis. -/
def residueLiftResidueEquiv :
    let _ : IsLocalRing D := residueLift_isLocalRing B L b
    ResidueField D ≃+* L := by
  let : IsLocalRing D := residueLift_isLocalRing B L b
  change (D ⧸ maximalIdeal D) ≃+* L
  exact (Ideal.quotEquivOfEq (show maximalIdeal D = residueLiftClosedIdeal B L b from
    residueLift_maximalIdeal B L b)).trans
    (residueLiftQuotientEquiv B L b).toRingEquiv

@[simp]
theorem residueLiftResidueEquiv_residue (x : D) :
    let _ : IsLocalRing D := residueLift_isLocalRing B L b
    residueLiftResidueEquiv B L b (residue D x) = residueLiftPoint B L b x := by
  let : IsLocalRing D := residueLift_isLocalRing B L b
  change residueLiftResidueEquiv B L b (residue D x) = residueLiftPoint B L b x
  rfl

/-- The marked residue comparison retains the original coefficient map. -/
theorem residueLiftResidueEquiv_algebraMap (a : B) :
    let _ : IsLocalRing D := residueLift_isLocalRing B L b
    residueLiftResidueEquiv B L b (residue D (algebraMap B D a)) =
      algebraMap (ResidueField B) L (residue B a) := by
  let : IsLocalRing D := residueLift_isLocalRing B L b
  change residueLiftResidueEquiv B L b (residue D (algebraMap B D a)) = _
  exact (residueLiftResidueEquiv_residue B L b (algebraMap B D a)).trans
    (residueLiftPoint_algebraMap B L b a)

private theorem residueLift_algebraMap_injective : Function.Injective (algebraMap B D) := by
  let : Module.Free B D := residueLift_free B L b
  let : Nontrivial D := (residueLiftPoint B L b).toRingHom.domain_nontrivial
  exact FaithfulSMul.algebraMap_injective B D

private theorem residueLift_parameter_pow_ne_zero [IsDomain B]
    (p : B) (hp : Irreducible p) (n : ℕ) : (algebraMap B D p) ^ n ≠ 0 := by
  intro h
  apply pow_ne_zero n hp.ne_zero
  apply residueLift_algebraMap_injective B L b
  simpa only [map_pow, map_zero] using h

end LocalRing

section DVR

variable (B L : Type*) [CommRing B] [IsDomain B] [IsDiscreteValuationRing B]
  [Field L] [Algebra (ResidueField B) L] (b : PowerBasis (ResidueField B) L)

attribute [local instance] residueLiftAlgebra residueLiftTower

local notation "D" => ResidueLiftRing B L b

/-- The original uniformizer generates the actual new maximal ideal. -/
theorem residueLift_maximalIdeal_eq_span (p : B) (hp : Irreducible p) :
    let _ : IsLocalRing D := residueLift_isLocalRing B L b
    maximalIdeal D = Ideal.span {algebraMap B D p} := by
  let : IsLocalRing D := residueLift_isLocalRing B L b
  change maximalIdeal D = Ideal.span {algebraMap B D p}
  rw [residueLift_maximalIdeal B L b, residueLiftClosedIdeal_eq_map_algebraMap,
    hp.maximalIdeal_eq, Ideal.map_span, Set.image_singleton]

/-- The actual root algebra is a domain, using separatedness and the
principal maximal ideal rather than a separability assertion. -/
theorem residueLift_isDomain : IsDomain D := by
  let : IsLocalRing D := residueLift_isLocalRing B L b
  let : Module.Finite B D := residueLift_finite B L b
  let : IsNoetherianRing D := IsNoetherianRing.of_finite B D
  obtain ⟨p, hp⟩ := IsDiscreteValuationRing.exists_irreducible B
  exact IsLocalRing.isDomain_of_isHausdorff_of_maximalIdeal_eq_span (algebraMap B D p)
    (residueLift_maximalIdeal_eq_span B L b p hp)
    (residueLift_parameter_pow_ne_zero B L b p hp)

/-- The actual root algebra is a DVR with the original uniformizer.
The given power-basis field extension may be inseparable. -/
theorem residueLift_isDiscreteValuationRing :
    let _ : IsDomain D := residueLift_isDomain B L b
    IsDiscreteValuationRing D := by
  let : IsLocalRing D := residueLift_isLocalRing B L b
  let : Module.Finite B D := residueLift_finite B L b
  let : IsNoetherianRing D := IsNoetherianRing.of_finite B D
  obtain ⟨p, hp⟩ := IsDiscreteValuationRing.exists_irreducible B
  exact IsLocalRing.isDiscreteValuationRing_of_isHausdorff_of_maximalIdeal_eq_span
    (algebraMap B D p) (residueLift_maximalIdeal_eq_span B L b p hp)
    (residueLift_parameter_pow_ne_zero B L b p hp)

/-- Every original uniformizer remains a uniformizer in the constructed DVR. -/
theorem residueLift_irreducible_algebraMap (p : B) (hp : Irreducible p) :
    Irreducible (algebraMap B D p) := by
  let : IsDomain D := residueLift_isDomain B L b
  let : IsDiscreteValuationRing D := residueLift_isDiscreteValuationRing B L b
  exact (IsDiscreteValuationRing.irreducible_iff_uniformizer _).mpr
    (residueLift_maximalIdeal_eq_span B L b p hp)

/-- Completeness is transported through the original finite algebra and
the proved equality of maximal ideals. -/
theorem residueLift_isAdicComplete [IsAdicComplete (maximalIdeal B) B] :
    let _ : IsLocalRing D := residueLift_isLocalRing B L b
    IsAdicComplete (maximalIdeal D) D := by
  let : IsLocalRing D := residueLift_isLocalRing B L b
  let : Module.Finite B D := residueLift_finite B L b
  change IsAdicComplete (maximalIdeal D) D
  rw [residueLift_maximalIdeal B L b, residueLiftClosedIdeal_eq_map_algebraMap]
  exact IsAdicComplete.map_algebraMap_of_finite B (maximalIdeal B) D

end DVR

end PowerBasis
