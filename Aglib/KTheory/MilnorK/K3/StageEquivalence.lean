/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.KTheory.MilnorK.K3.StageLift
public import Aglib.KTheory.MilnorK.K3.DegreeGeneration
public import Mathlib.LinearAlgebra.DFinsupp

/-!
# Actual degree-stage residues and sections

The source is the image of the actual next polynomial degree span in the
quotient by the preceding span. The residue coordinates are the original
Milnor K₂ groups of the literal polynomial residue fields. Sections use the
canonical reduced representatives constructed in `StageLift`.
-/

@[expose] public noncomputable section

namespace MilnorK.K3.DegreeFiltration

open Polynomial PolynomialResidue

variable {k : Type*} [Field k]

/-- Monic irreducible polynomial places of exactly the indicated degree. -/
abbrev DegreePlace (k : Type*) [Field k] (d : ℕ) :=
  {p : MonicIrreducible k // p.val.natDegree = d}

/-- The actual next degree span, viewed modulo the actual preceding span. -/
def actualStage (k : Type*) [Field k] (d : ℕ) :
    Submodule ℤ (Group (RatFunc k) ⧸ lower k d) :=
  (lower k (d + 1)).map (lower k d).mkQ

instance instDegreeResidueAddCommGroup (d : ℕ) :
    (p : DegreePlace k d) → AddCommGroup (MilnorK.K2.Group (AdjoinRoot p.val.val)) :=
  fun _ => inferInstance

instance instDegreeResidueModule (d : ℕ) :
    (p : DegreePlace k d) → Module ℤ (MilnorK.K2.Group (AdjoinRoot p.val.val)) :=
  fun _ => inferInstance

/-- The dependent finite sum of the original residue-field Milnor K₂ groups. -/
abbrev DegreeResidues (k : Type*) [Field k] (d : ℕ) :=
  Π₀ p : DegreePlace k d, MilnorK.K2.Group (AdjoinRoot p.val.val)

/-- Restrict the checked finite-support total residue to places of degree `d`. -/
def degreeResidues (d : ℕ) : Group (RatFunc k) →ₗ[ℤ] DegreeResidues k d := by
  classical
  exact (DFinsupp.subtypeDomainLinearMap ℤ
    (fun p : MonicIrreducible k => MilnorK.K2.Group (AdjoinRoot p.val))
    (fun p => p.val.natDegree = d)).comp totalResidue

@[simp] theorem degreeResidues_apply (d : ℕ) (x : Group (RatFunc k))
    (p : DegreePlace k d) : degreeResidues d x p = residueAt p.val.val x := rfl

/-- Every degree-`d` coordinate kills the preceding polynomial span. -/
theorem lower_le_ker_degreeResidues (d : ℕ) :
    lower k d ≤ LinearMap.ker (degreeResidues d) := by
  intro x hx
  apply DFinsupp.ext
  intro p
  exact lower_le_ker_residueAt p.val.val p.val.property.1 (by simpa [p.property] using hx)

/-- The actual degree-restricted total residue on the lower-stage quotient. -/
def quotientDegreeResidues (d : ℕ) :
    (Group (RatFunc k) ⧸ lower k d) →ₗ[ℤ] DegreeResidues k d :=
  (lower k d).liftQ (degreeResidues d) (lower_le_ker_degreeResidues d)

theorem quotientDegreeResidues_mkQ (d : ℕ) (x : Group (RatFunc k)) :
    quotientDegreeResidues d ((lower k d).mkQ x) = degreeResidues d x := rfl

/-- The residue of an actual degree-stage class. -/
def actualStageResidues (d : ℕ) : actualStage k d →ₗ[ℤ] DegreeResidues k d :=
  (quotientDegreeResidues d).comp (actualStage k d).subtype

/-- Transport the checked section along the literal equality of degree bounds. -/
def degreeSection (d : ℕ) (p : DegreePlace k d) :
    MilnorK.K2.Group (AdjoinRoot p.val.val) →ₗ[ℤ] Group (RatFunc k) ⧸ lower k d :=
  ((lower k p.val.val.natDegree).mapQ (lower k d) LinearMap.id
    (by simpa only [p.property, Submodule.comap_id] using (le_refl (lower k d)))).comp
      (stageLift p.val.val p.val.property.1)

/-- A section still has precisely its literal reduced triple-symbol value. -/
@[simp] theorem degreeSection_symbol (d : ℕ) (p : DegreePlace k d)
    (a b : (AdjoinRoot p.val.val)ˣ) :
    degreeSection d p (MilnorK.K2.symbol a b) =
      (lower k d).mkQ
        (symbol3 (polynomialUnit p.val.val p.val.property.2.ne_zero)
          (reducedUnit p.val.val p.val.property.1 a)
          (reducedUnit p.val.val p.val.property.1 b)) := rfl

/-- Reduced polynomial entries give the expected literal quotient symbol. -/
theorem degreeSection_reduced (d : ℕ) (p : DegreePlace k d) (a b : k[X])
    (ha : a ≠ 0) (hb : b ≠ 0) (hadeg : a.natDegree < d) (hbdeg : b.natDegree < d) :
    degreeSection d p (MilnorK.K2.symbol
      (quotientUnit p.val.val a
        (p.val.property.1.not_dvd_of_natDegree_lt ha (by simpa [p.property] using hadeg)))
      (quotientUnit p.val.val b
        (p.val.property.1.not_dvd_of_natDegree_lt hb (by simpa [p.property] using hbdeg)))) =
      (lower k d).mkQ
        (symbol3 (polynomialUnit p.val.val p.val.property.2.ne_zero)
          (polynomialUnit a ha) (polynomialUnit b hb)) := by
  unfold degreeSection
  rw [LinearMap.comp_apply, stageLift_reduced _ _ _ _ _ _
    (by simpa [p.property] using hadeg) (by simpa [p.property] using hbdeg)]
  rfl

/-- A canonical section lies in the image of the actual next polynomial span. -/
theorem degreeSection_mem_actualStage (d : ℕ) (p : DegreePlace k d)
    (x : MilnorK.K2.Group (AdjoinRoot p.val.val)) : degreeSection d p x ∈ actualStage k d := by
  have h : (actualStage k d).mkQ.comp (degreeSection d p) = 0 := by
    apply MilnorK.K2.linearMap_ext
    intro a b
    change (actualStage k d).mkQ (degreeSection d p (MilnorK.K2.symbol a b)) = 0
    rw [degreeSection_symbol]
    apply (Submodule.Quotient.mk_eq_zero _).mpr
    apply Submodule.mem_map.mpr
    refine ⟨_, ?_, rfl⟩
    exact polynomial_symbol_mem_lower (d + 1) _ _ _ _ _ _
      (by omega)
      ((reducedRepresentative_natDegree_lt p.val.val p.val.property.1 a).trans_le
        (by omega))
      ((reducedRepresentative_natDegree_lt p.val.val p.val.property.1 b).trans_le
        (by omega))
  exact (Submodule.Quotient.mk_eq_zero _).mp (LinearMap.congr_fun h x)

/-- Distinct monic places of the same degree cannot divide each other. -/
theorem degreePlace_not_dvd (d : ℕ) (p q : DegreePlace k d) (hpq : p ≠ q) :
    ¬ q.val.val ∣ p.val.val := by
  intro hdiv
  apply hpq
  apply Subtype.ext
  apply Subtype.ext
  exact eq_of_monic_of_dvd_of_natDegree_le q.val.property.1 p.val.property.1 hdiv
    (by rw [p.property, q.property])

/-- Equal-degree off-diagonal residues vanish on every literal reduced section symbol. -/
theorem residueAt_degreeSection_symbol_of_ne (d : ℕ) (p q : DegreePlace k d)
    (hpq : p ≠ q) (a b : (AdjoinRoot p.val.val)ˣ) :
    residueAt q.val.val
      (symbol3 (polynomialUnit p.val.val p.val.property.2.ne_zero)
        (reducedUnit p.val.val p.val.property.1 a)
        (reducedUnit p.val.val p.val.property.1 b)) = 0 := by
  apply residueAt_polynomial_units_zero
  · exact degreePlace_not_dvd d p q hpq
  · exact q.val.property.1.not_dvd_of_natDegree_lt
      (reducedRepresentative_ne_zero p.val.val p.val.property.1 a)
      (by simpa only [p.property, q.property] using
        reducedRepresentative_natDegree_lt p.val.val p.val.property.1 a)
  · exact q.val.property.1.not_dvd_of_natDegree_lt
      (reducedRepresentative_ne_zero p.val.val p.val.property.1 b)
      (by simpa only [p.property, q.property] using
        reducedRepresentative_natDegree_lt p.val.val p.val.property.1 b)

/-- The actual degree residues of each section are concentrated at its own place. -/
@[simp] theorem quotientDegreeResidues_degreeSection (d : ℕ) [DecidableEq (DegreePlace k d)]
    (p : DegreePlace k d)
    (x : MilnorK.K2.Group (AdjoinRoot p.val.val)) :
    quotientDegreeResidues d (degreeSection d p x) = DFinsupp.single p x := by
  classical
  have h : (quotientDegreeResidues d).comp (degreeSection d p) = DFinsupp.lsingle (R := ℤ)
      (M := fun q : DegreePlace k d => MilnorK.K2.Group (AdjoinRoot q.val.val)) p := by
    apply MilnorK.K2.linearMap_ext
    intro a b
    apply DFinsupp.ext
    intro q
    simp only [LinearMap.comp_apply, degreeSection_symbol, quotientDegreeResidues_mkQ,
      degreeResidues_apply, DFinsupp.lsingle_apply]
    by_cases hpq : p = q
    · subst q
      simp only [DFinsupp.single_eq_same, reducedUnit,
        residueAt_reduced p.val.val p.val.property.1 _ _ _ _
          (reducedRepresentative_natDegree_lt p.val.val p.val.property.1 a)
          (reducedRepresentative_natDegree_lt p.val.val p.val.property.1 b),
        quotientUnit_reducedRepresentative]
    · rw [DFinsupp.single_eq_of_ne (Ne.symm hpq), residueAt_degreeSection_symbol_of_ne d p q hpq]
  exact LinearMap.congr_fun h x

/-- Off-diagonal vanishing holds on all original K₂ classes, not just symbols. -/
theorem quotientDegreeResidues_degreeSection_of_ne (d : ℕ) (p q : DegreePlace k d)
    (hpq : p ≠ q) (x : MilnorK.K2.Group (AdjoinRoot p.val.val)) :
    quotientDegreeResidues d (degreeSection d p x) q = 0 := by
  classical
  rw [quotientDegreeResidues_degreeSection, DFinsupp.single_eq_of_ne (Ne.symm hpq)]

/-- The finite sum of the actual canonical residue-field sections. -/
def degreeSectionSum (d : ℕ) : DegreeResidues k d →ₗ[ℤ] Group (RatFunc k) ⧸ lower k d := by
  classical
  exact DFinsupp.lsum ℤ (degreeSection d)

@[simp] theorem degreeSectionSum_single (d : ℕ) [DecidableEq (DegreePlace k d)]
    (p : DegreePlace k d)
    (x : MilnorK.K2.Group (AdjoinRoot p.val.val)) :
    degreeSectionSum d (DFinsupp.single p x) = degreeSection d p x := by
  classical
  exact DFinsupp.lsum_single ℤ (degreeSection d) p x

/-- The assembled finite sum lies in the actual next degree stage. -/
theorem degreeSectionSum_mem_actualStage (d : ℕ) (x : DegreeResidues k d) :
    degreeSectionSum d x ∈ actualStage k d := by
  classical
  exact (actualStage k d).dfinsuppSumAddHom_mem x
    (fun p => (degreeSection d p).toAddMonoidHom)
    (fun p _ => degreeSection_mem_actualStage d p (x p))

/-- The actual total residues recover every input to the finite sum of sections. -/
theorem quotientDegreeResidues_comp_degreeSectionSum (d : ℕ) :
    (quotientDegreeResidues d).comp (degreeSectionSum (k := k) d) = LinearMap.id := by
  classical
  apply DFinsupp.lhom_ext
  intro p x
  simp only [LinearMap.comp_apply, degreeSectionSum_single,
    quotientDegreeResidues_degreeSection, LinearMap.id_apply]

@[simp] theorem quotientDegreeResidues_degreeSectionSum (d : ℕ)
    (x : DegreeResidues k d) : quotientDegreeResidues d (degreeSectionSum d x) = x :=
  LinearMap.congr_fun (quotientDegreeResidues_comp_degreeSectionSum d) x

/-- Generation of the actual next span makes the sum of sections cover its image.
The positivity hypothesis is necessary: the degree-zero stage contains constants. -/
theorem actualStage_le_range_degreeSectionSum (d : ℕ) (hd : 0 < d) :
    actualStage k d ≤ LinearMap.range (degreeSectionSum d) := by
  classical
  apply Submodule.map_le_iff_le_comap.mpr
  rw [lower_succ_eq d hd]
  refine sup_le ((lower k d).le_comap_mkQ _) ?_
  apply Submodule.span_le.mpr
  rintro x ⟨p, a, b, hp, ha, hb, hpm, hpi, hpdeg, hadeg, hbdeg, rfl⟩
  let : Fact (Irreducible p) := ⟨hpi⟩
  let place : DegreePlace k d := ⟨⟨p, hpm, hpi⟩, hpdeg⟩
  let residueSymbol : MilnorK.K2.Group (AdjoinRoot place.val.val) := MilnorK.K2.symbol
    (quotientUnit place.val.val a
      (hpm.not_dvd_of_natDegree_lt ha (by simpa only [hpdeg] using hadeg)))
    (quotientUnit place.val.val b
      (hpm.not_dvd_of_natDegree_lt hb (by simpa only [hpdeg] using hbdeg)))
  refine ⟨DFinsupp.single place residueSymbol, ?_⟩
  rw [degreeSectionSum_single]
  exact degreeSection_reduced d place a b ha hb hadeg hbdeg

/-- The original finite sections generate exactly the actual quotient stage. -/
theorem range_degreeSectionSum (d : ℕ) (hd : 0 < d) :
    LinearMap.range (degreeSectionSum (k := k) d) = actualStage k d := by
  apply le_antisymm
  · rintro x ⟨y, rfl⟩
    exact degreeSectionSum_mem_actualStage d y
  · exact actualStage_le_range_degreeSectionSum d hd

/-- The inverse identity on the actual stage follows from checked degree generation. -/
theorem degreeSectionSum_quotientDegreeResidues (d : ℕ) (hd : 0 < d)
    (x : Group (RatFunc k) ⧸ lower k d) (hx : x ∈ actualStage k d) :
    degreeSectionSum d (quotientDegreeResidues d x) = x := by
  obtain ⟨y, rfl⟩ := actualStage_le_range_degreeSectionSum d hd hx
  rw [quotientDegreeResidues_degreeSectionSum]

/-- The finite sum of sections, with codomain restricted to the proved actual stage. -/
def actualStageSectionSum (d : ℕ) : DegreeResidues k d →ₗ[ℤ] actualStage k d :=
  (degreeSectionSum d).codRestrict (actualStage k d) (degreeSectionSum_mem_actualStage d)

@[simp] theorem actualStageSectionSum_coe (d : ℕ) (x : DegreeResidues k d) :
    (actualStageSectionSum d x : Group (RatFunc k) ⧸ lower k d) = degreeSectionSum d x := rfl

/-- Actual stage residues are a left inverse of the finite sum of sections. -/
theorem actualStageResidues_comp_actualStageSectionSum (d : ℕ) :
    (actualStageResidues d).comp (actualStageSectionSum (k := k) d) = LinearMap.id := by
  apply LinearMap.ext
  intro x
  exact quotientDegreeResidues_degreeSectionSum d x

/-- Positive-degree stage generation supplies the other inverse identity. -/
theorem actualStageSectionSum_comp_actualStageResidues (d : ℕ) (hd : 0 < d) :
    (actualStageSectionSum d).comp (actualStageResidues (k := k) d) = LinearMap.id := by
  apply LinearMap.ext
  intro x
  apply Subtype.ext
  exact degreeSectionSum_quotientDegreeResidues d hd x.val x.property

/-- The positive-degree actual polynomial stage is equivalent to the finite direct sum
of the original residue-field Milnor K₂ groups at places of that degree. -/
def actualStageEquiv (d : ℕ) (hd : 0 < d) :
    actualStage k d ≃ₗ[ℤ] DegreeResidues k d :=
  LinearEquiv.ofLinearMap (actualStageResidues d) (actualStageSectionSum d)
    (actualStageResidues_comp_actualStageSectionSum d)
    (actualStageSectionSum_comp_actualStageResidues d hd)

/-- The equivalence's forward map is precisely the degree-restricted actual total residue. -/
@[simp] theorem actualStageEquiv_apply (d : ℕ) (hd : 0 < d) (x : actualStage k d) :
    actualStageEquiv d hd x = quotientDegreeResidues d x.val := rfl

/-- Each coordinate on an actual representative is its original polynomial residue. -/
theorem actualStageEquiv_mkQ_apply (d : ℕ) (hd : 0 < d)
    (x : Group (RatFunc k)) (hx : x ∈ lower k (d + 1)) (p : DegreePlace k d) :
    actualStageEquiv d hd
      ⟨(lower k d).mkQ x, Submodule.mem_map.mpr ⟨x, hx, rfl⟩⟩ p = residueAt p.val.val x := rfl

/-- The inverse is exactly the finite sum of canonical reduced-symbol sections. -/
@[simp] theorem actualStageEquiv_symm_coe (d : ℕ) (hd : 0 < d) (x : DegreeResidues k d) :
    ((actualStageEquiv d hd).symm x : Group (RatFunc k) ⧸ lower k d) = degreeSectionSum d x := rfl

/-- Within the next actual span, vanishing degree-`d` residues means membership
in the preceding actual span. This is the degree-stage kernel statement. -/
theorem degreeResidues_eq_zero_iff_mem_lower (d : ℕ) (hd : 0 < d)
    (x : Group (RatFunc k)) (hx : x ∈ lower k (d + 1)) :
    degreeResidues d x = 0 ↔ x ∈ lower k d := by
  constructor
  · intro h
    have hstage : (lower k d).mkQ x ∈ actualStage k d :=
      Submodule.mem_map.mpr ⟨x, hx, rfl⟩
    have hi := degreeSectionSum_quotientDegreeResidues d hd ((lower k d).mkQ x) hstage
    rw [quotientDegreeResidues_mkQ, h, map_zero] at hi
    exact (Submodule.Quotient.mk_eq_zero _).mp hi.symm
  · intro h
    exact lower_le_ker_degreeResidues d h

end MilnorK.K3.DegreeFiltration
