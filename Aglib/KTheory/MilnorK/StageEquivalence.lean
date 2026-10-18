/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.KTheory.MilnorK.StageLift
public import Aglib.KTheory.MilnorK.DegreeGeneration
public import Aglib.KTheory.MilnorK.Residue.Polynomial.Support
public import Mathlib.LinearAlgebra.DFinsupp

/-!
# Actual polynomial degree-stage equivalences in every Milnor degree

The actual next polynomial span modulo the preceding span is identified with
finitely supported classes in the original residue-field Milnor groups. The
inverse uses canonical reduced representatives and the final-slot convention.
The residue degree may be zero, and the field is arbitrary.
-/

@[expose] public noncomputable section

namespace MilnorK.DegreeFiltration

open Polynomial PolynomialResidue

variable {F : Type*} [Field F]

/-- Monic irreducible polynomial places of the indicated degree. -/
abbrev DegreePlace (F : Type*) [Field F] (d : ℕ) :=
  {p : MonicIrreducible F // p.val.natDegree = d}

/-- The actual next polynomial span modulo the actual preceding span. -/
def actualStage (F : Type*) [Field F] (n d : ℕ) :
    Submodule ℤ (K (RatFunc F) (n + 1) ⧸ lower F (n + 1) d) :=
  (lower F (n + 1) (d + 1)).map (lower F (n + 1) d).mkQ

instance instDegreeResidueAddCommGroup (n d : ℕ) :
    (p : DegreePlace F d) → AddCommGroup (K (AdjoinRoot p.val.val) n) :=
  fun _ => inferInstance

instance instDegreeResidueModule (n d : ℕ) :
    (p : DegreePlace F d) → Module ℤ (K (AdjoinRoot p.val.val) n) :=
  fun _ => inferInstance

/-- The finite dependent sum of the original residue-field Milnor groups. -/
abbrev DegreeResidues (F : Type*) [Field F] (n d : ℕ) :=
  Π₀ p : DegreePlace F d, K (AdjoinRoot p.val.val) n

/-- Restrict the actual finite-support total residue to one polynomial degree. -/
def degreeResidues (n d : ℕ) : K (RatFunc F) (n + 1) →ₗ[ℤ] DegreeResidues F n d := by
  classical
  exact (DFinsupp.subtypeDomainLinearMap ℤ
    (fun p : MonicIrreducible F => K (AdjoinRoot p.val) n)
    (fun p => p.val.natDegree = d)).comp (totalResidue n)

@[simp] theorem degreeResidues_apply (n d : ℕ) (x : K (RatFunc F) (n + 1))
    (p : DegreePlace F d) : degreeResidues n d x p = residueAt p.val.val n x := rfl

/-- Degree-`d` residues annihilate the actual preceding span. -/
theorem lower_le_ker_degreeResidues (n d : ℕ) :
    lower F (n + 1) d ≤ LinearMap.ker (degreeResidues n d) := by
  intro x hx
  apply DFinsupp.ext
  intro p
  exact lower_le_ker_residueAt p.val.val p.val.property.1 n
    (by simpa only [p.property] using hx)

/-- The degree-restricted total residue on the actual lower-stage quotient. -/
def quotientDegreeResidues (n d : ℕ) :
    (K (RatFunc F) (n + 1) ⧸ lower F (n + 1) d) →ₗ[ℤ] DegreeResidues F n d :=
  (lower F (n + 1) d).liftQ (degreeResidues n d) (lower_le_ker_degreeResidues n d)

theorem quotientDegreeResidues_mkQ (n d : ℕ) (x : K (RatFunc F) (n + 1)) :
    quotientDegreeResidues n d ((lower F (n + 1) d).mkQ x) = degreeResidues n d x := rfl

/-- The actual stage's residue coordinates. -/
def actualStageResidues (n d : ℕ) : actualStage F n d →ₗ[ℤ] DegreeResidues F n d :=
  (quotientDegreeResidues n d).comp (actualStage F n d).subtype

/-- Transport the canonical lift along the literal equality of polynomial degrees. -/
def degreeSection (n d : ℕ) (p : DegreePlace F d) :
    K (AdjoinRoot p.val.val) n →ₗ[ℤ] K (RatFunc F) (n + 1) ⧸ lower F (n + 1) d :=
  ((lower F (n + 1) p.val.val.natDegree).mapQ (lower F (n + 1) d) LinearMap.id
    (by simpa only [p.property, Submodule.comap_id] using
      (le_refl (lower F (n + 1) d)))).comp (stageLift p.val.val p.val.property.1 n)

/-- The section retains its canonical final-slot symbol formula. -/
@[simp] theorem degreeSection_symbol (n d : ℕ) (p : DegreePlace F d)
    (a : SymbolTuple (AdjoinRoot p.val.val) n) :
    degreeSection n d p (symbol a) = (lower F (n + 1) d).mkQ
      (symbol (Fin.snoc (reducedTuple p.val.val p.val.property.1 a)
        (polynomialUnit F p.val.val p.val.property.2.ne_zero))) := by
  unfold degreeSection
  rw [LinearMap.comp_apply, stageLift_symbol]
  rfl

/-- Already reduced entries have their literal final-slot quotient value. -/
theorem degreeSection_reduced (n d : ℕ) (p : DegreePlace F d) (a : Fin n → F[X])
    (ha : ∀ i, a i ≠ 0) (hdeg : ∀ i, (a i).natDegree < d) :
    degreeSection n d p (symbol (fun i => quotientUnit p.val.val (a i)
      (p.val.property.1.not_dvd_of_natDegree_lt (ha i)
        (by simpa only [p.property] using hdeg i)))) =
      (lower F (n + 1) d).mkQ (symbol (Fin.snoc (polynomialTuple a ha)
        (polynomialUnit F p.val.val p.val.property.2.ne_zero))) := by
  unfold degreeSection
  rw [LinearMap.comp_apply, stageLift_reduced _ _ _ _
    (fun i => by simpa only [p.property] using hdeg i)]
  rfl

/-- A canonical section belongs to the image of the actual next polynomial span. -/
theorem degreeSection_mem_actualStage (n d : ℕ) (p : DegreePlace F d)
    (x : K (AdjoinRoot p.val.val) n) : degreeSection n d p x ∈ actualStage F n d := by
  have h : (actualStage F n d).mkQ.comp (degreeSection n d p) = 0 := by
    apply linearMap_ext
    intro a
    change (actualStage F n d).mkQ (degreeSection n d p (symbol a)) = 0
    rw [degreeSection_symbol]
    apply (Submodule.Quotient.mk_eq_zero _).mpr
    apply Submodule.mem_map.mpr
    refine ⟨_, ?_, rfl⟩
    rw [lower_succ_eq d (by simpa only [p.property] using p.val.property.2.natDegree_pos)]
    exact top_mem d p.val.val (fun i => reducedRepresentative p.val.val p.val.property.1 (a i))
      p.val.property.2.ne_zero
      (fun i => reducedRepresentative_ne_zero p.val.val p.val.property.1 (a i))
      p.val.property.1 p.val.property.2 p.property
      (fun i => by simpa only [p.property] using
        reducedRepresentative_natDegree_lt p.val.val p.val.property.1 (a i))
  exact (Submodule.Quotient.mk_eq_zero _).mp (LinearMap.congr_fun h x)

/-- Distinct monic places of the same degree cannot divide one another. -/
theorem degreePlace_not_dvd (d : ℕ) (p q : DegreePlace F d) (hpq : p ≠ q) :
    ¬ q.val.val ∣ p.val.val := by
  intro hdiv
  apply hpq
  apply Subtype.ext
  apply Subtype.ext
  exact eq_of_monic_of_dvd_of_natDegree_le q.val.property.1 p.val.property.1 hdiv
    (by rw [p.property, q.property])

/-- Equal-degree off-diagonal residues vanish on canonical section symbols. -/
theorem residueAt_degreeSection_symbol_of_ne (n d : ℕ) (p q : DegreePlace F d)
    (hpq : p ≠ q) (a : SymbolTuple (AdjoinRoot p.val.val) n) :
    residueAt q.val.val n (symbol (Fin.snoc (reducedTuple p.val.val p.val.property.1 a)
      (polynomialUnit F p.val.val p.val.property.2.ne_zero))) = 0 := by
  let b : Fin (n + 1) → F[X] :=
    Fin.snoc (fun i => reducedRepresentative p.val.val p.val.property.1 (a i)) p.val.val
  have hb : ∀ i, b i ≠ 0 := by
    intro i
    refine Fin.lastCases ?_ (fun j => ?_) i
    · simpa only [b, Fin.snoc_last] using p.val.property.2.ne_zero
    · simpa only [b, Fin.snoc_castSucc] using
        reducedRepresentative_ne_zero p.val.val p.val.property.1 (a j)
  have htuple : Fin.snoc (reducedTuple p.val.val p.val.property.1 a)
      (polynomialUnit F p.val.val p.val.property.2.ne_zero) = polynomialTuple b hb := by
    funext i
    refine Fin.lastCases ?_ (fun j => ?_) i <;>
      simp only [b, polynomialTuple, reducedTuple, reducedUnit, Fin.snoc_last, Fin.snoc_castSucc]
  rw [htuple]
  apply residueAt_polynomial_units_zero q.val.val n b hb
  intro i
  refine Fin.lastCases ?_ (fun j => ?_) i
  · simpa only [b, Fin.snoc_last] using degreePlace_not_dvd d p q hpq
  · simp only [b, Fin.snoc_castSucc]
    exact q.val.property.1.not_dvd_of_natDegree_lt
      (reducedRepresentative_ne_zero p.val.val p.val.property.1 (a j))
      (by simpa only [p.property, q.property] using
        reducedRepresentative_natDegree_lt p.val.val p.val.property.1 (a j))

/-- Actual degree residues of a section are concentrated at its own place. -/
@[simp] theorem quotientDegreeResidues_degreeSection (n d : ℕ)
    [DecidableEq (DegreePlace F d)] (p : DegreePlace F d) (x : K (AdjoinRoot p.val.val) n) :
    quotientDegreeResidues n d (degreeSection n d p x) = DFinsupp.single p x := by
  classical
  have h : (quotientDegreeResidues n d).comp (degreeSection n d p) = DFinsupp.lsingle (R := ℤ)
      (M := fun q : DegreePlace F d => K (AdjoinRoot q.val.val) n) p := by
    apply linearMap_ext
    intro a
    apply DFinsupp.ext
    intro q
    simp only [LinearMap.comp_apply, degreeSection_symbol, quotientDegreeResidues_mkQ,
      degreeResidues_apply, DFinsupp.lsingle_apply]
    by_cases hpq : p = q
    · subst q
      rw [DFinsupp.single_eq_same]
      exact stageResidue_stageSymbol p.val.val p.val.property.1 a
    · rw [DFinsupp.single_eq_of_ne (Ne.symm hpq),
        residueAt_degreeSection_symbol_of_ne n d p q hpq]
  exact LinearMap.congr_fun h x

/-- Off-diagonal vanishing holds for all original residue-field Milnor classes. -/
theorem quotientDegreeResidues_degreeSection_of_ne (n d : ℕ) (p q : DegreePlace F d)
    (hpq : p ≠ q) (x : K (AdjoinRoot p.val.val) n) :
    quotientDegreeResidues n d (degreeSection n d p x) q = 0 := by
  classical
  rw [quotientDegreeResidues_degreeSection, DFinsupp.single_eq_of_ne (Ne.symm hpq)]

/-- The finite sum of the actual canonical residue-field sections. -/
def degreeSectionSum (n d : ℕ) :
    DegreeResidues F n d →ₗ[ℤ] K (RatFunc F) (n + 1) ⧸ lower F (n + 1) d := by
  classical
  exact DFinsupp.lsum ℤ (degreeSection n d)

@[simp] theorem degreeSectionSum_single (n d : ℕ) [DecidableEq (DegreePlace F d)]
    (p : DegreePlace F d) (x : K (AdjoinRoot p.val.val) n) :
    degreeSectionSum n d (DFinsupp.single p x) = degreeSection n d p x := by
  classical
  exact DFinsupp.lsum_single ℤ (degreeSection n d) p x

/-- The assembled finite sum lies in the actual next degree stage. -/
theorem degreeSectionSum_mem_actualStage (n d : ℕ) (x : DegreeResidues F n d) :
    degreeSectionSum n d x ∈ actualStage F n d := by
  classical
  exact (actualStage F n d).dfinsuppSumAddHom_mem x
    (fun p => (degreeSection n d p).toAddMonoidHom)
    (fun p _ => degreeSection_mem_actualStage n d p (x p))

/-- The actual degree residues recover every finite sum input. -/
theorem quotientDegreeResidues_comp_degreeSectionSum (n d : ℕ) :
    (quotientDegreeResidues n d).comp (degreeSectionSum (F := F) n d) = LinearMap.id := by
  classical
  apply DFinsupp.lhom_ext
  intro p x
  simp only [LinearMap.comp_apply, degreeSectionSum_single,
    quotientDegreeResidues_degreeSection, LinearMap.id_apply]

@[simp] theorem quotientDegreeResidues_degreeSectionSum (n d : ℕ)
    (x : DegreeResidues F n d) : quotientDegreeResidues n d (degreeSectionSum n d x) = x :=
  LinearMap.congr_fun (quotientDegreeResidues_comp_degreeSectionSum n d) x

/-- Checked degree generation makes the sections cover the actual positive stage. -/
theorem actualStage_le_range_degreeSectionSum (n d : ℕ) (hd : 0 < d) :
    actualStage F n d ≤ LinearMap.range (degreeSectionSum n d) := by
  classical
  apply Submodule.map_le_iff_le_comap.mpr
  rw [lower_succ_eq d hd]
  refine sup_le ((lower F (n + 1) d).le_comap_mkQ _) ?_
  apply Submodule.span_le.mpr
  rintro x ⟨p, a, hp, ha, hpm, hpi, hpdeg, hadeg, rfl⟩
  let : Fact (Irreducible p) := ⟨hpi⟩
  let place : DegreePlace F d := ⟨⟨p, hpm, hpi⟩, hpdeg⟩
  let residueSymbol : K (AdjoinRoot place.val.val) n := symbol (fun i =>
    quotientUnit place.val.val (a i)
      (hpm.not_dvd_of_natDegree_lt (ha i) (by simpa only [hpdeg] using hadeg i)))
  refine ⟨DFinsupp.single place residueSymbol, ?_⟩
  rw [degreeSectionSum_single]
  exact degreeSection_reduced n d place a ha hadeg

/-- The sections generate precisely the actual degree stage. -/
theorem range_degreeSectionSum (n d : ℕ) (hd : 0 < d) :
    LinearMap.range (degreeSectionSum (F := F) n d) = actualStage F n d := by
  apply le_antisymm
  · rintro x ⟨y, rfl⟩
    exact degreeSectionSum_mem_actualStage n d y
  · exact actualStage_le_range_degreeSectionSum n d hd

/-- Generation proves the inverse identity on the actual degree stage. -/
theorem degreeSectionSum_quotientDegreeResidues (n d : ℕ) (hd : 0 < d)
    (x : K (RatFunc F) (n + 1) ⧸ lower F (n + 1) d) (hx : x ∈ actualStage F n d) :
    degreeSectionSum n d (quotientDegreeResidues n d x) = x := by
  obtain ⟨y, rfl⟩ := actualStage_le_range_degreeSectionSum n d hd hx
  rw [quotientDegreeResidues_degreeSectionSum]

/-- Restrict the finite sum's codomain to the proved actual stage. -/
def actualStageSectionSum (n d : ℕ) : DegreeResidues F n d →ₗ[ℤ] actualStage F n d :=
  (degreeSectionSum n d).codRestrict (actualStage F n d) (degreeSectionSum_mem_actualStage n d)

@[simp] theorem actualStageSectionSum_coe (n d : ℕ) (x : DegreeResidues F n d) :
    (actualStageSectionSum n d x : K (RatFunc F) (n + 1) ⧸ lower F (n + 1) d) =
      degreeSectionSum n d x := rfl

/-- The residue is a left inverse of the finite sum of sections. -/
theorem actualStageResidues_comp_actualStageSectionSum (n d : ℕ) :
    (actualStageResidues n d).comp (actualStageSectionSum (F := F) n d) = LinearMap.id := by
  apply LinearMap.ext
  intro x
  exact quotientDegreeResidues_degreeSectionSum n d x

/-- Positive degree generation supplies the other inverse identity. -/
theorem actualStageSectionSum_comp_actualStageResidues (n d : ℕ) (hd : 0 < d) :
    (actualStageSectionSum n d).comp (actualStageResidues (F := F) n d) = LinearMap.id := by
  apply LinearMap.ext
  intro x
  apply Subtype.ext
  exact degreeSectionSum_quotientDegreeResidues n d hd x.val x.property

/-- The positive polynomial degree stage equals the finite direct sum of the
original degree-`n` residue-field Milnor groups, including `n = 0`. -/
def actualStageEquiv (n d : ℕ) (hd : 0 < d) :
    actualStage F n d ≃ₗ[ℤ] DegreeResidues F n d :=
  LinearEquiv.ofLinearMap (actualStageResidues n d) (actualStageSectionSum n d)
    (actualStageResidues_comp_actualStageSectionSum n d)
    (actualStageSectionSum_comp_actualStageResidues n d hd)

@[simp] theorem actualStageEquiv_apply (n d : ℕ) (hd : 0 < d) (x : actualStage F n d) :
    actualStageEquiv n d hd x = quotientDegreeResidues n d x.val := rfl

/-- Each coordinate on a representative is its original polynomial residue. -/
theorem actualStageEquiv_mkQ_apply (n d : ℕ) (hd : 0 < d)
    (x : K (RatFunc F) (n + 1)) (hx : x ∈ lower F (n + 1) (d + 1)) (p : DegreePlace F d) :
    actualStageEquiv n d hd
      ⟨(lower F (n + 1) d).mkQ x, Submodule.mem_map.mpr ⟨x, hx, rfl⟩⟩ p =
        residueAt p.val.val n x := rfl

@[simp] theorem actualStageEquiv_symm_coe (n d : ℕ) (hd : 0 < d) (x : DegreeResidues F n d) :
    ((actualStageEquiv n d hd).symm x : K (RatFunc F) (n + 1) ⧸ lower F (n + 1) d) =
      degreeSectionSum n d x := rfl

/-- Within the next actual span, zero top residues characterize the preceding span. -/
theorem degreeResidues_eq_zero_iff_mem_lower (n d : ℕ) (hd : 0 < d)
    (x : K (RatFunc F) (n + 1)) (hx : x ∈ lower F (n + 1) (d + 1)) :
    degreeResidues n d x = 0 ↔ x ∈ lower F (n + 1) d := by
  constructor
  · intro h
    have hstage : (lower F (n + 1) d).mkQ x ∈ actualStage F n d :=
      Submodule.mem_map.mpr ⟨x, hx, rfl⟩
    have hi := degreeSectionSum_quotientDegreeResidues n d hd ((lower F (n + 1) d).mkQ x) hstage
    rw [quotientDegreeResidues_mkQ, h, map_zero] at hi
    exact (Submodule.Quotient.mk_eq_zero _).mp hi.symm
  · intro h
    exact lower_le_ker_degreeResidues n d h

end MilnorK.DegreeFiltration
