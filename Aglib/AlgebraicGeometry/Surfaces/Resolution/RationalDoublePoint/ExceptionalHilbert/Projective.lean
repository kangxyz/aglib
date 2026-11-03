/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Surfaces.Resolution.RationalDoublePoint.ExceptionalHilbert
public import Aglib.AlgebraicGeometry.Cohomology.Duality.Projective.Relative.CohenMacaulayCurve.AnticanonicalHilbert.BaseChange

/-!
# Actual exceptional Hilbert numerics over arbitrary residue fields

The original tautological embedding and the actual closed-stalk CM parameters
supply the projective curve geometry. Only cohomology of the inverse exceptional
line remains an input. Ordinary field-extension cohomology constructs and
uses a finite Cartier representative without assuming one over the original
residue field. The entire quadratic kernel is then the existing algebraic
producer's conclusion on the original cone and chart maps.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry.Scheme.Modules AlgebraicGeometry.Scheme.Modules.Invertible
open AlgebraicGeometry.Scheme.Hom AlgebraicGeometry.Scheme.Cohomology
open IsLocalRing

universe u

namespace AlgebraicGeometry.Scheme.RationalSingularities.MaximalIdealBlowup

variable (A : Type u) [CommRing A] [IsLocalRing A]
  [IsDomain A] [IsNoetherianRing A] [IsIntegrallyClosed A]

/-- The field structure on the original maximal-ideal quotient. -/
local instance exceptionalProjectiveResidueField : Field (A ⧸ maximalIdeal A) :=
  Ideal.Quotient.field (maximalIdeal A)

/-- The original residue-field action on a maximal-ideal associated-graded component. -/
local instance exceptionalProjectiveComponentModule (r : ℕ) :
    Module (ResidueField A) (Ideal.associatedGradedQuotientGrading (maximalIdeal A) r) :=
  Submodule.module (Ideal.associatedGradedQuotientGrading (maximalIdeal A) r)

/-- Actual inverse-line cohomology gives the complete exceptional Hilbert
function over the original residue field, with no rational-point or Cartier-
representative hypothesis on that field. -/
theorem exceptional_hilbert_of_inverseLine_cohomology (hd : ringKrullDim A = 2)
    (hA : IsNagataRing.{u, 0} A) (hRat : NormalModificationH1Vanishing A)
    [Subsingleton (moduleCohomology (A ⧸ maximalIdeal A)
      (Over.mk (exceptionalStructureMap A hd))
      (dualLineBundle (exceptionalCurve A hd) (exceptionalLine A hd)).val 0)]
    (hJ : Module.finrank (A ⧸ maximalIdeal A)
      (moduleCohomology (A ⧸ maximalIdeal A) (Over.mk (exceptionalStructureMap A hd))
        (dualLineBundle (exceptionalCurve A hd) (exceptionalLine A hd)).val 1) = 1)
    (r : ℕ) :
    Module.finrank (ResidueField A)
      (Ideal.associatedGradedQuotientGrading (maximalIdeal A) r) = 2 * r + 1 := by
  let k := A ⧸ maximalIdeal A
  let E := exceptionalCurve A hd
  let X := Over.mk (exceptionalStructureMap A hd)
  obtain ⟨d, j, _, hjclosed, hj, ⟨eL⟩⟩ := exists_exceptionalTautologicalEmbedding A hd
  let := hjclosed
  let ι := ULift.{u} (Fin (d + 1))
  let Y := Over.mk (j ≫ ProjectiveSpace.toSpec k ι)
  have hj' : j ≫ ProjectiveSpace.toSpec k ι = exceptionalStructureMap A hd := hj
  have hUnit : Subsingleton
      (moduleCohomology k X (SheafOfModules.unit E.ringCatSheaf) 1) :=
    exceptionalUnit_h1_subsingleton A hd hA hRat
  have hUnitRank : Module.finrank k
      (moduleCohomology k X (SheafOfModules.unit E.ringCatSheaf) 0) = 1 :=
    exceptionalUnit_h0_finrank A hd hA hRat
  have hRank (M : E.Modules) (q : ℕ) :
      Module.finrank k (moduleCohomology k Y M q) =
        Module.finrank k (moduleCohomology k X M q) :=
    congrArg (fun f : E ⟶ Spec (.of k) =>
      Module.finrank k (moduleCohomology k (Over.mk f) M q)) hj'
  let L := curveHyperplaneLine k ι j
  let eD : (dualLineBundle E L).val ≅
      (dualLineBundle E (exceptionalLine A hd)).val :=
    InternalHom.iso E eL (Iso.refl (SheafOfModules.unit E.ringCatSheaf))
  let : Subsingleton (moduleCohomology k X (dualLineBundle E L).val 0) :=
    (moduleCohomologyIso X eD 0).injective.subsingleton
  let : Subsingleton (moduleCohomology k Y (dualLineBundle E L).val 0) := by
    dsimp only [Y]
    rw [hj']
    exact inferInstanceAs (Subsingleton (moduleCohomology k X (dualLineBundle E L).val 0))
  let : Subsingleton (moduleCohomology k Y (SheafOfModules.unit E.ringCatSheaf) 1) := by
    dsimp only [Y]
    rw [hj']
    exact hUnit
  have hO : Module.finrank k (moduleCohomology k Y
      (SheafOfModules.unit E.ringCatSheaf) 0) = 1 :=
    (hRank (SheafOfModules.unit E.ringCatSheaf) 0).trans hUnitRank
  have hD : Module.finrank k (moduleCohomology k Y
      (dualLineBundle E L).val 1) = 1 :=
    (hRank (dualLineBundle E L).val 1).trans
      ((moduleCohomologyIso X eD 1).finrank_eq.trans hJ)
  have h := cmCurve_hyperplanePower_h0_finrank k ι j
    (exceptionalCurve_closedPoint_cmParameter A hd hA hRat) hO hD r
  have hP : Module.finrank k
      (moduleCohomology k X (tensorPowerLineBundle E L r).val 0) = 2 * r + 1 :=
    (hRank (tensorPowerLineBundle E L r).val 0).symm.trans h
  let eP : exceptionalPower A hd r ≅ (tensorPowerLineBundle E L r).val :=
    exceptionalPowerTensorIso A hd r ≪≫ (TrivializedPower.powerIso E eL r).symm
  exact ((exceptionalGradedCohomologyEquiv A hd hA hRat r).trans
    (moduleCohomologyIso X eP 0)).finrank_eq.trans hP

/-- The original cotangent space has dimension three; this is derived from
the full exceptional curve, rather than used as a Hilbert-function premise. -/
theorem exceptional_cotangent_finrank_of_inverseLine_cohomology
    (hd : ringKrullDim A = 2) (hA : IsNagataRing.{u, 0} A)
    (hRat : NormalModificationH1Vanishing A)
    [Subsingleton (moduleCohomology (A ⧸ maximalIdeal A)
      (Over.mk (exceptionalStructureMap A hd))
      (dualLineBundle (exceptionalCurve A hd) (exceptionalLine A hd)).val 0)]
    (hJ : Module.finrank (A ⧸ maximalIdeal A)
      (moduleCohomology (A ⧸ maximalIdeal A) (Over.mk (exceptionalStructureMap A hd))
        (dualLineBundle (exceptionalCurve A hd) (exceptionalLine A hd)).val 1) = 1) :
    Module.finrank (ResidueField A) (CotangentSpace A) = 3 := by
  exact ((exceptionalPowerOneCotangentEquiv A).symm.trans
    (exceptionalPowerLayerGradingEquiv A 1)).finrank_eq.trans
      (exceptional_hilbert_of_inverseLine_cohomology A hd hA hRat hJ 1)

/-- The three-element minimal generating set is derived from the original
cotangent dimension. Its elements lie in the actual maximal ideal. -/
theorem exceptional_exists_three_generators_of_inverseLine_cohomology
    (hd : ringKrullDim A = 2) (hA : IsNagataRing.{u, 0} A)
    (hRat : NormalModificationH1Vanishing A)
    [Subsingleton (moduleCohomology (A ⧸ maximalIdeal A)
      (Over.mk (exceptionalStructureMap A hd))
      (dualLineBundle (exceptionalCurve A hd) (exceptionalLine A hd)).val 0)]
    (hJ : Module.finrank (A ⧸ maximalIdeal A)
      (moduleCohomology (A ⧸ maximalIdeal A) (Over.mk (exceptionalStructureMap A hd))
        (dualLineBundle (exceptionalCurve A hd) (exceptionalLine A hd)).val 1) = 1) :
    ∃ (t : maximalIdeal A) (g : Fin 2 → maximalIdeal A),
      Ideal.span (Set.range fun a =>
        (Localization.Away.CaseOne.orderedGenerators t g a : A)) = maximalIdeal A := by
  classical
  have hd₃ : (maximalIdeal A).spanFinrank = 3 :=
    (IsLocalRing.spanFinrank_eq_finrank_quotient (maximalIdeal A)
      (maximalIdeal A).fg_of_isNoetherianRing).trans
        (exceptional_cotangent_finrank_of_inverseLine_cohomology A hd hA hRat hJ)
  obtain ⟨s, hcard, hspan⟩ := Submodule.FG.exists_span_finset_card_eq_spanFinrank
    (maximalIdeal A).fg_of_isNoetherianRing
  obtain ⟨a, b, c, _, _, _, hs⟩ := Finset.card_eq_three.mp (hcard.trans hd₃)
  have hspan₃ : Ideal.span ({a, b, c} : Set A) = maximalIdeal A := by
    simpa only [hs, Finset.coe_insert, Finset.coe_singleton] using hspan
  have ha : a ∈ maximalIdeal A := hspan₃ ▸ Ideal.subset_span (by simp)
  have hb : b ∈ maximalIdeal A := hspan₃ ▸ Ideal.subset_span (by simp)
  have hc : c ∈ maximalIdeal A := hspan₃ ▸ Ideal.subset_span (by simp)
  let t : maximalIdeal A := ⟨a, ha⟩
  let g : Fin 2 → maximalIdeal A := ![⟨b, hb⟩, ⟨c, hc⟩]
  refine ⟨t, g, ?_⟩
  have hr : Set.range (fun i =>
      (Localization.Away.CaseOne.orderedGenerators t g i : A)) = {a, b, c} := by
    ext x
    constructor
    · rintro ⟨i, rfl⟩
      fin_cases i <;> simp [Localization.Away.CaseOne.orderedGenerators, t, g]
    · intro hx
      rcases hx with hx | hx | hx
      · exact ⟨0, hx.symm⟩
      · exact ⟨1, hx.symm⟩
      · exact ⟨2, hx.symm⟩
  rw [hr]; exact hspan₃

/-- The full canonical quadratic kernel and the actual ordinary-chart
exceptional presentation follow without choosing a Cartier divisor over the
original field. The generators are still explicit original elements. -/
theorem exceptional_quadratic_presentation_of_inverseLine_cohomology
    (hd : ringKrullDim A = 2) (hA : IsNagataRing.{u, 0} A)
    (hRat : NormalModificationH1Vanishing A)
    [Subsingleton (moduleCohomology (A ⧸ maximalIdeal A)
      (Over.mk (exceptionalStructureMap A hd))
      (dualLineBundle (exceptionalCurve A hd) (exceptionalLine A hd)).val 0)]
    (hJ : Module.finrank (A ⧸ maximalIdeal A)
      (moduleCohomology (A ⧸ maximalIdeal A) (Over.mk (exceptionalStructureMap A hd))
        (dualLineBundle (exceptionalCurve A hd) (exceptionalLine A hd)).val 1) = 1)
    (t : maximalIdeal A) (g : Fin 2 → maximalIdeal A)
    (hgen : Ideal.span (Set.range fun a =>
      (Localization.Away.CaseOne.orderedGenerators t g a : A)) = maximalIdeal A) :
    ∃ q : MvPolynomial (Fin 3) (ResidueField A),
      q ≠ 0 ∧ q.IsHomogeneous 2 ∧
      RingHom.ker (Localization.Away.CaseOne.canonicalConeMap t g) = Ideal.span {q} ∧
      (t : A) ≠ 0 ∧ MvPolynomial.FirstCoordinate.dehom q ≠ 0 ∧
      (MvPolynomial.FirstCoordinate.dehom q).totalDegree ≤ 2 ∧
      Nonempty (Localization.Away.CaseOne.Presentation A t g
        (MvPolynomial.FirstCoordinate.dehom q)) :=
  Localization.Away.CaseOne.exists_presentation_of_hilbert t g hgen
    (exceptional_hilbert_of_inverseLine_cohomology A hd hA hRat hJ)

end AlgebraicGeometry.Scheme.RationalSingularities.MaximalIdealBlowup
