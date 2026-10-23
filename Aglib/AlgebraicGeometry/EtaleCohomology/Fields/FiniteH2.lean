/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.Fields.FiniteCyclicLine
public import Aglib.AlgebraicGeometry.EtaleCohomology.Fields.FiniteCokernel
public import Aglib.AlgebraicGeometry.EtaleCohomology.Fields.FiberCokernel
public import Aglib.AlgebraicGeometry.EtaleCohomology.Fields.FiniteEtaleTransfer.Injectivity
public import Aglib.AlgebraicGeometry.EtaleCohomology.Fields.SeparablyClosedConstantH2
public import Aglib.AlgebraicGeometry.EtaleCohomology.H0.FiberZero
public import Aglib.AlgebraicGeometry.EtaleCohomology.H0.ConstantFiber
public import Aglib.AlgebraicGeometry.EtaleCohomology.GeometricPoints.InverseImage
public import Aglib.CategoryTheory.Sites.SheafCohomology.Vanishing.ExactSequence

/-! # Original degree-two cohomology of finite prime-torsion local systems

Strong induction on the actual finite geometric fibre combines genuine
prime-to-p Sylow restriction, an actual constant cyclic subobject, the
literal finite locally constant cokernel, and original restriction-trace
injectivity. The same separably closed ambient field is retained throughout.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian AlgebraicGeometry
open Scheme.FiniteEtale.FieldGalois.OverRing

namespace AlgebraicGeometry.Scheme.EtaleCohomology.Fields

universe u w

attribute [local instance] hasSheafifyLarge hasExtStandard

variable (K : Type u) [Field K] [IsSepClosed K]
  (p : ℕ) [Fact p.Prime] (hK : IsUnit (p : Γ(Spec (.of K), ⊤)))

include hK

private theorem finiteH2_cardinal_induction (N : ℕ) :
    ∀ (E Ω : Type u) [Field E] [Field Ω] [Algebra E Ω]
      [IsGalois E Ω] [IsSepClosed Ω]
      [Algebra (RatFunc K) E] [Algebra.IsAlgebraic (RatFunc K) E]
      (F : AbelianSheaf.{u, u + 1} (Spec (.of E))),
      IsFiniteLocallyConstant F → KilledBy p F →
      Nat.card (coefficientFiber (basePoint E Ω) F) = N →
      Subsingleton (Sheaf.H.{u + 2} F 2) := by
  classical
  induction N using Nat.strong_induction_on with
  | h N ih =>
    intro E Ω _ _ _ _ _ _ _ F hF hp hcard
    let s := basePoint E Ω
    let R := CoefficientRepresentation.ofFiniteLocallyConstant F (stacks03RV _) hF
    let : Finite (coefficientFiber s F) := R.fiber_finite s
    by_cases hz : Subsingleton (coefficientFiber s F)
    · let := hz
      exact Sheaf.subsingleton_H_of_isZero (R.isZero_of_subsingleton_fiber s) 2
    · let : Nontrivial (coefficientFiber s F) := not_subsingleton_iff_nontrivial.mp hz
      obtain ⟨M, hfin, hdegree, q, hq⟩ :=
        exists_primeTo_field_cyclic_mono_of_finiteLocallyConstant E Ω F hF hp
      let := hfin
      let := hq
      let f := Spec.algebraMap E M
      let C := (inverseImage f).obj F
      let Q := cokernel q
      have hC : IsFiniteLocallyConstant C := isFiniteLocallyConstant_pullback f hF
      have hpC : KilledBy p C := killedBy_pullback f hp
      have hQ : IsFiniteLocallyConstant Q :=
        isFiniteLocallyConstant_cokernel_from_constant M
          (ULift.{u} (ZMod p)) C hC q
      have hpQ : KilledBy p Q := killedBy_cokernel q p hpC
      let t := basePoint M Ω
      have e : coefficientFiber s F ≅ coefficientFiber t C := by
        have he : t ≫ f = s := basePoint_comp_algebraMap E M Ω
        exact eqToIso (congrArg
          (fun v : Spec (.of Ω) ⟶ Spec (.of E) => coefficientFiber v F) he.symm) ≪≫
            (StalkInverseImage.nativeStalkIso f t).app F
      let : Finite (coefficientFiber t C) :=
        Finite.of_equiv (coefficientFiber s F)
          (Iso.addCommGroupIsoToAddEquiv e).toEquiv
      let : Nontrivial (coefficientFiber t
          (ConstantFinite.coefficient (ULift.{u} (ZMod p)) (Spec (.of M)))) :=
        ConstantFinite.nontrivial_coefficientFiber _ t
      have hc : Nat.card (coefficientFiber t C) = N :=
        (Nat.card_congr (Iso.addCommGroupIsoToAddEquiv e).toEquiv).symm.trans hcard
      have hlt : Nat.card (coefficientFiber t Q) < N :=
        (card_coefficientFiber_cokernel_lt t q).trans_eq hc
      let : Algebra (RatFunc K) M :=
        ((algebraMap E M).comp (algebraMap (RatFunc K) E)).toAlgebra
      let : IsScalarTower (RatFunc K) E M := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
      let : Algebra.IsAlgebraic (RatFunc K) M := Algebra.IsAlgebraic.trans _ E M
      let : Subsingleton (Sheaf.H.{u + 2} Q 2) :=
        ih _ hlt M Ω Q hQ hpQ rfl
      let : Subsingleton (Sheaf.H.{u + 2}
          (ConstantFinite.coefficient (ULift.{u} (ZMod p)) (Spec (.of M))) 2) :=
        constantH2_subsingleton_of_separablyClosed_ratFunc K M p (Fact.out : p.Prime).pos hK
      have hseq : (ShortComplex.mk q (cokernel.π q) (cokernel.condition q)).ShortExact :=
        { exact := ShortComplex.exact_cokernel q }
      let : Subsingleton (Sheaf.H.{u + 2} C 2) :=
        Sheaf.H.subsingleton_middle_of_shortExact hseq 2
      exact (finiteField_cohomologyPullback_injective E M F p hdegree hp 2).subsingleton

/-- Genuine finite locally constant prime-torsion coefficients have zero
original H2 over algebraic function fields with separably closed constants. -/
theorem finiteH2_subsingleton_of_separablyClosed_ratFunc
    (E : Type u) [Field E] [Algebra (RatFunc K) E]
    [Algebra.IsAlgebraic (RatFunc K) E]
    [HasExt.{w} (AbelianSheaf.{u, u + 1} (Spec (.of E)))]
    (F : AbelianSheaf.{u, u + 1} (Spec (.of E)))
    (hF : IsFiniteLocallyConstant F) (hp : KilledBy p F) :
    Subsingleton (Sheaf.H.{w} F 2) := by
  let : Subsingleton (Sheaf.H.{u + 2} F 2) :=
    finiteH2_cardinal_induction K p hK _ E (SeparableClosure E) F hF hp rfl
  let e : Sheaf.H.{w} F 2 ≃ Sheaf.H.{u + 2} F 2 := Ext.chgUniv
  exact e.injective.subsingleton

end AlgebraicGeometry.Scheme.EtaleCohomology.Fields
