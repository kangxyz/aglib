/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.Curves.KummerGenericRepresentative
public import Aglib.AlgebraicGeometry.EtaleCohomology.Kummer.GenericRepresentativePullback
public import Aglib.AlgebraicGeometry.EtaleCohomology.Kummer.GenericPoint
public import Aglib.AlgebraicGeometry.Curves.Divisors.OpenPrincipal

/-! # Zero original Kummer residues and actual extension

An original class on an open curve extends exactly when its original boundary
residues vanish. Positive generic representatives and the native Finsupp
range construction produce the extending divisor pair. Original generic
pullback composition and generic H1 injectivity identify its restriction.
No finite boundary, global-unit roots, residue exactness premise or alternative
pair/cohomology model is used.
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace
open AlgebraicGeometry.Scheme.Modules.Invertible
open AlgebraicGeometry.Scheme.OverField.Curve.Divisors
open AlgebraicGeometry.Scheme.OverField.Curve.Picard
open GroupCohomology.Kummer.Coefficients
open GroupCohomology.Kummer.CoefficientBaseChange
open GroupCohomology.Kummer.Torsor

namespace AlgebraicGeometry.Scheme.EtaleCohomology.Curves.KummerResidueExtension

universe u wX wU wKX wKU

variable {U X : Scheme.{u}} [IsIntegral U] [IsIntegral X]
  (j : U ⟶ X) [IsOpenImmersion j]

local instance : IsDominant j := Scheme.isDominant_of_isOpenImmersion j

/-- The original field-unit scalar coordinate commutes with the original generic field map. -/
theorem genericFieldUnit_coordinate (a : X.functionFieldˣ) :
    GroupCohomology.Kummer.RootNaturality.pulledUnit
      (Spec.map (CommRingCat.ofHom (Scheme.functionFieldMap j)))
      ((Kummer.ringGlobalUnitsEquiv X.functionField (Additive.ofMul a)).toMul) =
    (Kummer.ringGlobalUnitsEquiv U.functionField
      (Additive.ofMul (Scheme.functionFieldUnitMap j a))).toMul :=
  GroupCohomology.Kummer.Torsor.genericFieldUnit_coordinate j a

variable [HasExt.{wX} (AbelianSheaf.{u, u + 1} X)]
  [HasExt.{wU} (AbelianSheaf.{u, u + 1} U)]
  [HasExt.{wKX} (AbelianSheaf.{u, u + 1} (Spec X.functionField))]
  [HasExt.{wKU} (AbelianSheaf.{u, u + 1} (Spec U.functionField))]
  (n : ℕ) (hn : 0 < n) (hinv : IsUnit (n : Γ(X, ⊤)))

/-- Original open/generic composition transports an actual positive rational root representative. -/
theorem genericPullback_open_rootRepresentative
    (c : H1Etale X (mu X n)) (a : X.functionFieldˣ)
    (ha : h1Map (X.fromSpecStalk (genericPoint X)) n hn hinv c =
      rootClass GroupCohomology.Kummer.RootCover.etalePowerSurjectivity
        (Spec X.functionField) n hn
        (levelInvertible (X.fromSpecStalk (genericPoint X)) n hinv)
        ((Kummer.ringGlobalUnitsEquiv X.functionField (Additive.ofMul a)).toMul)) :
    h1Map (U.fromSpecStalk (genericPoint U)) n hn (levelInvertible j n hinv)
        (h1Map j n hn hinv c) =
      rootClass GroupCohomology.Kummer.RootCover.etalePowerSurjectivity
        (Spec U.functionField) n hn
        (levelInvertible (U.fromSpecStalk (genericPoint U)) n (levelInvertible j n hinv))
        ((Kummer.ringGlobalUnitsEquiv U.functionField
          (Additive.ofMul (Scheme.functionFieldUnitMap j a))).toMul) :=
  GroupCohomology.Kummer.Torsor.genericPullback_rootRepresentative j n hn hinv c a ha

section Orders

variable [IsNoetherian X]

omit [HasExt.{wX} (AbelianSheaf.{u, u + 1} X)]
  [HasExt.{wU} (AbelianSheaf.{u, u + 1} U)]
  [HasExt.{wKX} (AbelianSheaf.{u, u + 1} (Spec X.functionField))]
  [HasExt.{wKU} (AbelianSheaf.{u, u + 1} (Spec U.functionField))] in
/-- The boundary order of a pulled rational unit is its original order on X. -/
theorem boundaryOrder_functionFieldUnitMap (x : ClosedPoint X) (a : X.functionFieldˣ) :
    KummerResidue.boundaryOrder j x (Additive.ofMul (Scheme.functionFieldUnitMap j a)) =
      X.ord (a : X.functionField) x.val := by
  exact congrArg (fun b : X.functionField => X.ord b x.val)
    ((Scheme.FunctionField.fieldEquiv j).symm_apply_apply (a : X.functionField))

variable [∀ x : ClosedPoint X, IsDiscreteValuationRing (X.presheaf.stalk x.val)]
  (hdim : topologicalKrullDim X ≤ 1)

include hdim in
/-- Every original restricted class has zero residues at all closed points of X. -/
theorem residue_pullback_eq_zero (c : H1Etale X (mu X n)) (x : ClosedPoint X) :
    KummerResidue.residue j n hn (levelInvertible j n hinv) x (h1Map j n hn hinv c) = 0 := by
  obtain ⟨a, D, hD, ha⟩ :=
    KummerGenericRepresentative.exists_positive_generic_representative X hdim n hn hinv c
  have hv := (congrArg (KummerResidue.fieldResidue j n hn
    (levelInvertible (U.fromSpecStalk (genericPoint U)) n (levelInvertible j n hinv)) x)
      (genericPullback_open_rootRepresentative j n hn hinv c a ha)).trans
        (KummerResidue.fieldResidue_rootClass j n hn
          (levelInvertible (U.fromSpecStalk (genericPoint U)) n (levelInvertible j n hinv)) x
          (Additive.ofMul (Scheme.functionFieldUnitMap j a)))
  refine hv.trans ?_
  have ho : KummerResidue.boundaryOrder j x
      (Additive.ofMul (Scheme.functionFieldUnitMap j a)) = n • D x :=
    (boundaryOrder_functionFieldUnitMap j x a).trans (DFunLike.congr_fun hD x)
  rw [ho]
  change (Int.castAddHom (ZMod n)) (n • D x) = 0
  rw [map_nsmul, nsmul_eq_mul, ZMod.natCast_self, zero_mul]

end Orders

section Extension

variable [IsNoetherian U] [IsNoetherian X] [JacobsonSpace X]
  [∀ x : ClosedPoint U, IsDiscreteValuationRing (U.presheaf.stalk x.val)]
  [∀ x : ClosedPoint X, IsDiscreteValuationRing (X.presheaf.stalk x.val)]
  [∀ x : U, IsIntegrallyClosed (U.presheaf.stalk x)]
  (hdim : topologicalKrullDim X ≤ 1)

include hdim in
/-- Vanishing of the actual boundary residues constructs an actual original H1 preimage. -/
theorem exists_preimage_of_residue_eq_zero (c : H1Etale U (mu U n))
    (hc : ∀ x : ClosedPoint X, x.val ∉ Set.range j →
      KummerResidue.residue j n hn (levelInvertible j n hinv) x c = 0) :
    ∃ b : H1Etale X (mu X n), h1Map j n hn hinv b = c := by
  obtain ⟨a, D, hD, ha⟩ :=
    KummerGenericRepresentative.exists_positive_generic_representative U
      (DivisorClass.openSource_dimension_le_one j hdim) n hn (levelInvertible j n hinv) c
  let f : X.functionFieldˣ := Units.mapEquiv (Scheme.FunctionField.fieldEquiv j).symm.toMulEquiv a
  have hf : Scheme.functionFieldUnitMap j f = a := by
    apply Units.ext
    exact (Scheme.FunctionField.fieldEquiv j).apply_symm_apply (a : U.functionField)
  have hdiv (x : ClosedPoint X) : (n : ℤ) ∣ principal X (Additive.ofMul f) x := by
    by_cases hx : x.val ∈ Set.range j
    · obtain ⟨y, rfl⟩ := (ClosedPoint.mem_range_openEmbedding_iff j x).mpr hx
      let : IsDiscreteValuationRing (X.presheaf.stalk (j y.val)) :=
        inferInstanceAs (IsDiscreteValuationRing
          (X.presheaf.stalk (ClosedPoint.openEmbedding j y).val))
      have ho := (order_functionFieldMap_openImmersion j y.val (f : X.functionField)).symm
      have hv := congrArg (fun z : U.functionFieldˣ => (z : U.functionField)) hf
      have hd : U.ord (a : U.functionField) y.val = n • D y :=
        DFunLike.congr_fun hD y
      refine ⟨D y, ?_⟩
      change X.ord (f : X.functionField) (j y.val) = (n : ℤ) * D y
      simpa only [nsmul_eq_mul] using
        ho.trans ((congrArg (fun z => U.ord z y.val) hv).trans hd)
    · have hv := (congrArg (KummerResidue.fieldResidue j n hn
        (levelInvertible (U.fromSpecStalk (genericPoint U)) n (levelInvertible j n hinv)) x)
          ha).trans (KummerResidue.fieldResidue_rootClass j n hn
            (levelInvertible (U.fromSpecStalk (genericPoint U)) n (levelInvertible j n hinv)) x
            (Additive.ofMul a))
      have hz : (principal X (Additive.ofMul f) x : ZMod n) = 0 := hv.symm.trans (hc x hx)
      exact (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp hz
  have hrange : principal X (Additive.ofMul f) ∈
      Set.range (Finsupp.mapRange (α := ClosedPoint X)
        (fun z : ℤ => n • z) (smul_zero n)) := by
    rw [Finsupp.range_mapRange]
    intro x
    obtain ⟨b, hb⟩ := hdiv x
    exact ⟨b, by simpa only [nsmul_eq_mul] using hb.symm⟩
  obtain ⟨E, hE⟩ := hrange
  have hprincipal : principal X (Additive.ofMul f) = n • E := by
    ext x
    exact (DFunLike.congr_fun hE x).symm
  let p : KummerPairs.pairs X n := ⟨(E, Additive.ofMul f), hprincipal⟩
  let b := torsorExtClass (TrivializedPowerTorsor.torsor EtaleDescent.etaleLineBundleDescent
    X n hn hinv (TrivializedPower.ofDivisorPair X hdim n p))
  refine ⟨b, ?_⟩
  apply h1Map_injective_genericPoint U n hn (levelInvertible j n hinv)
  refine (genericPullback_open_rootRepresentative j n hn hinv b f
    (KummerResidue.genericPullback_divisorPair n hn hinv hdim p)).trans ?_
  exact (congrArg (fun z : U.functionFieldˣ =>
    rootClass GroupCohomology.Kummer.RootCover.etalePowerSurjectivity
      (Spec U.functionField) n hn
      (levelInvertible (U.fromSpecStalk (genericPoint U)) n (levelInvertible j n hinv))
      ((Kummer.ringGlobalUnitsEquiv U.functionField (Additive.ofMul z)).toMul)) hf).trans ha.symm

include hdim in
/-- The image of the original open pullback is exactly the zero-boundary-residue classes. -/
theorem exists_preimage_iff_residue_eq_zero (c : H1Etale U (mu U n)) :
    (∃ b : H1Etale X (mu X n), h1Map j n hn hinv b = c) ↔
      ∀ x : ClosedPoint X, x.val ∉ Set.range j →
        KummerResidue.residue j n hn (levelInvertible j n hinv) x c = 0 := by
  constructor
  · rintro ⟨b, rfl⟩ x _
    exact residue_pullback_eq_zero j n hn hinv hdim b x
  · exact exists_preimage_of_residue_eq_zero j n hn hinv hdim c

end Extension

end AlgebraicGeometry.Scheme.EtaleCohomology.Curves.KummerResidueExtension
