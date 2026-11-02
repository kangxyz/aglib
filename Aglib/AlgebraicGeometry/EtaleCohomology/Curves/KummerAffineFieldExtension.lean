/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.Curves.KummerBoundaryObstruction
public import Aglib.AlgebraicGeometry.EtaleCohomology.Curves.KummerResidueExtension
public import Aglib.AlgebraicGeometry.EtaleCohomology.Curves.KummerResidueNaturality
public import Aglib.AlgebraicGeometry.Limits.Range

/-! # Original affine-curve Kummer field comparison

The construction uses the actual rational boundary obstruction, positive
rational generic representatives and original root pullbacks. In particular,
the correction on the open is a divisor-pair class, not a presumed root of a
global unit. All intermediate divisors are native finitely supported functions.
-/

@[expose] public noncomputable section

open CategoryTheory Limits AlgebraicGeometry TopologicalSpace
open AlgebraicGeometry.Scheme.Modules.Invertible
open AlgebraicGeometry.Scheme.OverField.Curve.Divisors
open AlgebraicGeometry.Scheme.OverField.Curve.Picard
open GroupCohomology.Kummer.Coefficients
open GroupCohomology.Kummer.CoefficientBaseChange
open GroupCohomology.Kummer.Torsor

universe u wU wKU

namespace AlgebraicGeometry.Scheme.EtaleCohomology.Curves.KummerAffineFieldExtension

section BoundaryRepresentative

variable {U Y : Scheme.{u}} [IsIntegral U] [IsIntegral Y]
  [IsNoetherian U] [IsNoetherian Y] [JacobsonSpace Y]
  [∀ x : ClosedPoint U, IsDiscreteValuationRing (U.presheaf.stalk x.val)]
  [∀ y : ClosedPoint Y, IsDiscreteValuationRing (Y.presheaf.stalk y.val)]
  (j : U ⟶ Y) [IsOpenImmersion j]
  [HasExt.{wU} (AbelianSheaf.{u, u + 1} U)]
  [HasExt.{wKU} (AbelianSheaf.{u, u + 1} (Spec U.functionField))]
  (hdim : topologicalKrullDim Y ≤ 1)
  (n : ℕ) (hn : 0 < n) (hinv : IsUnit (n : Γ(U, ⊤)))

local instance : IsDominant j := Scheme.isDominant_of_isOpenImmersion j

/-- Every original open H1 class determines an actual rational function and a
boundary divisor whose Picard class is n-divisible. The boundary coefficients
are precisely the original local orders, not chosen residue lifts. -/
theorem exists_boundary_representative (c : H1Etale U (mu U n)) :
    ∃ (f : Y.functionFieldˣ) (B : Divisor Y),
      (∀ y ∈ B.support, y.val ∉ Set.range j) ∧
      (∃ L : PicardGroup Y, n • L = DivisorClass.divisorToPicard Y hdim B) ∧
      (∀ y : ClosedPoint Y, y.val ∉ Set.range j → B y = Y.ord (f : Y.functionField) y.val) ∧
      h1Map (U.fromSpecStalk (genericPoint U)) n hn hinv c =
        rootClass GroupCohomology.Kummer.RootCover.etalePowerSurjectivity
          (Spec U.functionField) n hn
          (levelInvertible (U.fromSpecStalk (genericPoint U)) n hinv)
          ((Kummer.ringGlobalUnitsEquiv U.functionField
            (Additive.ofMul (Scheme.functionFieldUnitMap j f))).toMul) := by
  obtain ⟨g, D, hD, hg⟩ := KummerGenericRepresentative.exists_positive_generic_representative
    U (DivisorClass.openSource_dimension_le_one j hdim) n hn hinv c
  let f := (Units.mapEquiv (Scheme.FunctionField.fieldEquiv j).toMulEquiv).symm g
  have hf : Scheme.functionFieldUnitMap j f = g :=
    (Units.mapEquiv (Scheme.FunctionField.fieldEquiv j).toMulEquiv).apply_symm_apply g
  let E := openExtension j D
  let B := principal Y (Additive.ofMul f) - n • E
  have hrestrict : openRestriction j B = 0 := by
    change openRestriction j (principal Y (Additive.ofMul f) - n • openExtension j D) = 0
    rw [map_sub, map_nsmul, openRestriction_principal, hf,
      openRestriction_openExtension, hD, sub_self]
  refine ⟨f, B, (openRestriction_eq_zero_iff j B).mp hrestrict, ?_, ?_, ?_⟩
  · refine ⟨-DivisorClass.divisorToPicard Y hdim E, ?_⟩
    change n • (-DivisorClass.divisorToPicard Y hdim E) =
      DivisorClass.divisorToPicard Y hdim (principal Y (Additive.ofMul f) - n • E)
    rw [map_sub, DivisorClass.divisorToPicard_principal, map_nsmul, zero_sub, smul_neg]
  · intro y hy
    change (principal Y (Additive.ofMul f) - n • openExtension j D) y = _
    rw [Finsupp.sub_apply, Finsupp.smul_apply, openExtension_apply_of_not_mem_range j D y hy]
    simp only [smul_zero, sub_zero]
    rfl
  · rw [hf]
    exact hg

include hdim in
/-- A rational function whose original principal divisor is a boundary minus
n times a divisor constructs an actual open H1 correction with those residues. -/
theorem exists_class_with_boundary_residues (B D : Divisor Y) (f : Y.functionFieldˣ)
    (hB : ∀ y ∈ B.support, y.val ∉ Set.range j)
    (hf : principal Y (Additive.ofMul f) = B - n • D) :
    ∃ c : H1Etale U (mu U n), ∀ y : ClosedPoint Y,
      KummerResidue.residue j n hn hinv y c = (B y : ZMod n) := by
  have hzero := (openRestriction_eq_zero_iff j B).mpr hB
  have hpair : principal U (Additive.ofMul (Scheme.functionFieldUnitMap j f)) =
      n • (-openRestriction j D) := by
    have h := congrArg (openRestriction j) hf
    rw [openRestriction_principal, map_sub, map_nsmul, hzero, zero_sub, ← smul_neg] at h
    exact h
  let P : KummerPairs.pairs U n :=
    ⟨(-openRestriction j D, Additive.ofMul (Scheme.functionFieldUnitMap j f)), hpair⟩
  let c := torsorExtClass (TrivializedPowerTorsor.torsor EtaleDescent.etaleLineBundleDescent
    U n hn hinv (TrivializedPower.ofDivisorPair U
      (DivisorClass.openSource_dimension_le_one j hdim) n P))
  refine ⟨c, fun y => ?_⟩
  have hv := KummerResidue.residue_divisorPair j n hn hinv
    (DivisorClass.openSource_dimension_le_one j hdim) y P
  have ho := KummerResidueExtension.boundaryOrder_functionFieldUnitMap j y f
  have he := DFunLike.congr_fun hf y
  have hval : KummerResidue.boundaryOrder j y P.val.2 = B y - n • D y :=
    ho.trans he
  refine hv.trans (congrArg (fun z : ℤ => (z : ZMod n)) hval |>.trans ?_)
  change (Int.castAddHom (ZMod n)) (B y - n • D y) = _
  rw [map_sub, map_nsmul, nsmul_eq_mul, ZMod.natCast_self, zero_mul, sub_zero]
  rfl

end BoundaryRepresentative

section FieldComparison

attribute [local instance] hasSheafifyLarge HasExt.standard

variable (k K : Type u) [Field k] [IsAlgClosed k] [Field K] [IsAlgClosed K] [Algebra k K]
  (X : OverField.FScheme k) [IsIntegral X.left] [IsNoetherian X.left]
  [IsProper X.hom] [SmoothOfRelativeDimension 1 X.hom] [JacobsonSpace X.left]
  [∀ x : ClosedPoint X.left, IsDiscreteValuationRing (X.left.presheaf.stalk x.val)]
  [IsIntegral (pullback X.hom (Spec.algebraMap k K))]
  [IsNoetherian (pullback X.hom (Spec.algebraMap k K))]
  [JacobsonSpace (show Scheme from pullback X.hom (Spec.algebraMap k K))]
  [∀ y : ClosedPoint (pullback X.hom (Spec.algebraMap k K)),
    IsDiscreteValuationRing
      ((pullback X.hom (Spec.algebraMap k K)).presheaf.stalk y.val)]
  {U U' : Scheme.{u}} [IsIntegral U] [IsNoetherian U]
  [∀ x : ClosedPoint U, IsDiscreteValuationRing (U.presheaf.stalk x.val)]
  [IsIntegral U'] [IsNoetherian U']
  [∀ y : ClosedPoint U', IsDiscreteValuationRing (U'.presheaf.stalk y.val)]
  [∀ y : U', IsIntegrallyClosed (U'.presheaf.stalk y)]
  (j : U ⟶ X.left) [IsOpenImmersion j]
  (j' : U' ⟶ pullback X.hom (Spec.algebraMap k K)) [IsOpenImmersion j']
  (a : U' ⟶ U)
  (H : IsPullback a j' j (pullback.fst X.hom (Spec.algebraMap k K)))
  (hN : Scheme.NormalStalks X.left) (hdim : topologicalKrullDim X.left = 1)
  (hdim' : topologicalKrullDim
    (show Scheme from pullback X.hom (Spec.algebraMap k K)) ≤ 1)
  (n : ℕ) (hn : 0 < n) (hk : IsUnit (n : Γ(Spec (.of k), ⊤)))

include H hN hdim hdim' in
/-- The original roots H1 pullback is surjective in a cartesian open square
of a smooth proper curve over algebraically closed fields. Boundary geometry
uses the source algebraic closure; proper H1 surjectivity uses the target
algebraic closure. No power-surjectivity of affine units is assumed. -/
theorem h1Map_surjective_cartesian_open :
    Function.Surjective (h1Map.{u, u + 2, u + 2} a n hn
      (levelInvertible j n (levelInvertible X.hom n hk))) := by
  let Y := pullback X.hom (Spec.algebraMap k K)
  let b : Y ⟶ X.left := pullback.fst X.hom (Spec.algebraMap k K)
  let hinv := levelInvertible X.hom n hk
  let : IsDominant j := Scheme.isDominant_of_isOpenImmersion j
  let : IsDominant j' := Scheme.isDominant_of_isOpenImmersion j'
  let : Surjective (Spec.algebraMap k K) :=
    ⟨fun x => ⟨IsLocalRing.closedPoint K, Subsingleton.elim _ _⟩⟩
  let : Surjective b := inferInstanceAs
    (Surjective (pullback.fst X.hom (Spec.algebraMap k K)))
  let : Surjective a := MorphismProperty.of_isPullback H.flip inferInstance
  let O := j.opensRange
  let : Nonempty O := ⟨⟨j (genericPoint U), ⟨genericPoint U, rfl⟩⟩⟩
  have hrange : Set.range j' = b ⁻¹' Set.range j :=
    Scheme.Pullback.Fibre.pullback_range_snd H
  intro c
  obtain ⟨g, B, hB, hdiv, hcoeff, hgen⟩ := exists_boundary_representative
    j' hdim' n hn (levelInvertible a n (levelInvertible j n hinv)) c
  have hBout : ∀ y ∈ B.support, y.val ∉ b ⁻¹ᵁ O := by
    intro y hy hyO
    exact hB y hy (hrange.symm ▸ hyO)
  obtain ⟨f, D, hf⟩ := exists_principal_congruent_boundary
    k K X hN hdim hdim' n hn hk O B hBout hdiv
  let B₀ := fieldRestriction X.hom (Spec.algebraMap k K) B
  have hB₀ : ∀ x ∈ B₀.support, x.val ∉ Set.range j := by
    intro x hx hxj
    have hzero : B (ClosedPoint.fieldExtensionPoint X.hom (Spec.algebraMap k K) x) = 0 := by
      by_contra hne
      apply hBout _ (Finsupp.mem_support_iff.mpr hne)
      change b (ClosedPoint.fieldExtensionPoint X.hom (Spec.algebraMap k K) x).val ∈ O
      rw [ClosedPoint.fieldExtensionPoint_fst]
      exact hxj
    exact (Finsupp.mem_support_iff.mp hx) hzero
  obtain ⟨c₀, hc₀⟩ := exists_class_with_boundary_residues
    j hdim.le n hn (levelInvertible j n hinv) B₀ D f hB₀ hf
  have hmatch (y : ClosedPoint Y) (hy : y.val ∉ Set.range j') :
      KummerResidue.residue j' n hn (levelInvertible a n (levelInvertible j n hinv)) y
        (h1Map a n hn (levelInvertible j n hinv) c₀) =
      KummerResidue.residue j' n hn (levelInvertible a n (levelInvertible j n hinv)) y c := by
    have hyO : y.val ∉ b ⁻¹ᵁ O := fun h => hy (hrange.symm ▸ h)
    obtain ⟨x, rfl⟩ := ClosedPoint.mem_range_fieldExtensionPoint_of_not_mem_preimage
      X.hom (Spec.algebraMap k K) hdim.le O y hyO
    let r := ClosedPoint.rationalPoint X.hom x
    have hnat := KummerResidueNaturality.residue_h1Map
      j j' a b H.w r (r.baseChange (Spec.algebraMap k K))
      (Spec.algebraMap k K) (r.baseChange_isPullback (Spec.algebraMap k K))
      n hn (levelInvertible j n hinv)
      (DivisorClass.openSource_dimension_le_one j hdim.le) c₀
    have hx : (⟨r.point, r.point_isClosed⟩ : ClosedPoint X.left) = x :=
      Subtype.ext (ClosedPoint.rationalPoint_point X.hom x)
    rw [hx] at hnat
    have ht := (congrArg (KummerResidue.fieldResidue j' n hn
      (levelInvertible (U'.fromSpecStalk (genericPoint U')) n
        (levelInvertible a n (levelInvertible j n hinv)))
      (ClosedPoint.fieldExtensionPoint X.hom (Spec.algebraMap k K) x)) hgen).trans
        (KummerResidue.fieldResidue_rootClass j' n hn
          (levelInvertible (U'.fromSpecStalk (genericPoint U')) n
            (levelInvertible a n (levelInvertible j n hinv)))
          (ClosedPoint.fieldExtensionPoint X.hom (Spec.algebraMap k K) x)
          (Additive.ofMul (Scheme.functionFieldUnitMap j' g)))
    have ho := KummerResidueExtension.boundaryOrder_functionFieldUnitMap j'
      (ClosedPoint.fieldExtensionPoint X.hom (Spec.algebraMap k K) x) g
    have hb := hcoeff (ClosedPoint.fieldExtensionPoint X.hom (Spec.algebraMap k K) x) hy
    exact hnat.trans ((hc₀ x).trans
      ((congrArg (fun z : ℤ => (z : ZMod n)) (hb.trans ho.symm)).trans ht.symm))
  have hzero (y : ClosedPoint Y) (hy : y.val ∉ Set.range j') :
      KummerResidue.residue j' n hn (levelInvertible j' n (levelInvertible b n hinv)) y
        (c - h1Map a n hn (levelInvertible j n hinv) c₀) = 0 := by
    rw [map_sub, hmatch y hy, sub_self]
  obtain ⟨d, hd⟩ := KummerResidueExtension.exists_preimage_of_residue_eq_zero
    j' n hn (levelInvertible b n hinv) hdim'
    (c - h1Map a n hn (levelInvertible j n hinv) c₀) hzero
  have hsurj := normalProperCurve_fieldExtension_rootsPullback_surjective
    k K X hN hdim n hn hk 1
  change Function.Surjective (h1Map b n hn hinv) at hsurj
  obtain ⟨e, he⟩ := hsurj d
  refine ⟨h1Map j n hn hinv e + c₀, ?_⟩
  have hcomm := (Kummer.h1Map_comp j a n hn hinv e).symm.trans
    ((congrArg (fun t => h1Map t n hn hinv e) H.w).trans
      (Kummer.h1Map_comp b j' n hn hinv e))
  rw [map_add, hcomm, he, hd, sub_add_cancel]

include hN hdim hdim' in
/-- Literal field-extension projection on the original open curve. The
cartesian open square is supplied by the native fibre inclusion. -/
theorem h1Map_surjective_open_fieldExtension
    [IsIntegral (pullback (j ≫ X.hom) (Spec.algebraMap k K))]
    [IsNoetherian (pullback (j ≫ X.hom) (Spec.algebraMap k K))]
    [∀ y : ClosedPoint (pullback (j ≫ X.hom) (Spec.algebraMap k K)),
      IsDiscreteValuationRing
        ((pullback (j ≫ X.hom) (Spec.algebraMap k K)).presheaf.stalk y.val)]
    [∀ y : (pullback (j ≫ X.hom) (Spec.algebraMap k K) : Scheme),
      IsIntegrallyClosed
        ((pullback (j ≫ X.hom) (Spec.algebraMap k K)).presheaf.stalk y)] :
    Function.Surjective (h1Map.{u, u + 2, u + 2}
      (pullback.fst (j ≫ X.hom) (Spec.algebraMap k K)) n hn
      (levelInvertible j n (levelInvertible X.hom n hk))) := by
  let jK := Hom.fibreInclusion X.hom j (Spec.algebraMap k K)
  have HK := Hom.fibreInclusion_isPullback X.hom j (Spec.algebraMap k K)
  let : IsOpenImmersion jK := MorphismProperty.of_isPullback HK inferInstance
  exact h1Map_surjective_cartesian_open k K X j jK
    (pullback.fst (j ≫ X.hom) (Spec.algebraMap k K)) HK hN hdim hdim' n hn hk

end FieldComparison

end AlgebraicGeometry.Scheme.EtaleCohomology.Curves.KummerAffineFieldExtension
