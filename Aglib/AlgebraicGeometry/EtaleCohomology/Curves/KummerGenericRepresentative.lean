/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.Picard.KummerUnitImage
public import Aglib.AlgebraicGeometry.EtaleCohomology.Curves.KummerResidue
public import Aglib.AlgebraicGeometry.Curves.Picard.OpenBoundary
public import Aglib.AlgebraicGeometry.Curves.Picard.KummerExactness

/-! # Positive generic representatives of original curve Kummer classes

Actual divisor/Picard exactness represents the original Picard image.
Subtracting the resulting actual divisor-pair class leaves an original
positive global-unit class. Generic restriction and root multiplication then
produce a positive rational-function representative whose divisor is divisible
by the level. No root-surjectivity or extra group on pair classes is used.
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace
open AlgebraicGeometry.Scheme.Modules.Invertible
open AlgebraicGeometry.Scheme.OverField.Curve.Divisors
open AlgebraicGeometry.Scheme.OverField.Curve.Picard
open GroupCohomology.Kummer.Coefficients
open GroupCohomology.Kummer.CoefficientBaseChange
open GroupCohomology.Kummer.Torsor

namespace AlgebraicGeometry.Scheme.EtaleCohomology.Curves.KummerGenericRepresentative

universe u w w'

variable (X : Scheme.{u}) [IsIntegral X] [IsNoetherian X]

omit [IsNoetherian X] in
/-- The actual generic germ of a global unit, in original Gamma-Spec coordinates,
is the literal pulled-back unit. -/
theorem genericUnit_coordinate (a : Additive Γ(X, ⊤)ˣ) :
    (Kummer.ringGlobalUnitsEquiv X.functionField (KummerPairs.globalUnitMap X a)).toMul =
      GroupCohomology.Kummer.RootNaturality.pulledUnit
        (X.fromSpecStalk (genericPoint X)) a.toMul := by
  let : Nonempty (⊤ : X.Opens) := ⟨⟨genericPoint X, trivial⟩⟩
  have hg : (X.fromSpecStalk (genericPoint X)).appTop ≫
      (Scheme.ΓSpecIso X.functionField).hom = X.germToFunctionField ⊤ := by
    change (X.fromSpecStalk (genericPoint X)).appTop ≫
      (Scheme.ΓSpecIso X.functionField).hom = X.presheaf.germ ⊤ (genericPoint X) trivial
    rw [Scheme.fromSpecStalk_appTop]
    simp
  have hg' : X.germToFunctionField ⊤ ≫ (Scheme.ΓSpecIso X.functionField).inv =
      (X.fromSpecStalk (genericPoint X)).appTop := by
    rw [← hg, Category.assoc, Iso.hom_inv_id, Category.comp_id]
  apply Units.ext
  exact ConcreteCategory.congr_hom hg' (a.toMul : Γ(X, ⊤))

variable [∀ x : ClosedPoint X, IsDiscreteValuationRing (X.presheaf.stalk x.val)]
  [HasExt.{w} (AbelianSheaf.{u, u + 1} X)]
  (hdim : topologicalKrullDim X ≤ 1)
  (n : ℕ) (hn : 0 < n) (hinv : IsUnit (n : Γ(X, ⊤)))

/-- Every original H1 class is an actual divisor-pair class plus a genuine
positive global-unit root class, without taking roots of global units. -/
theorem exists_divisorPair_add_rootClass (c : H1Etale X (mu X n)) :
    ∃ (p : KummerPairs.pairs X n) (a : Γ(X, ⊤)ˣ),
      c = torsorExtClass (TrivializedPowerTorsor.torsor EtaleDescent.etaleLineBundleDescent
          X n hn hinv (TrivializedPower.ofDivisorPair X hdim n p)) +
        rootClass GroupCohomology.Kummer.RootCover.etalePowerSurjectivity X n hn hinv a := by
  obtain ⟨D, hD⟩ := DivisorClass.divisorToPicard_surjective X hdim
    (Picard.kummerPicardMap X n c)
  have hprincipal : n • D ∈ (principal X).range := by
    rw [← DivisorClass.divisorToPicard_ker X hdim]
    change DivisorClass.divisorToPicard X hdim (n • D) = 0
    rw [map_nsmul, hD]
    exact Picard.nsmul_kummerPicardMap X n hn hinv c
  obtain ⟨f, hf⟩ := hprincipal
  let p : KummerPairs.pairs X n := ⟨(D, f), hf⟩
  let c₀ := torsorExtClass (TrivializedPowerTorsor.torsor EtaleDescent.etaleLineBundleDescent
    X n hn hinv (TrivializedPower.ofDivisorPair X hdim n p))
  have h₀ : Picard.kummerPicardMap X n c₀ = Picard.kummerPicardMap X n c :=
    (Picard.kummerPicardMap_powerPair X n hn hinv
      (TrivializedPower.ofDivisorPair X hdim n p)).trans hD
  have hu : c - c₀ ∈ (rootClassHom
      GroupCohomology.Kummer.RootCover.etalePowerSurjectivity X n hn hinv).range := by
    rw [Picard.rootClassHom_range_eq_kummerPicardMap_ker]
    change Picard.kummerPicardMap X n (c - c₀) = 0
    rw [map_sub, h₀, sub_self]
  obtain ⟨a, ha⟩ := hu
  refine ⟨p, a.toMul, ?_⟩
  exact (sub_eq_iff_eq_add.mp ha.symm).trans (add_comm _ _)

variable [HasExt.{w'} (AbelianSheaf.{u, u + 1} (Spec X.functionField))]

include hdim in
/-- Every original generic restriction is a positive rational root class,
with an actual principal divisor divisible by the level on the source. -/
theorem exists_positive_generic_representative (c : H1Etale X (mu X n)) :
    ∃ (f : X.functionFieldˣ) (D : Divisor X),
      principal X (Additive.ofMul f) = n • D ∧
        h1Map (X.fromSpecStalk (genericPoint X)) n hn hinv c =
          rootClass GroupCohomology.Kummer.RootCover.etalePowerSurjectivity
            (Spec X.functionField) n hn
            (levelInvertible (X.fromSpecStalk (genericPoint X)) n hinv)
            ((Kummer.ringGlobalUnitsEquiv X.functionField (Additive.ofMul f)).toMul) := by
  obtain ⟨p, a, rfl⟩ := exists_divisorPair_add_rootClass X hdim n hn hinv c
  let b := p.val.2 + KummerPairs.globalUnitMap X (Additive.ofMul a)
  refine ⟨b.toMul, p.val.1, ?_, ?_⟩
  · exact ((principal X).map_add _ _).trans
      (by rw [p.property, KummerPairs.globalUnitMap_principal, add_zero])
  · have hb : (Kummer.ringGlobalUnitsEquiv X.functionField b).toMul =
        (Kummer.ringGlobalUnitsEquiv X.functionField p.val.2).toMul *
          GroupCohomology.Kummer.RootNaturality.pulledUnit
            (X.fromSpecStalk (genericPoint X)) a := by
      exact (congrArg Additive.toMul
        ((Kummer.ringGlobalUnitsEquiv X.functionField).map_add p.val.2
          (KummerPairs.globalUnitMap X (Additive.ofMul a)))).trans
            (congrArg (fun z => (Kummer.ringGlobalUnitsEquiv X.functionField p.val.2).toMul * z)
              (genericUnit_coordinate X (Additive.ofMul a)))
    refine ((h1Map (X.fromSpecStalk (genericPoint X)) n hn hinv).map_add _ _).trans ?_
    refine (congrArg₂ (· + ·)
      (KummerResidue.genericPullback_divisorPair n hn hinv hdim p)
      (GroupCohomology.Kummer.RootNaturality.rootClass_pullback
        (X.fromSpecStalk (genericPoint X)) n hn hinv a)).trans ?_
    exact (rootClass_mul GroupCohomology.Kummer.RootCover.etalePowerSurjectivity
      (Spec X.functionField) n hn
      (levelInvertible (X.fromSpecStalk (genericPoint X)) n hinv) _ _).symm.trans
        (congrArg (rootClass GroupCohomology.Kummer.RootCover.etalePowerSurjectivity
          (Spec X.functionField) n hn
          (levelInvertible (X.fromSpecStalk (genericPoint X)) n hinv)) hb.symm)

end AlgebraicGeometry.Scheme.EtaleCohomology.Curves.KummerGenericRepresentative
