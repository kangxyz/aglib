/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Curves.Abel.BoundedFamily.TorsionLocus.Fibres
public import Aglib.AlgebraicGeometry.IdealSheaf.Closed.ReducedFactor
public import Aglib.AlgebraicGeometry.RationalPoint.ResidueFactor

/-! # Actual torsion parameters in the reduced closed locus

The rational section's original residue-field isomorphism compares its actual
family fibre with the intrinsic residue-field fibre. Actual power triviality
therefore proves membership in the native H0 support. The native reduced-source
factorization then lifts the original parameter into the actual closed locus.

For positive n, every actual n-torsion line bundle has degree zero by the
original degree homomorphism and is realized by a genus-sized lifted parameter.
There is no torsion-finiteness or proper-base-change assertion.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry.Scheme
open AlgebraicGeometry.Scheme.Modules.Invertible
open AlgebraicGeometry.Scheme.OverField.Curve.Divisors

universe u

namespace AlgebraicGeometry.Scheme.OverField.Curve.Abel.BoundedFamily

variable {k : Type u} [Field k] (X : FScheme k)
  [SmoothOfRelativeDimension 1 X.hom] [IsProper X.hom]
  (o : Spec (.of k) ⟶ X.left) (ho : o ≫ X.hom = 𝟙 _) (hX : Properties X)

include hX

/-- A power-trivial rational family fibre lies on the actual H0 support. The
comparison with the intrinsic residue fibre is an actual scheme isomorphism. -/
theorem mem_powerNonvanishingSupport_of_rational_power_trivial (g n : ℕ)
    (a : Spec (.of k) ⟶ (parameter X.hom g).left)
    (ha : a ≫ (parameter X.hom g).hom = 𝟙 _)
    (hτ : Nonempty ((pullbackLineBundle
      (Hom.familyMap X.hom (parameter X.hom g).hom (𝟙 _) a ha)
      (powerLineBundle X.hom o ho g n)).val ≅
        SheafOfModules.unit (pullback X.hom (𝟙 (Spec (.of k)))).ringCatSheaf)) :
    a (IsLocalRing.closedPoint k) ∈ powerNonvanishingSupport X.hom o ho g n := by
  let q : Scheme.RationalPoint k (parameter X.hom g).left :=
    ⟨(parameter X.hom g).hom, a, ha⟩
  let ρ := q.residueSpecIso
  let b := (parameter X.hom g).left.fromSpecResidueField q.point
  let t := b ≫ (parameter X.hom g).hom
  have hρb : ρ.hom ≫ b = a := q.residueSpecIso_hom_fromSpecResidueField
  have hρ : ρ.hom ≫ t = 𝟙 _ := by
    rw [← Category.assoc, hρb, ha]
  let m := Hom.familyMap X.hom t (𝟙 _) ρ.hom hρ
  let i := Hom.familyMap X.hom (parameter X.hom g).hom t b rfl
  let r := Hom.familyMap X.hom (parameter X.hom g).hom (𝟙 _) a ha
  have hmi : m ≫ i = r := by
    simpa only [hρb] using
      (Hom.familyMap_comp X.hom (parameter X.hom g).hom t (𝟙 _) b ρ.hom rfl hρ)
  let : IsIso m := (Hom.familyMap_isPullback X.hom t (𝟙 _) ρ.hom hρ).isIso_fst_of_isIso
  let : (Modules.pullback m).IsEquivalence := Modules.pullback_isEquivalence_of_isIso m
  let M := (powerLineBundle X.hom o ho g n).val
  let C : (Modules.pullback m).obj (powerPointFibreLineBundle X o ho g n q.point).val ≅
      (Modules.pullback r).obj M :=
    (Modules.pullbackComp m i).app M ≪≫ (Modules.pullbackCongr hmi).app M
  obtain ⟨τ⟩ := hτ
  apply (mem_powerNonvanishingSupport_iff_fibre_trivial X o ho hX g n q.point).mpr
  exact ⟨(Modules.pullback m).preimageIso
    (C ≪≫ τ ≪≫ (Modules.pullbackUnitIso m).symm)⟩

/-- Actual support containment for the entire original rational parameter map. -/
theorem range_rationalParameter_subset_powerNonvanishing (g n : ℕ)
    (a : Spec (.of k) ⟶ (parameter X.hom g).left)
    (ha : a ≫ (parameter X.hom g).hom = 𝟙 _)
    (hτ : Nonempty ((pullbackLineBundle
      (Hom.familyMap X.hom (parameter X.hom g).hom (𝟙 _) a ha)
      (powerLineBundle X.hom o ho g n)).val ≅
        SheafOfModules.unit (pullback X.hom (𝟙 (Spec (.of k)))).ringCatSheaf)) :
    Set.range a ⊆ Set.range (powerNonvanishingι X.hom o ho g n) := by
  rw [range_powerNonvanishingι]
  rintro _ ⟨s, rfl⟩
  have hs : s = IsLocalRing.closedPoint k := Subsingleton.elim _ _
  subst s
  exact mem_powerNonvanishingSupport_of_rational_power_trivial X o ho hX g n a ha hτ

/-- The canonical reduced-source factorization of the original parameter map
through the actual reduced closed power locus. -/
def liftPowerTrivialParameter (g n : ℕ)
    (a : Spec (.of k) ⟶ (parameter X.hom g).left)
    (ha : a ≫ (parameter X.hom g).hom = 𝟙 _)
    (hτ : Nonempty ((pullbackLineBundle
      (Hom.familyMap X.hom (parameter X.hom g).hom (𝟙 _) a ha)
      (powerLineBundle X.hom o ho g n)).val ≅
        SheafOfModules.unit (pullback X.hom (𝟙 (Spec (.of k)))).ringCatSheaf)) :
    Spec (.of k) ⟶ powerNonvanishingLocus X.hom o ho g n :=
  liftReducedToClosed (powerNonvanishingι X.hom o ho g n) a
    (range_rationalParameter_subset_powerNonvanishing X o ho hX g n a ha hτ)

/-- The lift preserves the literal original parameter, not just its image point. -/
@[reassoc (attr := simp)]
theorem liftPowerTrivialParameter_fac (g n : ℕ)
    (a : Spec (.of k) ⟶ (parameter X.hom g).left)
    (ha : a ≫ (parameter X.hom g).hom = 𝟙 _)
    (hτ : Nonempty ((pullbackLineBundle
      (Hom.familyMap X.hom (parameter X.hom g).hom (𝟙 _) a ha)
      (powerLineBundle X.hom o ho g n)).val ≅
        SheafOfModules.unit (pullback X.hom (𝟙 (Spec (.of k)))).ringCatSheaf)) :
    liftPowerTrivialParameter X o ho hX g n a ha hτ ≫
      powerNonvanishingι X.hom o ho g n = a :=
  liftReducedToClosed_fac _ _ _

variable [IsAlgClosed k]

/-- Every actual power-trivial line bundle has an actual genus-sized rational
parameter in the reduced closed locus. Positive n supplies degree zero rather
than retaining an independent degree-zero premise. -/
theorem exists_powerLocus_parameter_lineBundle_iso (L : LineBundle X.left)
    (n : ℕ) (hn : 0 < n)
    (τ : (tensorPowerLineBundle X.left L n).val ≅ SheafOfModules.unit X.left.ringCatSheaf) :
    ∃ z : Spec (.of k) ⟶
        powerNonvanishingLocus X.hom o ho (coherentGenus k X) n,
      ∃ hz : (z ≫ powerNonvanishingι X.hom o ho (coherentGenus k X) n) ≫
          (parameter X.hom (coherentGenus k X)).hom = 𝟙 _,
        Nonempty ((pullbackLineBundle (pullback.fst X.hom (𝟙 (Spec (.of k)))) L).val ≅
          (pullbackLineBundle (Hom.familyMap X.hom
            (parameter X.hom (coherentGenus k X)).hom (𝟙 _)
            (z ≫ powerNonvanishingι X.hom o ho (coherentGenus k X) n) hz)
            (lineBundle X.hom o ho (coherentGenus k X))).val) := by
  let : IsIntegral X.left := PointDivisor.isIntegral_of_properties X hX
  let : IsNoetherian X.left := curveProperties_isNoetherian hX
  let (x : ClosedPoint X.left) := PointDivisor.isDiscreteValuationRing_stalk X hX x
  have hdim := curveProperties_dimension smoothFieldDimension hX
  have hdeg := Picard.Degree.picard_torsion_degree_zero X.left X.hom hdim.le
    (Picard.Degree.properCurveProductFormula k X.left X.hom hdim) n hn (classOf X.left L)
    (TrivializedPower.pair_class_nsmul X.left ⟨L, τ⟩)
  obtain ⟨a, ha, ⟨e⟩⟩ := exists_parameter_lineBundle_iso X hX hdim o ho L hdeg
  let g := coherentGenus k X
  let f := pullback.fst X.hom (𝟙 (Spec (.of k)))
  let r := Hom.familyMap X.hom (parameter X.hom g).hom (𝟙 _) a ha
  let d : (tensorPowerLineBundle _ (pullbackLineBundle f L) n).val ≅
      SheafOfModules.unit (pullback X.hom (𝟙 (Spec (.of k)))).ringCatSheaf :=
    (PowerPullback.pullbackPowerIso f L n).symm ≪≫
      (Modules.pullback f).mapIso τ ≪≫ Modules.pullbackUnitIso f
  have hτ : Nonempty ((pullbackLineBundle r (powerLineBundle X.hom o ho g n)).val ≅
      SheafOfModules.unit (pullback X.hom (𝟙 (Spec (.of k)))).ringCatSheaf) :=
    ⟨PowerPullback.pullbackPowerIso r (lineBundle X.hom o ho g) n ≪≫
      (TrivializedPower.powerIso _ e n).symm ≪≫ d⟩
  let z := liftPowerTrivialParameter X o ho hX g n a ha hτ
  have hza : z ≫ powerNonvanishingι X.hom o ho g n = a :=
    liftPowerTrivialParameter_fac X o ho hX g n a ha hτ
  have hz : (z ≫ powerNonvanishingι X.hom o ho g n) ≫ (parameter X.hom g).hom = 𝟙 _ := by
    rw [hza, ha]
  refine ⟨z, hz, ?_⟩
  have hr : Hom.familyMap X.hom (parameter X.hom g).hom (𝟙 _)
      (z ≫ powerNonvanishingι X.hom o ho g n) hz = r := by
    apply pullback.hom_ext
    · exact (Hom.familyMap_fst _ _ _ _ _).trans (Hom.familyMap_fst _ _ _ _ _).symm
    · exact (Hom.familyMap_snd _ _ _ _ _).trans
        ((congrArg (fun b => pullback.snd X.hom (𝟙 (Spec (.of k))) ≫ b) hza).trans
          (Hom.familyMap_snd _ _ _ _ _).symm)
  exact ⟨e ≪≫ ((Modules.pullbackCongr hr).app (lineBundle X.hom o ho g).val).symm⟩

/-- The actual ordinary Picard n-torsion hypothesis also gives the same
scheme-valued parameter, with degree zero and power triviality both derived. -/
theorem exists_powerLocus_parameter_of_class_nsmul_eq_zero (L : LineBundle X.left)
    (n : ℕ) (hn : 0 < n) (hL : n • classOf X.left L = 0) :
    ∃ z : Spec (.of k) ⟶
        powerNonvanishingLocus X.hom o ho (coherentGenus k X) n,
      ∃ hz : (z ≫ powerNonvanishingι X.hom o ho (coherentGenus k X) n) ≫
          (parameter X.hom (coherentGenus k X)).hom = 𝟙 _,
        Nonempty ((pullbackLineBundle (pullback.fst X.hom (𝟙 (Spec (.of k)))) L).val ≅
          (pullbackLineBundle (Hom.familyMap X.hom
            (parameter X.hom (coherentGenus k X)).hom (𝟙 _)
            (z ≫ powerNonvanishingι X.hom o ho (coherentGenus k X) n) hz)
            (lineBundle X.hom o ho (coherentGenus k X))).val) := by
  have hc : classOf X.left (tensorPowerLineBundle X.left L n) =
      classOf X.left (trivialLineBundle X.left) := by
    rw [classOf_tensorPower, hL, classOf_trivial]
  obtain ⟨e⟩ := (class_eq_iff _ _ _).mp hc
  exact exists_powerLocus_parameter_lineBundle_iso X o ho hX L n hn
    (e ≪≫ PowerPullback.freeUnitIso X.left)

end AlgebraicGeometry.Scheme.OverField.Curve.Abel.BoundedFamily
