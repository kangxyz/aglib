/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.Constructible.Modules.CohomologyVanishing
public import Aglib.AlgebraicGeometry.EtaleCohomology.Curves.PrimeToCharacteristicVanishing
public import Aglib.AlgebraicGeometry.EtaleCohomology.Kummer.HenselianConstant
public import Aglib.AlgebraicGeometry.Morphisms.Etale.StalkMap
public import Aglib.AlgebraicGeometry.Stalk.Dimension
public import Aglib.AlgebraicGeometry.EtaleCohomology.Coefficients.ModuleCohomology
public import Aglib.AlgebraicGeometry.EtaleCohomology.Exceptional.Coefficients.Underlying

/-!
# Ordinary finite-local-system vanishing on finite-type curves

The roots theorem applies directly on every actual finite étale test of the
original curve. Equality of actual étale stalk dimensions gives the same
upper dimension bound there. The original coefficient-level prime-test
criterion then gives finite-local-system vanishing and its native unit-Ext
form. No properness, smoothness or new completion is required.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

namespace AlgebraicGeometry.Scheme.EtaleCohomology.Curves

open Constructible.Modules

universe u r w w'

attribute [local instance] hasSheafifyLarge ModuleCat.Sheaf.hasSheafify
  Coefficients.hasSheafifyModules
  CategoryTheory.TorsionZMod.Ringed.abWEqualsLocallyBijectiveStandard

/-- Actual étale stalk dimensions give the same upper bound globally. -/
theorem dimension_le_one_of_etale {X Y : Scheme.{u}} [IsLocallyNoetherian X]
    (f : Y ⟶ X) [Etale f] (hdim : topologicalKrullDim X ≤ 1) :
    topologicalKrullDim Y ≤ 1 := by
  rw [Scheme.topologicalKrullDim_eq_iSup_stalk]
  apply iSup_le
  intro y
  rw [Scheme.ringKrullDim_stalk_eq_of_etale f y]
  have h := le_iSup (fun x : X => ringKrullDim (X.presheaf.stalk x)) (f y)
  rw [← Scheme.topologicalKrullDim_eq_iSup_stalk] at h
  exact h.trans hdim

section FiniteTypeCurve

variable {k : Type u} [Field k] [IsSepClosed k] (X : Scheme.{u})
  (f : X ⟶ Spec (.of k)) [LocallyOfFiniteType f] [CompactSpace X]
  (hdim : topologicalKrullDim X ≤ 1)
  [HasExt.{w} (AbelianSheaf.{u, u + 1} X)]

include f hdim

/-- Prime constants vanish directly on the original finite-type curve. -/
theorem primeField_high_subsingleton_of_finiteType_curve (p : ℕ) [Fact p.Prime]
    (hunit : IsUnit (p : k)) (q : ℕ) (hq : 2 < q) :
    Subsingleton (Sheaf.H.{w} (primeFieldSheaf X p) q) := by
  have hinv : IsUnit (p : Γ(X, ⊤)) := by
    simpa only [map_natCast] using
      hunit.map (((Scheme.ΓSpecIso (.of k)).inv ≫ f.appTop).hom)
  let : IsSepClosed (IsLocalRing.ResidueField k) :=
    Algebra.IsAlgebraic.isSepClosed (F := k) (E := IsLocalRing.ResidueField k)
  let e : ConstantFinite.coefficient (ULift.{u} (ZMod p)) X ≅
      GroupCohomology.Kummer.Coefficients.mu X p :=
    Kummer.HenselianConstant.constantRootIsoOver k p (Fact.out : p.Prime).pos
      (by simpa only [map_natCast] using hunit.map (Scheme.ΓSpecIso (.of k)).inv.hom) f
  let : Subsingleton (Sheaf.H.{w} (GroupCohomology.Kummer.Coefficients.mu X p) q) :=
    roots_subsingleton_H_of_curve k X f hdim p (Fact.out : p.Prime).pos hunit hinv q hq
  let E : Sheaf.H.{w} (primeFieldSheaf X p) q ≃+
      Sheaf.H.{w} (GroupCohomology.Kummer.Coefficients.mu X p) q :=
    ((Sheaf.functorH X.smallEtaleTopology q).mapIso
      ((cyclicPrimeFieldIso X p).symm ≪≫ e)).addCommGroupIsoToAddEquiv
  exact E.injective.subsingleton


/-- The original coefficient criterion applies to the actual finite étale
tests, whose roots cohomology vanishes directly by the curve dimension bound. -/
theorem moduleSheaf_high_subsingleton_of_finiteType_curve
    [ConnectedSpace X] (R : Type r) [CommRing R] [Finite R]
    [(forget₂ (ModuleCat.{u + 1} R) AddCommGrpCat.{u + 1}).Full]
    (n : ℕ) (hn : 0 < n) (hunit : IsUnit (n : k)) (q : ℕ) (hq : 2 < q)
    (F : ModuleSheaf R X) (hF : IsFiniteTypeLocallyConstant F) (hkill : n • 𝟙 F = 0) :
    Subsingleton ((ModuleCat.Sheaf.cohomology X.smallEtaleTopology R q).obj F) := by
  let : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian f
  let : IsNoetherian X := ⟨⟩
  apply moduleSheaf_cohomology_subsingleton_of_constant_prime_tests X R n hn q
    ?_ F hF hkill
  intro p hp hpn Y
  let : Fact p.Prime := ⟨hp⟩
  let : CompactSpace Y.obj.left := QuasiCompact.compactSpace_of_compactSpace Y.obj.hom
  let : HasExt.{u + 2} (AbelianSheaf.{u, u + 1} Y.obj.left) := hasExtStandard Y.obj.left
  have hdimY : topologicalKrullDim Y.obj.left ≤ 1 := dimension_le_one_of_etale Y.obj.hom hdim
  obtain ⟨m, hm⟩ := hpn
  have hmul : IsUnit ((p : k) * (m : k)) := by
    rw [← Nat.cast_mul, ← hm]
    exact hunit
  exact primeField_high_subsingleton_of_finiteType_curve
    Y.obj.left (Y.obj.hom ≫ f) hdimY p
    (IsUnit.mul_iff.mp hmul).1 q hq

/-- Lifted-ZMod local systems retain the original scalar and coefficient
model, including composite positive levels and level one. -/
theorem uLiftZMod_moduleSheaf_high_subsingleton_of_finiteType_curve
    [ConnectedSpace X] (n : ℕ) (hn : 0 < n) (hunit : IsUnit (n : k))
    (q : ℕ) (hq : 2 < q) (F : ModuleSheaf (ULift.{u + 1} (ZMod n)) X)
    (hF : IsFiniteTypeLocallyConstant F) :
    Subsingleton ((ModuleCat.Sheaf.cohomology X.smallEtaleTopology
      (ULift.{u + 1} (ZMod n)) q).obj F) := by
  let : NeZero n := ⟨Nat.ne_of_gt hn⟩
  let : (forget₂ (ModuleCat.{u + 1} (ULift.{u + 1} (ZMod n))) AddCommGrpCat.{u + 1}).Full :=
    ModuleCat.uLiftZMod_forget₂_full n
  apply moduleSheaf_high_subsingleton_of_finiteType_curve X f hdim
    (ULift.{u + 1} (ZMod n)) n hn hunit q hq F hF
  apply ObjectProperty.hom_ext
  ext V m
  change n • m = 0
  rw [← Nat.cast_smul_eq_nsmul (R := ULift.{u + 1} (ZMod n))]
  have hnzero : (n : ULift.{u + 1} (ZMod n)) = 0 := by
    apply ULift.ext
    simp
  rw [hnzero, zero_smul]

/-- The same ordinary high vanishing on the native unit-Ext carrier, with
independent module and abelian Ext universes. -/
theorem moduleUnitExt_high_subsingleton_of_finiteType_curve
    [ConnectedSpace X] (n : ℕ) (hn : 0 < n) (hunit : IsUnit (n : k))
    (q : ℕ) (hq : 2 < q)
    [HasExt.{w'} (Coefficients.ModuleSheaf X (ULift.{u + 1} (ZMod n)))]
    (M : Coefficients.ModuleSheaf X (ULift.{u + 1} (ZMod n)))
    (hM : IsFiniteTypeLocallyConstant
      ((Coefficients.moduleSheafEquivalence X (ULift.{u + 1} (ZMod n))).inverse.obj M)) :
    Subsingleton (CategoryTheory.Abelian.Ext.{w'}
      (moduleUnit X (ULift.{u + 1} (ZMod n))) M q) := by
  let F := (Coefficients.moduleSheafEquivalence X (ULift.{u + 1} (ZMod n))).inverse.obj M
  let : Subsingleton (Sheaf.H.{w}
      ((moduleUnderlying (ULift.{u + 1} (ZMod n)) X).obj F) q) :=
    uLiftZMod_moduleSheaf_high_subsingleton_of_finiteType_curve X f hdim n hn hunit q hq F hM
  let E : CategoryTheory.Abelian.Ext.{w'}
      (moduleUnit X (ULift.{u + 1} (ZMod n))) M q ≃+
      Sheaf.H.{w} ((moduleUnderlying (ULift.{u + 1} (ZMod n)) X).obj F) q :=
    (etaleModuleExtCohomologyAddEquivLargeScalars X
      (Coefficients.constantRing X (ULift.{u + 1} (ZMod n))) M q).trans
        (((Sheaf.functorH X.smallEtaleTopology q).mapIso
          ((Coefficients.moduleSheafInverseUnderlyingIso X
            (ULift.{u + 1} (ZMod n))).app M).symm).addCommGroupIsoToAddEquiv)
  exact E.injective.subsingleton

end FiniteTypeCurve

end AlgebraicGeometry.Scheme.EtaleCohomology.Curves
