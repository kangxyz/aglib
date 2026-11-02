/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.Duality.CoefficientExactness
public import Aglib.AlgebraicGeometry.EtaleCohomology.Duality.ConstantCoefficients
public import Aglib.AlgebraicGeometry.EtaleCohomology.Coefficients.ModuleCohomologyPullback
public import Aglib.AlgebraicGeometry.EtaleCohomology.H1.CyclicKilling
public import Aglib.AlgebraicGeometry.EtaleCohomology.Finiteness.PrimeToCharacteristicCurveH1
public import Aglib.AlgebraicGeometry.EtaleCohomology.Kummer.ModuleCohomology
public import Aglib.AlgebraicGeometry.EtaleCohomology.Exceptional.Open.ModuleComparisons
public import Aglib.AlgebraicGeometry.EtaleCohomology.Curves.FiniteCoefficientsVanishing

/-!
# The native source-Ext reduction for degree-one curve duality

For an actual short exact coefficient sequence, a degree-one class killed by
source precomposition and by the original duality map is zero as soon as the
two indicated degree-zero duality maps are respectively surjective and injective.
The proof constructs the original unsigned boundary and proves both squares;
no commutativity premise or finite-pushforward trace premise is hidden here.
The geometric suppliers needed for unconditional constant perfectness are separate.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian AlgebraicGeometry

namespace AlgebraicGeometry.Scheme.EtaleCohomology

universe u w w' w''

open Coefficients Scheme.OverField

attribute [local instance] hasSheafifyLarge hasSheafifyModules
  CategoryTheory.TorsionZMod.Ringed.abWEqualsLocallyBijectiveStandard moduleSheafExtZModModule

section Killing

variable {U : Scheme.{u}} [ConnectedSpace U] (n : ℕ)
  [HasExt.{w} (ModuleSheaf U (ULift.{u + 1} (ZMod n)))]

/-- Actual finite locally constant coefficient classes are killed for the
original native module-unit pullback. The abelian cohomology comparison is the
existing one, and the module Ext universes on source and cover are independent. -/
theorem exists_galois_finiteEtale_moduleUnitExtPullback_one_eq_zero
    (M : ModuleSheaf U (ULift.{u + 1} (ZMod n)))
    (hM : IsFiniteLocallyConstant
      ((SheafOfModules.toSheaf (constantRing U (ULift.{u + 1} (ZMod n)))).obj M))
    (e : Ext.{w} (moduleUnit U (ULift.{u + 1} (ZMod n))) M 1) :
    ∃ Y : Scheme.FiniteEtale U,
      PreGaloisCategory.IsGalois Y ∧ ConnectedSpace Y.obj.left ∧ Surjective Y.obj.hom ∧
      ∀ [HasExt.{w'} (ModuleSheaf Y.obj.left (ULift.{u + 1} (ZMod n)))],
        moduleUnitExtPullback Y.obj.hom n M 1 e = 0 := by
  let : HasExt.{u + 2} (AbelianSheaf.{u, u + 1} U) := hasExtStandard U
  let E := etaleModuleExtCohomologyAddEquivLargeScalars U
    (constantRing U (ULift.{u + 1} (ZMod n))) M 1
  obtain ⟨Y, hgal, hconn, hsurj, hzero⟩ :=
    exists_galois_finiteEtale_h1Pullback_eq_zero.{u, u + 2, u + 2} hM (E e)
  refine ⟨Y, hgal, hconn, hsurj, ?_⟩
  intro hY
  let : HasExt.{u + 2} (AbelianSheaf.{u, u + 1} Y.obj.left) := hasExtStandard Y.obj.left
  let EY := etaleModuleExtCohomologyAddEquivLargeScalars Y.obj.left
    (constantRing Y.obj.left (ULift.{u + 1} (ZMod n)))
    ((moduleInverseImage Y.obj.hom (ULift.{u + 1} (ZMod n))).obj M) 1
  let EY' := coefficientIso
    ((moduleInverseImageUnderlyingIso (ULift.{u + 1} (ZMod n)) Y.obj.hom).app M)
  apply EY.injective
  apply EY'.injective
  have hv := DFunLike.congr_fun
    (moduleUnitExtCohomologyPullback_square Y.obj.hom n M 1) e
  have hz : cohomologyPullback Y.obj.hom
      ((SheafOfModules.toSheaf (constantRing U (ULift.{u + 1} (ZMod n)))).obj M)
      1 (E e) = 0 := hzero
  change EY' (EY (moduleUnitExtPullback Y.obj.hom n M 1 e)) = _ at hv
  exact (hv.trans hz).trans
    ((congrArg EY' (map_zero EY)).trans (map_zero EY')).symm

/-- The actual unit-to-roots degree-one class has a connected Galois finite
étale killing cover, with no representability or trivialization premise. -/
theorem exists_galois_finiteEtale_moduleRoots_one_killed
    (k : Type u) [Field k] [IsAlgClosed k] (hn : 0 < n) (hunit : IsUnit (n : k))
    (p : U ⟶ Spec (.of k))
    (e : Ext.{w} (moduleUnit U (ULift.{u + 1} (ZMod n))) (moduleRootsOfUnity U n) 1) :
    ∃ Y : Scheme.FiniteEtale U,
      PreGaloisCategory.IsGalois Y ∧ ConnectedSpace Y.obj.left ∧ Surjective Y.obj.hom ∧
      ∀ [HasExt.{w'} (ModuleSheaf Y.obj.left (ULift.{u + 1} (ZMod n)))],
        moduleUnitExtPullback Y.obj.hom n (moduleRootsOfUnity U n) 1 e = 0 := by
  let : NeZero n := ⟨Nat.ne_of_gt hn⟩
  apply exists_galois_finiteEtale_moduleUnitExtPullback_one_eq_zero n _ _ e
  let eA := moduleUnitCoefficientIso U n ≪≫
    (SheafOfModules.toSheaf (constantRing U (ULift.{u + 1} (ZMod n)))).mapIso
      (moduleUnitRootsIso k n hn hunit p)
  exact (isFiniteLocallyConstant_iff_of_iso eA).mp
    (ConstantFinite.isFiniteLocallyConstant (ULift.{u} (ZMod n)) U)

/-- Every original unit-to-roots degree-one class is killed by precomposition
with an actual epimorphic, unit-normalized lower-shriek counit on a constructed
connected Galois finite étale cover. No finite-pushforward pairing premise is used. -/
theorem exists_galois_finiteEtale_unitCounit_one_killed
    (k : Type u) [Field k] [IsAlgClosed k] (hn : 0 < n) (hunit : IsUnit (n : k))
    (p : U ⟶ Spec (.of k))
    (e : Ext.{w} (moduleUnit U (ULift.{u + 1} (ZMod n))) (moduleRootsOfUnity U n) 1) :
    ∃ Y : Scheme.FiniteEtale U,
      PreGaloisCategory.IsGalois Y ∧ ConnectedSpace Y.obj.left ∧ Surjective Y.obj.hom ∧
      Epi (moduleUnitLowerShriekCounit Y.obj.hom n) ∧
      (Ext.mk₀ (moduleUnitLowerShriekCounit Y.obj.hom n)).comp e (zero_add 1) = 0 := by
  obtain ⟨Y, hgal, hconn, hsurj, hzero⟩ :=
    exists_galois_finiteEtale_moduleRoots_one_killed.{u, w, u + 2} n k hn hunit p e
  let : Surjective Y.obj.hom := hsurj
  let : HasExt.{u + 2} (ModuleSheaf Y.obj.left (ULift.{u + 1} (ZMod n))) :=
    SheafOfModules.hasExt (constantRing Y.obj.left (ULift.{u + 1} (ZMod n)))
  refine ⟨Y, hgal, hconn, hsurj, moduleUnitLowerShriekCounit_epi Y.obj.hom n, ?_⟩
  let E : Ext.{w}
      ((moduleLowerShriek Y.obj.hom (ULift.{u + 1} (ZMod n))).obj
        (moduleUnit Y.obj.left (ULift.{u + 1} (ZMod n)))) (moduleRootsOfUnity U n) 1 ≃+
      Ext.{u + 2} (moduleUnit Y.obj.left (ULift.{u + 1} (ZMod n)))
        ((moduleInverseImage Y.obj.hom (ULift.{u + 1} (ZMod n))).obj (moduleRootsOfUnity U n)) 1 :=
    moduleLowerShriekExtEquiv Y.obj.hom (ULift.{u + 1} (ZMod n))
      (moduleUnit Y.obj.left (ULift.{u + 1} (ZMod n))) (moduleRootsOfUnity U n) 1
  apply E.injective
  have h := DFunLike.congr_fun
    (moduleUnitLowerShriekCounit_ext_square Y.obj.hom n (moduleRootsOfUnity U n) 1) e
  change E ((Ext.mk₀ (moduleUnitLowerShriekCounit Y.obj.hom n)).comp e (zero_add 1)) = _ at h
  exact (h.trans hzero).trans (map_zero E).symm

end Killing

section ProperCardinality

variable {k : Type u} [Field k] [IsAlgClosed k] (X : FScheme k) (hX : Curve.Properties X)
  (n : ℕ) (hn : 0 < n) (hunit : IsUnit (n : k))
  [HasExt.{w} (ModuleSheaf X.left (ULift.{u + 1} (ZMod n)))]
  [HasExt.{w'} (ModuleSheaf X.left (ULift.{u + 1} (ZMod n)))]
  [HasExt.{w''} (AbelianSheaf.{u, u + 1} X.left)]

include hX hn hunit in
/-- On the proper curve the two original degree-one arguments are finite and
have equal order. This uses original roots H1 finiteness and coefficient
isomorphisms, without a rank computation or Weil pairing. -/
theorem moduleUnit_one_finite_and_natCard_eq :
    Finite (Ext.{w} (moduleUnit X.left (ULift.{u + 1} (ZMod n)))
      (moduleRootsOfUnity X.left n) 1) ∧
    Finite (Ext.{w'} (moduleUnit X.left (ULift.{u + 1} (ZMod n)))
      ((moduleLowerShriek (𝟙 X.left) (ULift.{u + 1} (ZMod n))).obj
        (moduleUnit X.left (ULift.{u + 1} (ZMod n)))) 1) ∧
    Nat.card (Ext.{w} (moduleUnit X.left (ULift.{u + 1} (ZMod n)))
        (moduleRootsOfUnity X.left n) 1) =
      Nat.card (Ext.{w'} (moduleUnit X.left (ULift.{u + 1} (ZMod n)))
        ((moduleLowerShriek (𝟙 X.left) (ULift.{u + 1} (ZMod n))).obj
          (moduleUnit X.left (ULift.{u + 1} (ZMod n)))) 1) := by
  let : Finite (Sheaf.H.{w''} (GroupCohomology.Kummer.Coefficients.mu X.left n) 1) :=
    Finiteness.finite_roots_h1_of_smooth_proper_curve X hX n hn hunit
  let e := (moduleLowerShriekIdIso (ULift.{u + 1} (ZMod n)) X.left).app
      (moduleUnit X.left (ULift.{u + 1} (ZMod n))) ≪≫
    moduleUnitRootsIso k n hn hunit X.hom
  let Ec : Ext.{w'} (moduleUnit X.left (ULift.{u + 1} (ZMod n)))
      ((moduleLowerShriek (𝟙 X.left) (ULift.{u + 1} (ZMod n))).obj
        (moduleUnit X.left (ULift.{u + 1} (ZMod n)))) 1 ≃+
      Sheaf.H.{w''} (GroupCohomology.Kummer.Coefficients.mu X.left n) 1 :=
    (((extFunctorObj (moduleUnit X.left (ULift.{u + 1} (ZMod n))) 1).mapIso
      e).addCommGroupIsoToAddEquiv).trans
        (moduleRootsUnitExtCohomologyAddEquiv.{u, w', w''} X.left n 1)
  let Eo := moduleRootsUnitExtCohomologyAddEquiv.{u, w, w''} X.left n 1
  exact ⟨Finite.of_injective Eo Eo.injective, Finite.of_injective Ec Ec.injective,
    Nat.card_congr (Eo.trans Ec.symm).toEquiv⟩

omit [HasExt.{w} (ModuleSheaf X.left (ULift.{u + 1} (ZMod n)))] in
include hX hn hunit in
/-- Proper compact support through the original identity lower shriek vanishes
above degree two for every actual finite-LCC coefficient. -/
theorem moduleUnitCompactIdExt_subsingleton_of_finiteLocallyConstant
    (M : ModuleSheaf X.left (ULift.{u + 1} (ZMod n)))
    (hM : Constructible.Modules.IsFiniteTypeLocallyConstant
      ((moduleSheafEquivalence X.left (ULift.{u + 1} (ZMod n))).inverse.obj M))
    (q : ℕ) (hq : 2 < q) :
    Subsingleton (Ext.{w'} (moduleUnit X.left (ULift.{u + 1} (ZMod n)))
      ((moduleLowerShriek (𝟙 X.left) (ULift.{u + 1} (ZMod n))).obj M) q) := by
  let : Subsingleton (Ext.{w'} (moduleUnit X.left (ULift.{u + 1} (ZMod n))) M q) :=
    Curves.moduleUnitExt_subsingleton_of_finiteLocallyConstant X hX n hn hunit q hq M hM
  let E : Ext.{w'} (moduleUnit X.left (ULift.{u + 1} (ZMod n)))
      ((moduleLowerShriek (𝟙 X.left) (ULift.{u + 1} (ZMod n))).obj M) q ≃+
      Ext.{w'} (moduleUnit X.left (ULift.{u + 1} (ZMod n))) M q :=
    ((extFunctorObj (moduleUnit X.left (ULift.{u + 1} (ZMod n))) q).mapIso
      ((moduleLowerShriekIdIso (ULift.{u + 1} (ZMod n)) X.left).app M)).addCommGroupIsoToAddEquiv
  exact E.injective.subsingleton

end ProperCardinality

variable {k : Type u} [Field k] [IsAlgClosed k] (X : FScheme k) (hX : Curve.Properties X)
  (D : Set X.left) (hfin : D.Finite) (hclosed : ∀ x ∈ D, IsClosed ({x} : Set X.left))
  {U : Scheme.{u}} (j : U ⟶ X.left) [IsOpenImmersion j] (hD : Set.range j = Dᶜ)
  (n : ℕ) (hn : 0 < n) (hunit : IsUnit (n : k)) (hinv : IsUnit (n : Γ(X.left, ⊤)))
  [HasExt.{w} (ModuleSheaf U (ULift.{u + 1} (ZMod n)))]
  [HasExt.{w'} (ModuleSheaf X.left (ULift.{u + 1} (ZMod n)))]
  [HasExt.{w''} (AbelianSheaf.{u, u + 1} X.left)]

/-- The original degree-one class vanishes if both its original source pullback
and its original trace-duality functional vanish, under the two precise
degree-zero perfectness consequences needed by the diagram chase. -/
theorem moduleDualityTransposeMap_one_eq_zero_of_precomp_eq_zero
    {S : ShortComplex (ModuleSheaf U (ULift.{u + 1} (ZMod n)))} (hS : S.ShortExact)
    (hB : Function.Surjective (moduleDualityTransposeMap X hX D hfin hclosed j hD
      n hn hunit hinv S.X₂ 0 (by decide)))
    (hK : Function.Injective (moduleDualityTransposeMap X hX D hfin hclosed j hD
      n hn hunit hinv S.X₁ 0 (by decide)))
    (e : Ext.{w} S.X₃ (moduleRootsOfUnity U n) 1)
    (he : (Ext.mk₀ S.g).comp e (zero_add 1) = 0)
    (hzero : moduleDualityTransposeMap X hX D hfin hclosed j hD n hn hunit hinv
      S.X₃ 1 (by decide) e = 0) : e = 0 := by
  let : NeZero n := ⟨Nat.ne_of_gt hn⟩
  let d := AddMonoidHom.toZModLinearMap n
    ((shortExact_moduleLowerShriek j (ULift.{u + 1} (ZMod n)) hS).extClass.postcomp
      (moduleUnit X.left (ULift.{u + 1} (ZMod n))) (show 1 + 1 = 2 from rfl))
  let i := AddMonoidHom.toZModLinearMap n
    ((Ext.mk₀ ((moduleLowerShriek j (ULift.{u + 1} (ZMod n))).map S.f)).postcomp
      (moduleUnit X.left (ULift.{u + 1} (ZMod n))) (add_zero 2))
  have hdi : Function.Exact d i := by
    have h := Ext.covariant_sequence_exact₁'
      (moduleUnit X.left (ULift.{u + 1} (ZMod n)))
      (shortExact_moduleLowerShriek j (ULift.{u + 1} (ZMod n)) hS) 1 2 rfl
    rw [ShortComplex.ab_exact_iff_function_exact] at h
    exact h
  obtain ⟨a, ha⟩ := Ext.contravariant_sequence_exact₃ hS (moduleRootsOfUnity U n)
    e he (n₀ := 0) rfl
  let aDual := moduleDualityTransposeMap X hX D hfin hclosed j hD n hn hunit hinv
    S.X₁ 0 (by decide) a
  have hd : d.dualMap aDual = 0 := by
    have hv := LinearMap.congr_fun
      (moduleDualityTransposeMap_extClass X hX D hfin hclosed j hD n hn hunit hinv
        hS 0 (by decide)) a
    change moduleDualityTransposeMap X hX D hfin hclosed j hD n hn hunit hinv
      S.X₃ 1 (by decide) (hS.extClass.comp a rfl) = d.dualMap aDual at hv
    rw [ha, hzero] at hv
    exact hv.symm
  obtain ⟨l, hl⟩ := (ZMod.dualMap_exact n d i hdi aDual).mp hd
  obtain ⟨b, hb⟩ := hB l
  have hab : (Ext.mk₀ S.f).comp b (zero_add 0) = a := by
    apply hK
    have hv := LinearMap.congr_fun
      (moduleDualityTransposeMap_naturality X hX D hfin hclosed j hD n hn hunit hinv
        S.f 0 (by decide)) b
    change moduleDualityTransposeMap X hX D hfin hclosed j hD n hn hunit hinv
      S.X₁ 0 (by decide) ((Ext.mk₀ S.f).comp b (zero_add 0)) =
        i.dualMap (moduleDualityTransposeMap X hX D hfin hclosed j hD n hn hunit hinv
          S.X₂ 0 (by decide) b) at hv
    exact hv.trans ((congrArg i.dualMap hb).trans hl)
  rw [← ha, ← hab]
  exact hS.extClass_comp_assoc b

end AlgebraicGeometry.Scheme.EtaleCohomology
