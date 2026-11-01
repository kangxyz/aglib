/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.Duality.PointPurity
public import Aglib.AlgebraicGeometry.EtaleCohomology.Duality.ConstantPerfectness
public import Aglib.AlgebraicGeometry.EtaleCohomology.Duality.FinitePushforward
public import Aglib.AlgebraicGeometry.EtaleCohomology.StrictlyLocal.Standard

/-!
# The original point-supported trace pairing

Closed-support excision and the actual trace-counit formula identify evaluation
on the original compact point generator with the already normalized supported
point map. The Ext worlds on the open and its completion remain independent.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian AlgebraicGeometry

universe u wU wX wA wZ wV wP

namespace AlgebraicGeometry.Scheme.EtaleCohomology

open Coefficients Scheme.OverField

attribute [local instance] hasSheafifyLarge hasSheafifyModules
  CategoryTheory.TorsionZMod.Ringed.abWEqualsLocallyBijectiveStandard moduleSheafExtZModModule

section PointExcision

variable {Z U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j]
  (i : Z ⟶ U) [IsClosedImmersion (i ≫ j)] (n : ℕ) (hn : 0 < n)
  (hinv : IsUnit (n : Γ(X, ⊤)))
  [HasExt.{wU} (ModuleSheaf U (ULift.{u + 1} (ZMod n)))]
  [HasExt.{wX} (ModuleSheaf X (ULift.{u + 1} (ZMod n)))]

/-- The inverse of the original point excision equivalence uses the inverse
closed-support iso and the original lower-shriek Ext adjunction counit. -/
theorem modulePointExtExcisionAddEquiv_symm_apply (q : ℕ)
    (e : Ext.{wU} ((moduleDirectImage i (ULift.{u + 1} (ZMod n))).obj
      (moduleUnit Z (ULift.{u + 1} (ZMod n)))) (moduleRootsOfUnity U n) q) :
    (modulePointExtExcisionAddEquiv j i n hn hinv q).symm e =
      (Ext.mk₀ (modulePointLowerShriekDirectImageIso j i n).inv).comp
        ((moduleLowerShriekExtEquiv j (ULift.{u + 1} (ZMod n))
          ((moduleDirectImage i (ULift.{u + 1} (ZMod n))).obj
            (moduleUnit Z (ULift.{u + 1} (ZMod n)))) (moduleRootsOfUnity X n) q).symm
              (e.comp (Ext.mk₀ (moduleRootsOfUnityInverseImageIso j n hn hinv).inv)
                (add_zero q))) (zero_add q) := rfl

end PointExcision

section PointScalars

variable {Z X : Scheme.{u}} (i : Z ⟶ X) [IsFinite i] [ConnectedSpace Z]
  (n : ℕ) [NeZero n]
  [HasExt.{wX} (ModuleSheaf X (ULift.{u + 1} (ZMod n)))]

/-- For a finite connected source the original point-unit map generates all
native degree-zero maps from the unit to its direct image. -/
theorem modulePointUnitMap_scalar_bijective :
    Function.Bijective (fun a : ZMod n => a • Ext.mk₀ (modulePointUnitMap i n)) := by
  let : HasExt.{u + 2} (ModuleSheaf Z (ULift.{u + 1} (ZMod n))) :=
    SheafOfModules.hasExt (constantRing Z (ULift.{u + 1} (ZMod n)))
  let : PreservesFiniteColimits (moduleDirectImage i (ULift.{u + 1} (ZMod n))) :=
    Functor.preservesFiniteColimits_of_preservesHomology _
  let E := moduleFiniteUnitExtAddEquiv.{u, wX, u + 2} i n
    (moduleUnit Z (ULift.{u + 1} (ZMod n))) 0
  have hid : E.symm (Ext.mk₀ (𝟙 (moduleUnit Z (ULift.{u + 1} (ZMod n))))) =
      Ext.mk₀ (modulePointUnitMap i n) := by
    have h := DFunLike.congr_fun
      (moduleFiniteUnitExtAddEquiv_symm_toAddMonoidHom i n
        (moduleUnit Z (ULift.{u + 1} (ZMod n))) 0)
      (Ext.mk₀ (𝟙 (moduleUnit Z (ULift.{u + 1} (ZMod n)))))
    change E.symm (Ext.mk₀ (𝟙 (moduleUnit Z (ULift.{u + 1} (ZMod n))))) =
      (Ext.mk₀ (modulePointUnitMap i n)).comp
        ((Ext.mk₀ (𝟙 (moduleUnit Z (ULift.{u + 1} (ZMod n))))).mapExactFunctor
          (moduleDirectImage i (ULift.{u + 1} (ZMod n)))) (zero_add 0) at h
    rw [Ext.mapExactFunctor_mk₀] at h
    have hmap : (moduleDirectImage i (ULift.{u + 1} (ZMod n))).map
        (𝟙 (moduleUnit Z (ULift.{u + 1} (ZMod n)))) = 𝟙 _ :=
      (moduleDirectImage i (ULift.{u + 1} (ZMod n))).map_id _
    rw [hmap] at h
    simpa only [Ext.comp_mk₀_id] using h
  have he : (fun a : ZMod n => a • Ext.mk₀ (modulePointUnitMap i n)) =
      E.symm ∘ moduleUnitScalarLinearMap Z n := by
    funext a
    change a • Ext.mk₀ (modulePointUnitMap i n) =
      E.symm (a • Ext.mk₀ (𝟙 (moduleUnit Z (ULift.{u + 1} (ZMod n)))))
    rw [ZMod.map_smul, hid]
  rw [he]
  exact E.symm.bijective.comp (moduleUnitScalarLinearMap_bijective Z n)

end PointScalars

section PointTrace

variable {k : Type u} [Field k] [IsAlgClosed k] (X : FScheme k) (hX : Curve.Properties X)
  (D : Set X.left) (hfin : D.Finite) (hclosed : ∀ x ∈ D, IsClosed ({x} : Set X.left))
  {U : Scheme.{u}} (j : U ⟶ X.left) [IsOpenImmersion j] (hD : Set.range j = Dᶜ)
  {Z : Scheme.{u}} (i : Z ⟶ U) [IsClosedImmersion (i ≫ j)]
  (n : ℕ) (hn : 0 < n) (hunit : IsUnit (n : k)) (hinv : IsUnit (n : Γ(X.left, ⊤)))
  [HasExt.{wU} (ModuleSheaf U (ULift.{u + 1} (ZMod n)))]
  [HasExt.{wX} (ModuleSheaf X.left (ULift.{u + 1} (ZMod n)))]
  [HasExt.{wA} (AbelianSheaf.{u, u + 1} X.left)]

/-- The original compact degree-zero point arrow, formed from the same
composite point and the inverse of the existing closed-support comparison. -/
def moduleCompactPointUnitMap :
    moduleUnit X.left (ULift.{u + 1} (ZMod n)) ⟶
      (moduleLowerShriek j (ULift.{u + 1} (ZMod n))).obj
        ((moduleDirectImage i (ULift.{u + 1} (ZMod n))).obj
          (moduleUnit Z (ULift.{u + 1} (ZMod n)))) :=
  modulePointUnitMap (i ≫ j) n ≫ (modulePointLowerShriekDirectImageIso j i n).inv

omit [IsAlgClosed k] [HasExt.{wU} (ModuleSheaf U (ULift.{u + 1} (ZMod n)))]
  [HasExt.{wA} (AbelianSheaf.{u, u + 1} X.left)] in
/-- The original compact point arrow generates the native compact degree-zero
argument when the point scheme is connected. -/
theorem moduleCompactPointUnitMap_scalar_bijective [ConnectedSpace Z] [NeZero n] :
    Function.Bijective (fun a : ZMod n =>
      a • Ext.mk₀ (moduleCompactPointUnitMap X j i n)) := by
  let E : Ext.{wX} (moduleUnit X.left (ULift.{u + 1} (ZMod n)))
      ((moduleLowerShriek j (ULift.{u + 1} (ZMod n))).obj
        ((moduleDirectImage i (ULift.{u + 1} (ZMod n))).obj
          (moduleUnit Z (ULift.{u + 1} (ZMod n))))) 0 ≃+
        Ext.{wX} (moduleUnit X.left (ULift.{u + 1} (ZMod n)))
          ((moduleDirectImage (i ≫ j) (ULift.{u + 1} (ZMod n))).obj
            (moduleUnit Z (ULift.{u + 1} (ZMod n)))) 0 :=
    ((extFunctorObj (moduleUnit X.left (ULift.{u + 1} (ZMod n))) 0).mapIso
      (modulePointLowerShriekDirectImageIso j i n)).addCommGroupIsoToAddEquiv
  have he : (fun a : ZMod n => a • Ext.mk₀ (moduleCompactPointUnitMap X j i n)) =
      E.symm ∘ (fun a : ZMod n => a • Ext.mk₀ (modulePointUnitMap (i ≫ j) n)) := by
    funext a
    rw [Function.comp_apply, ZMod.map_smul]
    change a • Ext.mk₀ (moduleCompactPointUnitMap X j i n) =
      a • (Ext.mk₀ (modulePointUnitMap (i ≫ j) n)).comp
        (Ext.mk₀ (modulePointLowerShriekDirectImageIso j i n).inv) (add_zero 0)
    rw [Ext.mk₀_comp_mk₀]
    rfl
  rw [he]
  exact E.symm.bijective.comp (modulePointUnitMap_scalar_bijective (i ≫ j) n)

/-- Evaluation on the original compact point generator is the original
proper support-forgetting map after closed-support excision, followed by trace.
This proves the whole degree-zero/degree-two point square. -/
theorem moduleTracePairingLinearMap_compactPointUnit :
    ((moduleTracePairingLinearMap X hX D hfin hclosed j hD n hn hunit hinv
      ((moduleDirectImage i (ULift.{u + 1} (ZMod n))).obj
        (moduleUnit Z (ULift.{u + 1} (ZMod n)))) 0 2 rfl)
          (Ext.mk₀ (moduleCompactPointUnitMap X j i n))).toAddMonoidHom =
      (Curves.traceAddEquiv hX n hn hunit hinv).toAddMonoidHom.comp
        ((modulePointExtToCohomology (i ≫ j) n 2).comp
          (modulePointExtExcisionAddEquiv j i n hn hinv 2).symm.toAddMonoidHom) := by
  ext e
  change moduleTracePairingLinearMap X hX D hfin hclosed j hD n hn hunit hinv
      ((moduleDirectImage i (ULift.{u + 1} (ZMod n))).obj
        (moduleUnit Z (ULift.{u + 1} (ZMod n)))) 0 2 rfl
          (Ext.mk₀ (moduleCompactPointUnitMap X j i n)) e =
    Curves.traceAddEquiv hX n hn hunit hinv
      (modulePointExtToCohomology (i ≫ j) n 2
        ((modulePointExtExcisionAddEquiv j i n hn hinv 2).symm e))
  rw [moduleTracePairingLinearMap_apply_apply,
    moduleCompactSupportTraceAddEquiv_counit_apply]
  change Curves.traceAddEquiv hX n hn hunit hinv
      (moduleRootsUnitExtCohomologyAddEquiv X.left n 2
        ((moduleLowerShriekPairing j (ULift.{u + 1} (ZMod n))
          (Ext.mk₀ (moduleCompactPointUnitMap X j i n)) e rfl).comp
            (Ext.mk₀ ((moduleLowerShriek j (ULift.{u + 1} (ZMod n))).map
              (moduleRootsOfUnityInverseImageIso j n hn hinv).inv ≫
                (moduleLowerShriekAdjunction j (ULift.{u + 1} (ZMod n))).counit.app
                  (moduleRootsOfUnity X.left n))) (add_zero 2))) =
    Curves.traceAddEquiv hX n hn hunit hinv
      (moduleRootsUnitExtCohomologyAddEquiv X.left n 2
        ((Ext.mk₀ (modulePointUnitMap (i ≫ j) n)).comp
          ((modulePointExtExcisionAddEquiv j i n hn hinv 2).symm e) (zero_add 2)))
  apply congrArg (Curves.traceAddEquiv hX n hn hunit hinv)
  apply congrArg (moduleRootsUnitExtCohomologyAddEquiv X.left n 2)
  rw [modulePointExtExcisionAddEquiv_symm_apply,
    moduleLowerShriekExtEquiv_symm_apply, moduleLowerShriekExt_comp,
    moduleLowerShriekExt_mk₀, Ext.mk₀_comp_mk₀_assoc]
  change ((Ext.mk₀ (moduleCompactPointUnitMap X j i n)).comp
      (e.mapExactFunctor (moduleLowerShriek j (ULift.{u + 1} (ZMod n)))) (zero_add 2)).comp
      (Ext.mk₀ _) (add_zero 2) = _
  rw [Ext.comp_assoc_of_third_deg_zero, Ext.comp_assoc_of_third_deg_zero,
    Ext.mk₀_comp_mk₀]
  rw [moduleLowerShriekExt_apply]
  rfl

omit [IsClosedImmersion (i ≫ j)] in
/-- The original point-supported pairing on a given open curve is perfect in
compact degree zero and supported Ext degree two. Its normalization is the
original Kummer point trace, with no purity or diagram premise. -/
theorem moduleDualityMap_point_zero_isPerfPair (x : Scheme.ClosedPoint U) :
    (moduleDualityMap X hX D hfin hclosed j hD n hn hunit hinv
      ((moduleDirectImage (U.fromSpecResidueField x.val) (ULift.{u + 1} (ZMod n))).obj
        (moduleUnit (Spec (U.residueField x.val)) (ULift.{u + 1} (ZMod n))))
          0 (by decide)).IsPerfPair := by
  let : NeZero n := ⟨Nat.ne_of_gt hn⟩
  let ip := U.fromSpecResidueField x.val
  let : IsClosedImmersion (ip ≫ j) := modulePoint_composite_isClosedImmersion hX j x
  let z : Scheme.ClosedPoint X.left := ⟨j x.val, modulePoint_image_isClosed hX j x⟩
  let M := (moduleDirectImage ip (ULift.{u + 1} (ZMod n))).obj
    (moduleUnit (Spec (U.residueField x.val)) (ULift.{u + 1} (ZMod n)))
  let B := moduleTracePairingLinearMap X hX D hfin hclosed j hD n hn hunit hinv M 0 2 rfl
  change B.IsPerfPair
  suffices h : B.flip.IsPerfPair from h.flip
  apply ZMod.isPerfPair_of_bijective_eval_generator n B.flip
    (Ext.mk₀ (moduleCompactPointUnitMap X j ip n))
    (moduleCompactPointUnitMap_scalar_bijective X j ip n).surjective
  change Function.Bijective
    ((B (Ext.mk₀ (moduleCompactPointUnitMap X j ip n))).toAddMonoidHom)
  rw [moduleTracePairingLinearMap_compactPointUnit]
  exact (Curves.traceAddEquiv hX n hn hunit hinv).bijective.comp
    ((modulePointExtToCohomology_two_bijective hX z (ip ≫ j)
      (modulePoint_composite_range j x) n hn hunit hinv).comp
        (modulePointExtExcisionAddEquiv j ip n hn hinv 2).symm.bijective)

omit [HasExt.{wU} (ModuleSheaf U (ULift.{u + 1} (ZMod n)))]
  [HasExt.{wA} (AbelianSheaf.{u, u + 1} X.left)] [IsClosedImmersion (i ≫ j)] in
include hX in
/-- A point-supported coefficient has no positive compact cohomology. The
original residue field is separably closed, and the original finite-image and
module-unit comparisons identify its compact Ext with its actual Sheaf.H. -/
theorem moduleCompactPointUnitExt_pos_subsingleton (x : Scheme.ClosedPoint U)
    (q : ℕ) (hq : 0 < q) :
    Subsingleton (Ext.{wX} (moduleUnit X.left (ULift.{u + 1} (ZMod n)))
      ((moduleLowerShriek j (ULift.{u + 1} (ZMod n))).obj
        ((moduleDirectImage (U.fromSpecResidueField x.val) (ULift.{u + 1} (ZMod n))).obj
          (moduleUnit (Spec (U.residueField x.val)) (ULift.{u + 1} (ZMod n))))) q) := by
  let ip := U.fromSpecResidueField x.val
  let Z := Spec (U.residueField x.val)
  let : IsClosedImmersion (ip ≫ j) := modulePoint_composite_isClosedImmersion hX j x
  let : HasExt.{u + 2} (ModuleSheaf Z (ULift.{u + 1} (ZMod n))) :=
    SheafOfModules.hasExt (constantRing Z (ULift.{u + 1} (ZMod n)))
  let : HasExt.{u + 2} (AbelianSheaf.{u, u + 1} Z) := hasExtStandard Z
  let := Curve.curveProperties_locallyOfFiniteType hX
  let : LocallyOfFiniteType (j ≫ X.hom) := inferInstance
  let := residueAlgebra U (j ≫ X.hom) x.val
  let : Module.Finite k (U.residueField x.val) := residue_finite U (j ≫ X.hom) x
  let : IsSepClosed (U.residueField x.val) := Algebra.IsAlgebraic.isSepClosed (F := k)
  let : HenselianLocalRing (U.residueField x.val) := Field.henselian _
  let : IsSepClosed (IsLocalRing.ResidueField (U.residueField x.val)) :=
    Algebra.IsAlgebraic.isSepClosed (F := U.residueField x.val)
  let M := moduleUnit Z (ULift.{u + 1} (ZMod n))
  let : Subsingleton (Sheaf.H.{u + 2}
      ((SheafOfModules.toSheaf (constantRing Z (ULift.{u + 1} (ZMod n)))).obj M) q) :=
    StrictlyLocal.subsingleton_H_standard (U.residueField x.val) _ q hq
  let E₁ : Ext.{wX} (moduleUnit X.left (ULift.{u + 1} (ZMod n)))
      ((moduleLowerShriek j (ULift.{u + 1} (ZMod n))).obj
        ((moduleDirectImage ip (ULift.{u + 1} (ZMod n))).obj M)) q ≃+
        Ext.{wX} (moduleUnit X.left (ULift.{u + 1} (ZMod n)))
          ((moduleDirectImage (ip ≫ j) (ULift.{u + 1} (ZMod n))).obj M) q :=
    ((extFunctorObj (moduleUnit X.left (ULift.{u + 1} (ZMod n))) q).mapIso
      (modulePointLowerShriekDirectImageIso j ip n)).addCommGroupIsoToAddEquiv
  let E₂ := moduleFiniteUnitExtAddEquiv.{u, wX, u + 2} (ip ≫ j) n M q
  let E₃ := etaleModuleExtCohomologyAddEquivLargeScalars Z
    (constantRing Z (ULift.{u + 1} (ZMod n))) M q
  exact (E₁.trans (E₂.trans E₃)).injective.subsingleton

omit [IsClosedImmersion (i ≫ j)] in
/-- All three degrees of the original point-supported trace pairing are
perfect, including positive composite levels and level one. -/
theorem moduleDualityMap_point_isPerfPair (x : Scheme.ClosedPoint U)
    (r : ℕ) (hr : r ≤ 2) :
    (moduleDualityMap X hX D hfin hclosed j hD n hn hunit hinv
      ((moduleDirectImage (U.fromSpecResidueField x.val) (ULift.{u + 1} (ZMod n))).obj
        (moduleUnit (Spec (U.residueField x.val)) (ULift.{u + 1} (ZMod n)))) r hr).IsPerfPair := by
  let : NeZero n := ⟨Nat.ne_of_gt hn⟩
  interval_cases r
  · exact moduleDualityMap_point_zero_isPerfPair X hX D hfin hclosed j hD n hn hunit hinv x
  · have := moduleCompactPointUnitExt_pos_subsingleton X hX j n x 1 (by decide)
    have := moduleOpenPointExt_one_subsingleton hX j x n hn hunit
    exact ZMod.isPerfPair_of_subsingleton n _
  · have := moduleCompactPointUnitExt_pos_subsingleton X hX j n x 2 (by decide)
    have := moduleOpenPointExt_zero_subsingleton hX j x n hn hunit
    exact ZMod.isPerfPair_of_subsingleton n _

end PointTrace












end AlgebraicGeometry.Scheme.EtaleCohomology
