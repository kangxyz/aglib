/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.Duality.TracePairing
public import Aglib.AlgebraicGeometry.EtaleCohomology.Duality.ConstantCoefficients
public import Aglib.AlgebraicGeometry.EtaleCohomology.CurveCohomology.Complement
public import Aglib.AlgebraicGeometry.EtaleCohomology.Exceptional.Open.ModuleIsomorphism
public import Aglib.AlgebraicGeometry.EtaleCohomology.Exceptional.Coefficients.ModuleUnitInverseImage
public import Aglib.Algebra.Module.ZMod.CyclicPairing
public import Aglib.Algebra.Homology.DerivedCategory.Ext.Equivalence
public import Mathlib.AlgebraicGeometry.Morphisms.IsIso

/-!
# Constant-coefficient curve duality in degrees zero and two

The original trace-composed Yoneda pairing for the unit coefficient is perfect
in degrees zero and two on a smooth proper geometrically connected curve and
on the complement of finitely many closed points. The public statements use
native `LinearMap.IsPerfPair` and contain no primitive root or basis choice.

Degree two is evaluation on a root generator followed by the actual trace.
For a nonempty complement both degree-zero arguments vanish. For the empty
complement the original open immersion is an isomorphism, and the original
adjunction counit transports the scalar identity generator. No purity, rank
assertion, degree-one perfectness, or SGA sign comparison is used or asserted.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian AlgebraicGeometry

universe u w w' w''

namespace AlgebraicGeometry.Scheme.EtaleCohomology

open Coefficients Scheme.OverField GroupCohomology.Kummer.Coefficients

attribute [local instance] hasSheafifyLarge hasSheafifyModules
  CategoryTheory.TorsionZMod.Ringed.abWEqualsLocallyBijectiveStandard moduleSheafExtZModModule

variable {k : Type u} [Field k] [IsAlgClosed k] (X : FScheme k) (hX : Curve.Properties X)
  (D : Set X.left) (hfin : D.Finite) (hclosed : ∀ x ∈ D, IsClosed ({x} : Set X.left))
  {U : Scheme.{u}} (j : U ⟶ X.left) [IsOpenImmersion j] (hD : Set.range j = Dᶜ)

omit [IsAlgClosed k] [IsOpenImmersion j] in
include hX hfin hclosed hD in
/-- A finite closed-point complement cannot exhaust a one-dimensional proper curve. -/
theorem nonempty_of_curve_finite_complement : Nonempty U := by
  classical
  by_contra hU
  have : IsEmpty U := not_nonempty_iff.mp hU
  have hDu : D = Set.univ := by
    apply compl_injective
    rw [Set.compl_univ, ← hD]
    exact Set.range_eq_empty j
  have : Finite X.left := Set.finite_univ_iff.mp (hDu ▸ hfin)
  have : T1Space X.left := ⟨fun x => hclosed x (by rw [hDu]; trivial)⟩
  have hdim := topologicalKrullDim_zero_of_discreteTopology X.left
  rw [hX.topologicalKrullDim_eq_one] at hdim
  exact (by norm_num : ¬ (1 : WithBot ℕ∞) ≤ 0) hdim

omit [IsAlgClosed k] in
include hX hfin hclosed hD in
/-- The finite-complement open of the original curve is connected. -/
theorem connectedSpace_of_curve_finite_complement : ConnectedSpace U := by
  have : Nonempty U := nonempty_of_curve_finite_complement X hX D hfin hclosed j hD
  have := hX.isIntegral
  have : IsIntegral U := isIntegral_of_isOpenImmersion j
  infer_instance

variable (n : ℕ) (hn : 0 < n) (hunit : IsUnit (n : k)) (hinv : IsUnit (n : Γ(X.left, ⊤)))
  [HasExt.{w} (ModuleSheaf U (ULift.{u + 1} (ZMod n)))]
  [HasExt.{w'} (ModuleSheaf X.left (ULift.{u + 1} (ZMod n)))]
  [HasExt.{w''} (AbelianSheaf.{u, u + 1} X.left)]

/-- The original constant-coefficient pairing is perfect in compact-support degree two. -/
theorem moduleDualityMap_unit_two_isPerfPair :
    (moduleDualityMap X hX D hfin hclosed j hD n hn hunit hinv
      (moduleUnit U (ULift.{u + 1} (ZMod n))) 2 le_rfl).IsPerfPair := by
  let : NeZero n := ⟨Nat.ne_of_gt hn⟩
  have : ConnectedSpace U := connectedSpace_of_curve_finite_complement X hX D hfin hclosed j hD
  let e := moduleUnitRootsIso k n hn hunit (j ≫ X.hom)
  let B := moduleTracePairingLinearMap X hX D hfin hclosed j hD n hn hunit hinv
    (moduleUnit U (ULift.{u + 1} (ZMod n))) 2 0 rfl
  change B.IsPerfPair
  apply ZMod.isPerfPair_of_bijective_eval_generator n B (Ext.mk₀ e.hom)
    (moduleUnitIsoScalarMap_bijective U n e).surjective
  let E : Ext.{w'} (moduleUnit X.left (ULift.{u + 1} (ZMod n)))
      ((moduleLowerShriek j (ULift.{u + 1} (ZMod n))).obj
        (moduleUnit U (ULift.{u + 1} (ZMod n)))) 2 ≃+
      Ext.{w'} (moduleUnit X.left (ULift.{u + 1} (ZMod n)))
        ((moduleLowerShriek j (ULift.{u + 1} (ZMod n))).obj (moduleRootsOfUnity U n)) 2 :=
    ((extFunctorObj (moduleUnit X.left (ULift.{u + 1} (ZMod n))) 2).mapIso
      ((moduleLowerShriek j (ULift.{u + 1} (ZMod n))).mapIso e)).addCommGroupIsoToAddEquiv
  have h := (moduleCompactSupportTraceAddEquiv X hX D hfin hclosed j hD n hn hunit
    hinv).bijective.comp E.bijective
  have he : (fun c => B c (Ext.mk₀ e.hom)) =
      (moduleCompactSupportTraceAddEquiv X hX D hfin hclosed j hD n hn hunit hinv) ∘ E := by
    funext c
    change moduleCompactSupportTraceAddEquiv X hX D hfin hclosed j hD n hn hunit hinv
        (Functor.extPairing _ _ c (Ext.mk₀ e.hom) (add_zero 2)) = _
    rw [Functor.extPairing_mk₀_right]
    rfl
  rw [he]
  exact h

omit [HasExt.{w} (ModuleSheaf U (ULift.{u + 1} (ZMod n)))] in
include hX hfin hclosed hD hn hunit in
/-- The original compact-support degree-zero unit-module Ext vanishes for a nonempty complement. -/
theorem subsingleton_moduleUnit_compactSupport_zero (hDne : D.Nonempty) :
    Subsingleton (Ext.{w'} (moduleUnit X.left (ULift.{u + 1} (ZMod n)))
      ((moduleLowerShriek j (ULift.{u + 1} (ZMod n))).obj
        (moduleUnit U (ULift.{u + 1} (ZMod n)))) 0) := by
  have := CompactSupport.subsingleton_H_roots_zero_of_curve X hX D hfin hclosed j hD n hDne hunit
  let e := moduleUnitRootsIso k n hn hunit (j ≫ X.hom)
  let E := ((extFunctorObj (moduleUnit X.left (ULift.{u + 1} (ZMod n))) 0).mapIso
    ((moduleLowerShriek j (ULift.{u + 1} (ZMod n))).mapIso e)).addCommGroupIsoToAddEquiv
  let E' : Ext.{w'} (moduleUnit X.left (ULift.{u + 1} (ZMod n)))
      ((moduleLowerShriek j (ULift.{u + 1} (ZMod n))).obj (moduleRootsOfUnity U n)) 0 ≃+
        CompactSupport.H.{w''} j (mu U n) 0 :=
    (moduleLowerShriekCohomologyAddEquiv j (ULift.{u + 1} (ZMod n))
      (moduleRootsOfUnity U n) 0).trans
      (((CompactSupport.functor j 0).mapIso
        (moduleRootsOfUnityUnderlyingIso U n)).addCommGroupIsoToAddEquiv)
  exact (E.trans E').injective.subsingleton

omit [HasExt.{w'} (ModuleSheaf X.left (ULift.{u + 1} (ZMod n)))]
  [HasExt.{w''} (AbelianSheaf.{u, u + 1} X.left)] in
include hX hclosed hD hunit in
/-- The original ordinary degree-two unit-to-roots Ext vanishes on a punctured curve. -/
theorem subsingleton_moduleUnit_roots_two (hDne : D.Nonempty) :
    Subsingleton (Ext.{w} (moduleUnit U (ULift.{u + 1} (ZMod n)))
      (moduleRootsOfUnity U n) 2) := by
  let : HasExt.{u + 2} (AbelianSheaf.{u, u + 1} U) := hasExtStandard U
  have := Curves.roots_subsingleton_H_of_range_eq_compl hX j D hDne hclosed hD n hunit 2 le_rfl
  let E : Ext.{w} (moduleUnit U (ULift.{u + 1} (ZMod n))) (moduleRootsOfUnity U n) 2 ≃+
      Sheaf.H.{u + 2} (mu U n) 2 :=
    (etaleModuleExtCohomologyAddEquivLargeScalars U
      (constantRing U (ULift.{u + 1} (ZMod n))) (moduleRootsOfUnity U n) 2).trans
      (((Sheaf.functorH (Scheme.smallEtaleTopology U) 2).mapIso
        (moduleRootsOfUnityUnderlyingIso U n)).addCommGroupIsoToAddEquiv)
  exact E.injective.subsingleton

/-- For an actual isomorphism onto the proper curve, the degree-zero pairing is perfect. -/
theorem moduleDualityMap_unit_zero_isPerfPair_of_isIso [IsIso j] :
    (moduleDualityMap X hX D hfin hclosed j hD n hn hunit hinv
      (moduleUnit U (ULift.{u + 1} (ZMod n))) 0 (by decide)).IsPerfPair := by
  let : NeZero n := ⟨Nat.ne_of_gt hn⟩
  have := hX.isIntegral
  let L := moduleLowerShriek j (ULift.{u + 1} (ZMod n))
  let R := moduleInverseImage j (ULift.{u + 1} (ZMod n))
  have : R.IsEquivalence :=
    moduleInverseImage_isEquivalence_of_iso (ULift.{u + 1} (ZMod n)) (asIso j)
  have : L.IsEquivalence :=
    Adjunction.isEquivalence_left_of_isEquivalence_right
      (moduleLowerShriekAdjunction j (ULift.{u + 1} (ZMod n)))
  let e : L.obj (moduleUnit U (ULift.{u + 1} (ZMod n))) ≅
      moduleUnit X.left (ULift.{u + 1} (ZMod n)) :=
    L.mapIso (moduleUnitInverseImageIso j n).symm ≪≫
      asIso ((moduleLowerShriekAdjunction j (ULift.{u + 1} (ZMod n))).counit.app
        (moduleUnit X.left (ULift.{u + 1} (ZMod n))))
  let B := moduleDualityMap X hX D hfin hclosed j hD n hn hunit hinv
    (moduleUnit U (ULift.{u + 1} (ZMod n))) 0 (by decide)
  change B.IsPerfPair
  suffices hperf : B.flip.IsPerfPair from hperf.flip
  apply ZMod.isPerfPair_of_bijective_eval_generator n B.flip (Ext.mk₀ e.inv)
    (moduleUnitIsoScalarMap_bijective X.left n e.symm).surjective
  have : EnoughInjectives (ModuleSheaf U (ULift.{u + 1} (ZMod n))) :=
    SheafOfModules.enoughInjectivesLargeOverSmallScalars.{u + 1, u, 0, u + 1}
      (constantRing U (ULift.{u + 1} (ZMod n)))
  exact (moduleCompactSupportTraceAddEquiv X hX D hfin hclosed j hD n hn hunit hinv).bijective.comp
    (L.extPrecompMap_bijective_of_isEquivalence e.inv (moduleRootsOfUnity U n) 2)

/-- The original constant-coefficient pairing is perfect in compact-support degree zero. -/
theorem moduleDualityMap_unit_zero_isPerfPair :
    (moduleDualityMap X hX D hfin hclosed j hD n hn hunit hinv
      (moduleUnit U (ULift.{u + 1} (ZMod n))) 0 (by decide)).IsPerfPair := by
  classical
  by_cases hDne : D.Nonempty
  · let : NeZero n := ⟨Nat.ne_of_gt hn⟩
    have := subsingleton_moduleUnit_compactSupport_zero X hX D hfin hclosed j hD n hn hunit hDne
    have := subsingleton_moduleUnit_roots_two X hX D hclosed j hD n hunit hDne
    exact ZMod.isPerfPair_of_subsingleton n _
  · have hDe : D = ∅ := Set.not_nonempty_iff_eq_empty.mp hDne
    have : Surjective j := ⟨Set.range_eq_univ.mp (by simpa only [hDe, Set.compl_empty] using hD)⟩
    have : IsIso j :=
      (isIso_iff_isOpenImmersion_and_surjective j).mpr ⟨inferInstance, inferInstance⟩
    exact moduleDualityMap_unit_zero_isPerfPair_of_isIso X hX D hfin hclosed j hD n hn hunit hinv

/-- The original transposed degree-zero map is the other adjoint of degree-two perfectness. -/
theorem moduleDualityTransposeMap_unit_zero_isPerfPair :
    (moduleDualityTransposeMap X hX D hfin hclosed j hD n hn hunit hinv
      (moduleUnit U (ULift.{u + 1} (ZMod n))) 0 (by decide)).IsPerfPair :=
  (moduleDualityMap_unit_two_isPerfPair X hX D hfin hclosed j hD n hn hunit hinv).flip

/-- The original transposed degree-two map is the other adjoint of degree-zero perfectness. -/
theorem moduleDualityTransposeMap_unit_two_isPerfPair :
    (moduleDualityTransposeMap X hX D hfin hclosed j hD n hn hunit hinv
      (moduleUnit U (ULift.{u + 1} (ZMod n))) 2 le_rfl).IsPerfPair :=
  (moduleDualityMap_unit_zero_isPerfPair X hX D hfin hclosed j hD n hn hunit hinv).flip

end AlgebraicGeometry.Scheme.EtaleCohomology
