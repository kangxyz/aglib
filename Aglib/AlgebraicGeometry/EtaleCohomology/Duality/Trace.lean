/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.Duality.LowerShriekCohomology
public import Aglib.AlgebraicGeometry.EtaleCohomology.Exceptional.Open.ModuleUnderlyingComposition
public import Aglib.AlgebraicGeometry.EtaleCohomology.Kummer.ModuleRootsComposition
public import Aglib.AlgebraicGeometry.EtaleCohomology.CompactSupport.RootsComposition
public import Aglib.AlgebraicGeometry.EtaleCohomology.Duality.ZModLinear
public import Aglib.AlgebraicGeometry.EtaleCohomology.Kummer.RootsOfUnityInverseImage
public import Aglib.AlgebraicGeometry.EtaleCohomology.CurveCohomology.CompactSupportTrace

/-!
# The normalized module compact-support trace

For a smooth proper geometrically connected curve over an algebraically closed field, and
an open complement of finitely many closed points, the original module Ext in degree two
is identified with `ZMod n` for positive invertible `n`. The map uses the existing module to
abelian cohomology comparison, the original roots coefficient isomorphism, and the trace
normalized to Aglib's Kummer boundary. Independent Ext universes are retained.

This supplies the trace functional needed by Milne, Lectures on Étale Cohomology v2.21,
Theorem 14.7, Step 2, p. 94. No comparison with the torsor/connecting-map signs of SGA,
perfectness, purity or change of compactification is asserted.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian AlgebraicGeometry
open GroupCohomology.Kummer.Coefficients GroupCohomology.Kummer.CoefficientBaseChange

namespace AlgebraicGeometry.Scheme.EtaleCohomology

open Coefficients Scheme.OverField

universe u w w'

attribute [local instance] hasSheafifyLarge hasSheafifyModules
  CategoryTheory.TorsionZMod.Ringed.abWEqualsLocallyBijectiveStandard


section RootCounit

variable {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j]
  (n : ℕ) (hn : 0 < n) (hinv : IsUnit (n : Γ(X, ⊤)))

/-- The actual module roots counit is the original abelian roots extension map underneath. -/
theorem moduleRootsCounit_underlying :
    (SheafOfModules.toSheaf (constantRing X (ULift.{u + 1} (ZMod n)))).map
        ((moduleLowerShriek j (ULift.{u + 1} (ZMod n))).map
            (moduleRootsOfUnityInverseImageIso j n hn hinv).inv ≫
          (moduleLowerShriekAdjunction j (ULift.{u + 1} (ZMod n))).counit.app
            (moduleRootsOfUnity X n)) ≫ (moduleRootsOfUnityUnderlyingIso X n).hom =
      (moduleLowerShriekUnderlyingIso j (ULift.{u + 1} (ZMod n))).hom.app
          (moduleRootsOfUnity U n) ≫
        (etaleLowerShriek j).map (moduleRootsOfUnityUnderlyingIso U n).hom ≫
          CompactSupport.rootsExtensionMap j n hn hinv :=
  Adjunction.underlying_coefficient_counit
    (moduleLowerShriekAdjunction j (ULift.{u + 1} (ZMod n))) (etaleLowerShriekAdjunction j)
    (moduleLowerShriekUnderlyingIso j (ULift.{u + 1} (ZMod n)))
    (moduleInverseImageUnderlyingIso (ULift.{u + 1} (ZMod n)) j)
    (mate_moduleLowerShriekUnderlyingIso_inv j (ULift.{u + 1} (ZMod n)))
    (moduleRootsOfUnityInverseImageIso j n hn hinv) (rootsPullbackIso j n hn hinv)
    (moduleRootsOfUnityUnderlyingIso X n) (moduleRootsOfUnityUnderlyingIso U n)
    (moduleRootsOfUnityInverseImageIso_underlying j n hn hinv)

end RootCounit

variable {k : Type u} [Field k] [IsAlgClosed k] (X : FScheme k) (hX : Curve.Properties X)
  (D : Set X.left) (hfin : D.Finite) (hclosed : ∀ x ∈ D, IsClosed ({x} : Set X.left))
  {U : Scheme.{u}} (j : U ⟶ X.left) [IsOpenImmersion j] (hD : Set.range j = Dᶜ)
  (n : ℕ) (hn : 0 < n) (hunit : IsUnit (n : k)) (hinv : IsUnit (n : Γ(X.left, ⊤)))
  [HasExt.{w} (ModuleSheaf X.left (ULift.{u + 1} (ZMod n)))]
  [HasExt.{w'} (AbelianSheaf.{u, u + 1} X.left)]

/-- The trace on the actual unit-module Ext with the original module lower shriek. -/
def moduleCompactSupportTraceAddEquiv :
    Ext.{w} (moduleUnit X.left (ULift.{u + 1} (ZMod n)))
      ((moduleLowerShriek j (ULift.{u + 1} (ZMod n))).obj (moduleRootsOfUnity U n)) 2 ≃+
        ZMod n :=
  (moduleLowerShriekCohomologyAddEquiv j (ULift.{u + 1} (ZMod n))
    (moduleRootsOfUnity U n) 2).trans
    (((CompactSupport.functor j 2).mapIso
      (moduleRootsOfUnityUnderlyingIso U n)).addCommGroupIsoToAddEquiv.trans
        (Curves.compactSupportTraceAddEquiv X hX D hfin hclosed j hD n hn hunit hinv))

/-- The whole trace map is the original module/abelian comparison followed by abelian trace. -/
theorem moduleCompactSupportTraceAddEquiv_toAddMonoidHom :
    (moduleCompactSupportTraceAddEquiv X hX D hfin hclosed j hD n hn hunit
      hinv).toAddMonoidHom =
      (Curves.compactSupportTraceAddEquiv X hX D hfin hclosed j hD n hn hunit
        hinv).toAddMonoidHom.comp
          ((CompactSupport.H.map j (moduleRootsOfUnityUnderlyingIso U n).hom 2).comp
            (moduleLowerShriekCohomologyAddEquiv j (ULift.{u + 1} (ZMod n))
              (moduleRootsOfUnity U n) 2).toAddMonoidHom) := rfl

/-- Evaluation of the whole trace correspondence on original module Ext. -/
theorem moduleCompactSupportTraceAddEquiv_apply
    (c : Ext.{w} (moduleUnit X.left (ULift.{u + 1} (ZMod n)))
      ((moduleLowerShriek j (ULift.{u + 1} (ZMod n))).obj (moduleRootsOfUnity U n)) 2) :
    moduleCompactSupportTraceAddEquiv X hX D hfin hclosed j hD n hn hunit hinv c =
      Curves.compactSupportTraceAddEquiv X hX D hfin hclosed j hD n hn hunit hinv
        (CompactSupport.H.map j (moduleRootsOfUnityUnderlyingIso U n).hom 2
          (moduleLowerShriekCohomologyAddEquiv j (ULift.{u + 1} (ZMod n))
            (moduleRootsOfUnity U n) 2 c)) :=
  DFunLike.congr_fun
    (moduleCompactSupportTraceAddEquiv_toAddMonoidHom X hX D hfin hclosed j hD n hn hunit hinv) c


/-- The whole module trace is the same normalized proper trace after the original module counit. -/
theorem moduleCompactSupportTraceAddEquiv_counit :
    (moduleCompactSupportTraceAddEquiv X hX D hfin hclosed j hD n hn hunit
      hinv).toAddMonoidHom =
      (Curves.traceAddEquiv hX n hn hunit hinv).toAddMonoidHom.comp
        ((Sheaf.H.map (moduleRootsOfUnityUnderlyingIso X.left n).hom 2).comp
          ((etaleModuleExtCohomologyAddEquivLargeScalars X.left
            (constantRing X.left (ULift.{u + 1} (ZMod n)))
            (moduleRootsOfUnity X.left n) 2).toAddMonoidHom.comp
            ((Ext.mk₀ ((moduleLowerShriek j (ULift.{u + 1} (ZMod n))).map
                (moduleRootsOfUnityInverseImageIso j n hn hinv).inv ≫
              (moduleLowerShriekAdjunction j (ULift.{u + 1} (ZMod n))).counit.app
                (moduleRootsOfUnity X.left n))).postcomp
              (moduleUnit X.left (ULift.{u + 1} (ZMod n))) (add_zero 2)))) := by
  apply AddMonoidHom.ext
  intro c
  change moduleCompactSupportTraceAddEquiv X hX D hfin hclosed j hD n hn hunit hinv c =
    Curves.traceAddEquiv hX n hn hunit hinv
      (Sheaf.H.map (moduleRootsOfUnityUnderlyingIso X.left n).hom 2
        (etaleModuleExtCohomologyAddEquivLargeScalars X.left
          (constantRing X.left (ULift.{u + 1} (ZMod n))) (moduleRootsOfUnity X.left n) 2
          (c.comp (Ext.mk₀ ((moduleLowerShriek j (ULift.{u + 1} (ZMod n))).map
            (moduleRootsOfUnityInverseImageIso j n hn hinv).inv ≫
              (moduleLowerShriekAdjunction j (ULift.{u + 1} (ZMod n))).counit.app
                (moduleRootsOfUnity X.left n))) (add_zero 2))))
  rw [moduleCompactSupportTraceAddEquiv_apply, Curves.compactSupportTraceAddEquiv_apply,
    CompactSupport.H.map_apply, moduleLowerShriekCohomologyAddEquiv_apply,
    moduleUnitExtAddEquiv_naturality]
  change Curves.traceAddEquiv hX n hn hunit hinv
      (Sheaf.H.map (CompactSupport.rootsExtensionMap j n hn hinv) 2
        (Sheaf.H.map ((etaleLowerShriek j).map (moduleRootsOfUnityUnderlyingIso U n).hom) 2
          (Sheaf.H.map ((moduleLowerShriekUnderlyingIso j
            (ULift.{u + 1} (ZMod n))).hom.app (moduleRootsOfUnity U n)) 2 _))) = _
  rw [← Sheaf.H.map_comp_apply, ← Sheaf.H.map_comp_apply, ← Sheaf.H.map_comp_apply,
    ← moduleRootsCounit_underlying j n hn hinv]

/-- Evaluation of the whole proper-trace normalization of the module counit. -/
theorem moduleCompactSupportTraceAddEquiv_counit_apply
    (c : Ext.{w} (moduleUnit X.left (ULift.{u + 1} (ZMod n)))
      ((moduleLowerShriek j (ULift.{u + 1} (ZMod n))).obj (moduleRootsOfUnity U n)) 2) :
    moduleCompactSupportTraceAddEquiv X hX D hfin hclosed j hD n hn hunit hinv c =
      Curves.traceAddEquiv hX n hn hunit hinv
        (Sheaf.H.map (moduleRootsOfUnityUnderlyingIso X.left n).hom 2
          (etaleModuleExtCohomologyAddEquivLargeScalars X.left
            (constantRing X.left (ULift.{u + 1} (ZMod n))) (moduleRootsOfUnity X.left n) 2
            (c.comp (Ext.mk₀ ((moduleLowerShriek j (ULift.{u + 1} (ZMod n))).map
              (moduleRootsOfUnityInverseImageIso j n hn hinv).inv ≫
                (moduleLowerShriekAdjunction j (ULift.{u + 1} (ZMod n))).counit.app
                  (moduleRootsOfUnity X.left n))) (add_zero 2)))) :=
  DFunLike.congr_fun
    (moduleCompactSupportTraceAddEquiv_counit X hX D hfin hclosed j hD n hn hunit hinv) c

attribute [local instance] moduleSheafExtZModModule

/-- The normalized trace as a linear functional for the existing canonical `ZMod n` action. -/
def moduleCompactSupportTraceLinearMap :
    Ext.{w} (moduleUnit X.left (ULift.{u + 1} (ZMod n)))
      ((moduleLowerShriek j (ULift.{u + 1} (ZMod n))).obj (moduleRootsOfUnity U n)) 2 →ₗ[ZMod n]
        ZMod n :=
  AddMonoidHom.toZModLinearMap n
    (moduleCompactSupportTraceAddEquiv X hX D hfin hclosed j hD n hn hunit hinv).toAddMonoidHom

/-- The linear trace has exactly the original additive trace map. -/
theorem moduleCompactSupportTraceLinearMap_toAddMonoidHom :
    (moduleCompactSupportTraceLinearMap X hX D hfin hclosed j hD n hn hunit
      hinv).toAddMonoidHom =
      (moduleCompactSupportTraceAddEquiv X hX D hfin hclosed j hD n hn hunit
        hinv).toAddMonoidHom := rfl


section Shrinking

variable {V : Scheme.{u}} (i : V ⟶ U) [IsOpenImmersion i]
  (E : Set X.left) (hEfin : E.Finite) (hEclosed : ∀ x ∈ E, IsClosed ({x} : Set X.left))
  (hE : Set.range (i ≫ j) = Eᶜ)

omit [HasExt.{w} (ModuleSheaf X.left (ULift.{u + 1} (ZMod n)))] in
/-- The original abelian compact-support trace commutes with the original smaller-open extension. -/
theorem compactSupportTrace_restriction :
    (Curves.compactSupportTraceAddEquiv X hX E hEfin hEclosed (i ≫ j) hE n hn hunit
      hinv).toAddMonoidHom.comp
        (CompactSupport.H.map (i ≫ j)
          (rootsPullbackIso i n hn (levelInvertible j n hinv)).hom 2) =
      (Curves.compactSupportTraceAddEquiv X hX D hfin hclosed j hD n hn hunit
        hinv).toAddMonoidHom.comp (CompactSupport.extensionCohomologyMap i j (mu U n) 2) := by
  apply AddMonoidHom.ext
  intro x
  change Curves.compactSupportTraceAddEquiv X hX E hEfin hEclosed (i ≫ j) hE n hn hunit hinv
    (CompactSupport.H.map (i ≫ j)
      (rootsPullbackIso i n hn (levelInvertible j n hinv)).hom 2 x) =
    Curves.compactSupportTraceAddEquiv X hX D hfin hclosed j hD n hn hunit hinv
      (CompactSupport.extensionCohomologyMap i j (mu U n) 2 x)
  rw [Curves.compactSupportTraceAddEquiv_apply, Curves.compactSupportTraceAddEquiv_apply]
  exact congrArg (Curves.traceAddEquiv hX n hn hunit hinv)
    (DFunLike.congr_fun (CompactSupport.rootsMap_extension j i n hn hinv 2) x)

/-- The whole normalized trace square for a smaller open, on the original module extension map. -/
theorem moduleCompactSupportTrace_restriction :
    (moduleCompactSupportTraceAddEquiv X hX E hEfin hEclosed (i ≫ j) hE n hn hunit
      hinv).toAddMonoidHom.comp
        ((Ext.mk₀ ((moduleLowerShriek (i ≫ j) (ULift.{u + 1} (ZMod n))).map
          (moduleRootsOfUnityInverseImageIso i n hn (levelInvertible j n hinv)).hom)).postcomp
          (moduleUnit X.left (ULift.{u + 1} (ZMod n))) (add_zero 2)) =
      (moduleCompactSupportTraceAddEquiv X hX D hfin hclosed j hD n hn hunit
        hinv).toAddMonoidHom.comp
        ((Ext.mk₀ ((moduleLowerShriekCompIso (ULift.{u + 1} (ZMod n)) j i).hom.app
            ((moduleInverseImage i (ULift.{u + 1} (ZMod n))).obj (moduleRootsOfUnity U n)) ≫
          (moduleLowerShriek j (ULift.{u + 1} (ZMod n))).map
            ((moduleLowerShriekAdjunction i (ULift.{u + 1} (ZMod n))).counit.app
              (moduleRootsOfUnity U n)))).postcomp
                (moduleUnit X.left (ULift.{u + 1} (ZMod n))) (add_zero 2)) := by
  apply AddMonoidHom.ext
  intro c
  change moduleCompactSupportTraceAddEquiv X hX E hEfin hEclosed (i ≫ j) hE n hn hunit hinv
    (c.comp (Ext.mk₀ ((moduleLowerShriek (i ≫ j) (ULift.{u + 1} (ZMod n))).map
      (moduleRootsOfUnityInverseImageIso i n hn (levelInvertible j n hinv)).hom))
        (add_zero 2)) =
    moduleCompactSupportTraceAddEquiv X hX D hfin hclosed j hD n hn hunit hinv
      (c.comp (Ext.mk₀ ((moduleLowerShriekCompIso (ULift.{u + 1} (ZMod n)) j i).hom.app
        ((moduleInverseImage i (ULift.{u + 1} (ZMod n))).obj (moduleRootsOfUnity U n)) ≫
          (moduleLowerShriek j (ULift.{u + 1} (ZMod n))).map
            ((moduleLowerShriekAdjunction i (ULift.{u + 1} (ZMod n))).counit.app
              (moduleRootsOfUnity U n)))) (add_zero 2))
  rw [moduleCompactSupportTraceAddEquiv_counit_apply,
    moduleCompactSupportTraceAddEquiv_counit_apply]
  have h := Adjunction.coefficient_counit_extension
    (moduleLowerShriekAdjunction (i ≫ j) (ULift.{u + 1} (ZMod n)))
    (moduleLowerShriekAdjunction i (ULift.{u + 1} (ZMod n)))
    (moduleLowerShriekAdjunction j (ULift.{u + 1} (ZMod n)))
    (moduleInverseImageCompIso (ULift.{u + 1} (ZMod n)) j i)
    (moduleRootsOfUnityInverseImageIso j n hn hinv)
    (moduleRootsOfUnityInverseImageIso i n hn (levelInvertible j n hinv))
    (moduleRootsOfUnityInverseImageIso (i ≫ j) n hn hinv)
    (moduleRootsOfUnityInverseImageIso_comp j i n hn hinv)
  simp only [Ext.comp_assoc_of_third_deg_zero, Ext.mk₀_comp_mk₀, Category.assoc]
  rw [h]
  rfl

end Shrinking

end AlgebraicGeometry.Scheme.EtaleCohomology
