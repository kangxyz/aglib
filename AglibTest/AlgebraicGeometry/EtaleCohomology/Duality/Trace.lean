/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.Duality.Trace

/-! Public original-map interfaces and approved-axiom guards. -/

@[expose] public section

open CategoryTheory CategoryTheory.Abelian AlgebraicGeometry
open AlgebraicGeometry.Scheme AlgebraicGeometry.Scheme.OverField
open AlgebraicGeometry.Scheme.EtaleCohomology
open AlgebraicGeometry.Scheme.EtaleCohomology.Coefficients

attribute [local instance] hasSheafifyLarge

universe u w w'
variable {k : Type u} [Field k] [IsAlgClosed k] (X : FScheme k) (hX : Curve.Properties X)
  (D : Set X.left) (hfin : D.Finite) (hclosed : ∀ x ∈ D, IsClosed ({x} : Set X.left))
  {U : Scheme.{u}} (j : U ⟶ X.left) [IsOpenImmersion j] (hD : Set.range j = Dᶜ)
  (n : ℕ) (hn : 0 < n) (hunit : IsUnit (n : k)) (hinv : IsUnit (n : Γ(X.left, ⊤)))
  [HasExt.{w} (ModuleSheaf X.left (ULift.{u + 1} (ZMod n)))]
  [HasExt.{w'} (AbelianSheaf.{u, u + 1} X.left)]

/-- The module trace retains independent module and abelian Ext universes on original carriers. -/
example : Nonempty (Ext.{w} (moduleUnit X.left (ULift.{u + 1} (ZMod n)))
    ((moduleLowerShriek j (ULift.{u + 1} (ZMod n))).obj (moduleRootsOfUnity U n)) 2 ≃+ ZMod n) :=
  ⟨moduleCompactSupportTraceAddEquiv X hX D hfin hclosed j hD n hn hunit hinv⟩

attribute [local instance] moduleSheafExtZModModule

/-- The linear functional is precisely the constructed normalized additive trace. -/
example : (moduleCompactSupportTraceLinearMap X hX D hfin hclosed j hD n hn hunit
    hinv).toAddMonoidHom =
      (moduleCompactSupportTraceAddEquiv X hX D hfin hclosed j hD n hn hunit
        hinv).toAddMonoidHom :=
  moduleCompactSupportTraceLinearMap_toAddMonoidHom X hX D hfin hclosed j hD n hn hunit hinv

/-- The smaller-open map square uses only Ext on the fixed compactification. -/
example {V : Scheme.{u}} (i : V ⟶ U) [IsOpenImmersion i]
    (E : Set X.left) (hEfin : E.Finite) (hEclosed : ∀ x ∈ E, IsClosed ({x} : Set X.left))
    (hE : Set.range (i ≫ j) = Eᶜ) :
    (moduleCompactSupportTraceAddEquiv X hX E hEfin hEclosed (i ≫ j) hE n hn hunit
      hinv).toAddMonoidHom.comp
        ((Ext.mk₀ ((moduleLowerShriek (i ≫ j) (ULift.{u + 1} (ZMod n))).map
          (moduleRootsOfUnityInverseImageIso i n hn
            (GroupCohomology.Kummer.CoefficientBaseChange.levelInvertible j n hinv)).hom)).postcomp
          (moduleUnit X.left (ULift.{u + 1} (ZMod n))) (add_zero 2)) =
      (moduleCompactSupportTraceAddEquiv X hX D hfin hclosed j hD n hn hunit
        hinv).toAddMonoidHom.comp
        ((Ext.mk₀ ((moduleLowerShriekCompIso (ULift.{u + 1} (ZMod n)) j i).hom.app
            ((moduleInverseImage i (ULift.{u + 1} (ZMod n))).obj (moduleRootsOfUnity U n)) ≫
          (moduleLowerShriek j (ULift.{u + 1} (ZMod n))).map
            ((moduleLowerShriekAdjunction i (ULift.{u + 1} (ZMod n))).counit.app
              (moduleRootsOfUnity U n)))).postcomp
                (moduleUnit X.left (ULift.{u + 1} (ZMod n))) (add_zero 2)) :=
  moduleCompactSupportTrace_restriction X hX D hfin hclosed j hD n hn hunit hinv
    i E hEfin hEclosed hE

/-- info: 'AlgebraicGeometry.Scheme.EtaleCohomology.moduleRootsCounit_underlying' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms AlgebraicGeometry.Scheme.EtaleCohomology.moduleRootsCounit_underlying

/-- info: 'AlgebraicGeometry.Scheme.EtaleCohomology.moduleCompactSupportTraceAddEquiv' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms AlgebraicGeometry.Scheme.EtaleCohomology.moduleCompactSupportTraceAddEquiv

/-- info: 'AlgebraicGeometry.Scheme.EtaleCohomology.moduleCompactSupportTraceAddEquiv_toAddMonoidHom' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms AlgebraicGeometry.Scheme.EtaleCohomology.moduleCompactSupportTraceAddEquiv_toAddMonoidHom

/-- info: 'AlgebraicGeometry.Scheme.EtaleCohomology.moduleCompactSupportTraceAddEquiv_apply' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms AlgebraicGeometry.Scheme.EtaleCohomology.moduleCompactSupportTraceAddEquiv_apply

/-- info: 'AlgebraicGeometry.Scheme.EtaleCohomology.moduleCompactSupportTraceAddEquiv_counit' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms AlgebraicGeometry.Scheme.EtaleCohomology.moduleCompactSupportTraceAddEquiv_counit

/-- info: 'AlgebraicGeometry.Scheme.EtaleCohomology.moduleCompactSupportTraceAddEquiv_counit_apply' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms AlgebraicGeometry.Scheme.EtaleCohomology.moduleCompactSupportTraceAddEquiv_counit_apply

/-- info: 'AlgebraicGeometry.Scheme.EtaleCohomology.moduleCompactSupportTraceLinearMap' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms AlgebraicGeometry.Scheme.EtaleCohomology.moduleCompactSupportTraceLinearMap

/-- info: 'AlgebraicGeometry.Scheme.EtaleCohomology.moduleCompactSupportTraceLinearMap_toAddMonoidHom' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms AlgebraicGeometry.Scheme.EtaleCohomology.moduleCompactSupportTraceLinearMap_toAddMonoidHom

/-- info: 'AlgebraicGeometry.Scheme.EtaleCohomology.moduleCompactSupportTrace_restriction' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms AlgebraicGeometry.Scheme.EtaleCohomology.moduleCompactSupportTrace_restriction

/-- info: 'AlgebraicGeometry.Scheme.EtaleCohomology.compactSupportTrace_restriction' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms AlgebraicGeometry.Scheme.EtaleCohomology.compactSupportTrace_restriction
