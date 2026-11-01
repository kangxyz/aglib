/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.Duality.PointPurity.Finite

/-! # Actual finite supported source, original SUM operator and empty support -/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian AlgebraicGeometry
open AlgebraicGeometry.Scheme AlgebraicGeometry.Scheme.OverField
open AlgebraicGeometry.Scheme.EtaleCohomology
open AlgebraicGeometry.Scheme.EtaleCohomology.Coefficients
open AlgebraicGeometry.Scheme.EtaleCohomology.Curves.FiniteClosedSupport

universe u wM wA

attribute [local instance] hasSheafifyLarge hasSheafifyModules Abelian.hasFiniteBiproducts

section Source

variable (X : Scheme.{u}) (D : Set X) [Finite D]
  (hclosed : ∀ x ∈ D, IsClosed ({x} : Set X)) (n : ℕ)

example : modulePointUnitMap (inclusion X D) n ≫
    (moduleFinitePointSourceIso X D n hclosed).hom =
      biproduct.lift (fun x : D => modulePointUnitMap (X.fromSpecResidueField x.val) n) :=
  moduleFinitePointSourceIso_unit X D n hclosed

variable [HasExt.{wM} (ModuleSheaf X (ULift.{u + 1} (ZMod n)))]

example (N : ModuleSheaf X (ULift.{u + 1} (ZMod n))) (q : ℕ) :
    Ext.{wM} (moduleFinitePointSource X D n) N q ≃+
      ∀ x : D, Ext.{wM}
        ((moduleDirectImage (X.fromSpecResidueField x.val) (ULift.{u + 1} (ZMod n))).obj
          (moduleUnit (Spec (X.residueField x.val)) (ULift.{u + 1} (ZMod n)))) N q :=
  moduleFinitePointExtAddEquiv X D n hclosed N q

example {N N' : ModuleSheaf X (ULift.{u + 1} (ZMod n))} (b : N ⟶ N') (q : ℕ)
    (e : Ext.{wM} (moduleFinitePointSource X D n) N q) :
    moduleFinitePointExtAddEquiv X D n hclosed N' q (e.comp (Ext.mk₀ b) (add_zero q)) =
      fun x => (moduleFinitePointExtAddEquiv X D n hclosed N q e x).comp
        (Ext.mk₀ b) (add_zero q) :=
  moduleFinitePointExtAddEquiv_naturality X D n hclosed b q e

variable [HasExt.{wA} (AbelianSheaf.{u, u + 1} X)]

example (q : ℕ)
    (e : Ext.{wM} (moduleFinitePointSource X D n) (moduleRootsOfUnity X n) q) :
    letI : Fintype D := Fintype.ofFinite D
    modulePointExtToCohomology (inclusion X D) n q e =
      ∑ x : D, modulePointExtToCohomology (X.fromSpecResidueField x.val) n q
        (moduleFinitePointExtAddEquiv X D n hclosed (moduleRootsOfUnity X n) q e x) := by
  classical
  let : Fintype D := Fintype.ofFinite D
  have h := moduleFinitePointExtToCohomology_eq_sum X D n hclosed q
  have he := DFunLike.congr_fun h e
  simpa only [AddMonoidHom.finsetSum_apply, AddMonoidHom.comp_apply,
    Pi.evalAddMonoidHom_apply, AddEquiv.coe_toAddMonoidHom] using he

end Source

section Proper

variable {k : Type u} [Field k] [IsAlgClosed k] {C : FScheme k}
  (hC : Curve.Properties C) (D : Set C.left) [Finite D]
  (hclosed : ∀ x ∈ D, IsClosed ({x} : Set C.left))
  (n : ℕ) (hn : 0 < n) (hunit : IsUnit (n : k))
  [HasExt.{wM} (ModuleSheaf C.left (ULift.{u + 1} (ZMod n)))]
  [HasExt.{wA} (AbelianSheaf.{u, u + 1} C.left)]

example : Ext.{wM} (moduleFinitePointSource C.left D n) (moduleRootsOfUnity C.left n) 2 ≃+
    (D → ZMod n) := moduleFinitePointPurityAddEquiv hC D hclosed n hn hunit

example (e : Ext.{wM} (moduleFinitePointSource C.left D n) (moduleRootsOfUnity C.left n) 2) :
    letI : Fintype D := Fintype.ofFinite D
    Curves.traceAddEquiv hC n hn hunit (modulePoint_globalLevelInvertible n hunit)
        (modulePointExtToCohomology (inclusion C.left D) n 2 e) =
      ∑ x : D, moduleFinitePointPurityAddEquiv hC D hclosed n hn hunit e x :=
  moduleFinitePointPurityAddEquiv_trace hC D hclosed n hn hunit e

example (q : ℕ) (hq : q ≠ 2) :
    Subsingleton (Ext.{wM} (moduleFinitePointSource C.left D n) (moduleRootsOfUnity C.left n) q) :=
  moduleFinitePointExt_subsingleton hC D hclosed n hn hunit q hq

example : Subsingleton (Ext.{wM}
    (moduleFinitePointSource C.left (∅ : Set C.left) n) (moduleRootsOfUnity C.left n) 2) :=
  (moduleFinitePointPurityAddEquiv hC (∅ : Set C.left) (by simp) n hn hunit).injective.subsingleton

example (e : Ext.{wM} (moduleFinitePointSource C.left (∅ : Set C.left) n)
    (moduleRootsOfUnity C.left n) 2) :
    Curves.traceAddEquiv hC n hn hunit (modulePoint_globalLevelInvertible n hunit)
        (modulePointExtToCohomology (inclusion C.left (∅ : Set C.left)) n 2 e) = 0 := by
  simpa using moduleFinitePointPurityAddEquiv_trace hC (∅ : Set C.left) (by simp) n hn hunit e

end Proper

/--
info: 'AlgebraicGeometry.Scheme.EtaleCohomology.moduleFinitePointSourceIso' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms AlgebraicGeometry.Scheme.EtaleCohomology.moduleFinitePointSourceIso

/--
info: 'AlgebraicGeometry.Scheme.EtaleCohomology.moduleFinitePointExtAddEquiv' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms AlgebraicGeometry.Scheme.EtaleCohomology.moduleFinitePointExtAddEquiv

/--
info: 'AlgebraicGeometry.Scheme.EtaleCohomology.moduleFinitePointPurityAddEquiv_trace' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms AlgebraicGeometry.Scheme.EtaleCohomology.moduleFinitePointPurityAddEquiv_trace

/--
info: 'AlgebraicGeometry.Scheme.EtaleCohomology.moduleFinitePointExt_subsingleton' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms AlgebraicGeometry.Scheme.EtaleCohomology.moduleFinitePointExt_subsingleton
