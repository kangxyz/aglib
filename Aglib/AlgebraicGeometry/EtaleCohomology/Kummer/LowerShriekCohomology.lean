/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.Kummer.ModuleCohomology
public import Aglib.AlgebraicGeometry.EtaleCohomology.Exceptional.Open.LowerShriekExt

/-!
# Original lower-shriek source and roots cohomology

For an etale morphism, Ext from the original lower shriek of the inverse image
of the unit computes original roots cohomology. The actual counit becomes the
original roots restriction map. The module and abelian Ext worlds on the two
schemes remain independent. This extracts the same construction previously
private in point purity for its second consumer, open-curve cardinalities.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian
open GroupCohomology.Kummer.Coefficients

universe u wM wA wMU wAU

namespace AlgebraicGeometry.Scheme.EtaleCohomology

open Coefficients

attribute [local instance] hasSheafifyLarge hasSheafifyModules
  CategoryTheory.TorsionZMod.Ringed.abWEqualsLocallyBijectiveStandard

variable {X : Scheme.{u}} (n : ℕ)
  [HasExt.{wM} (ModuleSheaf X (ULift.{u + 1} (ZMod n)))]
  [HasExt.{wA} (AbelianSheaf.{u, u + 1} X)]

omit [HasExt.{wA} (AbelianSheaf.{u, u + 1} X)] in
/-- The original lower-shriek source computes roots cohomology through the
native Ext adjunction and the selected unit and roots transports. -/
def moduleLowerShriekRootsExtCohomologyAddEquiv
    {V : Scheme.{u}} (j : V ⟶ X) [Etale j] (hn : 0 < n)
    (hinv : IsUnit (n : Γ(X, ⊤)))
    [HasExt.{wMU} (ModuleSheaf V (ULift.{u + 1} (ZMod n)))]
    [HasExt.{wAU} (AbelianSheaf.{u, u + 1} V)] (q : ℕ) :
    Ext.{wM} ((moduleLowerShriek j (ULift.{u + 1} (ZMod n))).obj
        ((moduleInverseImage j (ULift.{u + 1} (ZMod n))).obj
          (moduleUnit X (ULift.{u + 1} (ZMod n))))) (moduleRootsOfUnity X n) q ≃+
      Sheaf.H.{wAU} (mu V n) q := by
  let Λ := ULift.{u + 1} (ZMod n)
  let R := moduleInverseImage j Λ
  let a := moduleUnitInverseImageIso j n
  let b := moduleRootsOfUnityInverseImageIso j n hn hinv
  let e₁ : Ext.{wMU} (R.obj (moduleUnit X Λ)) (R.obj (moduleRootsOfUnity X n)) q ≃+
      Ext.{wMU} (moduleUnit V Λ) (R.obj (moduleRootsOfUnity X n)) q :=
    (((CategoryTheory.Abelian.extFunctor q).mapIso a.symm.op).app
      (R.obj (moduleRootsOfUnity X n))).addCommGroupIsoToAddEquiv
  let e₂ : Ext.{wMU} (moduleUnit V Λ) (R.obj (moduleRootsOfUnity X n)) q ≃+
      Ext.{wMU} (moduleUnit V Λ) (moduleRootsOfUnity V n) q :=
    ((CategoryTheory.Abelian.extFunctorObj (moduleUnit V Λ) q).mapIso b).addCommGroupIsoToAddEquiv
  exact (moduleLowerShriekExtEquiv j Λ (R.obj (moduleUnit X Λ))
    (moduleRootsOfUnity X n) q).trans
      (e₁.trans (e₂.trans (moduleRootsUnitExtCohomologyAddEquiv V n q)))

omit [HasExt.{wA} (AbelianSheaf.{u, u + 1} X)] in
/-- The forward map retains the original Ext adjunction and both coefficient transports. -/
theorem moduleLowerShriekRootsExtCohomologyAddEquiv_apply
    {V : Scheme.{u}} (j : V ⟶ X) [Etale j] (hn : 0 < n)
    (hinv : IsUnit (n : Γ(X, ⊤)))
    [HasExt.{wMU} (ModuleSheaf V (ULift.{u + 1} (ZMod n)))]
    [HasExt.{wAU} (AbelianSheaf.{u, u + 1} V)] (q : ℕ)
    (e : Ext.{wM} ((moduleLowerShriek j (ULift.{u + 1} (ZMod n))).obj
      ((moduleInverseImage j (ULift.{u + 1} (ZMod n))).obj
        (moduleUnit X (ULift.{u + 1} (ZMod n))))) (moduleRootsOfUnity X n) q) :
    moduleLowerShriekRootsExtCohomologyAddEquiv (n := n) j hn hinv q e =
      moduleRootsUnitExtCohomologyAddEquiv V n q
        (((Ext.mk₀ (moduleUnitInverseImageIso j n).inv).comp
          (moduleLowerShriekExtEquiv j (ULift.{u + 1} (ZMod n))
            ((moduleInverseImage j (ULift.{u + 1} (ZMod n))).obj
              (moduleUnit X (ULift.{u + 1} (ZMod n))))
            (moduleRootsOfUnity X n) q e) (zero_add q)).comp
          (Ext.mk₀ (moduleRootsOfUnityInverseImageIso j n hn hinv).hom) (add_zero q)) := rfl

/-- The whole counit square is the original roots-cohomology restriction map. -/
theorem moduleLowerShriekRootsExtCohomologyAddEquiv_counit
    {V : Scheme.{u}} (j : V ⟶ X) [Etale j] (hn : 0 < n)
    (hinv : IsUnit (n : Γ(X, ⊤)))
    [HasExt.{wMU} (ModuleSheaf V (ULift.{u + 1} (ZMod n)))]
    [HasExt.{wAU} (AbelianSheaf.{u, u + 1} V)] (q : ℕ) :
    (moduleLowerShriekRootsExtCohomologyAddEquiv (n := n) j hn hinv q).toAddMonoidHom.comp
      ((Ext.mk₀
        ((moduleLowerShriekAdjunction j (ULift.{u + 1} (ZMod n))).counit.app
          (moduleUnit X (ULift.{u + 1} (ZMod n))))).precomp
            (moduleRootsOfUnity X n) (zero_add q)) =
    (Kummer.rootsCohomologyPullback j n hn hinv q).comp
      (moduleRootsUnitExtCohomologyAddEquiv X n q).toAddMonoidHom := by
  ext e
  change moduleLowerShriekRootsExtCohomologyAddEquiv (n := n) j hn hinv q
      ((Ext.mk₀
        ((moduleLowerShriekAdjunction j (ULift.{u + 1} (ZMod n))).counit.app
          (moduleUnit X (ULift.{u + 1} (ZMod n))))).comp e (zero_add q)) = _
  rw [moduleLowerShriekRootsExtCohomologyAddEquiv_apply]
  have hr : moduleLowerShriekExtEquiv j (ULift.{u + 1} (ZMod n))
      ((moduleInverseImage j (ULift.{u + 1} (ZMod n))).obj
        (moduleUnit X (ULift.{u + 1} (ZMod n)))) (moduleRootsOfUnity X n) q
      ((Ext.mk₀
        ((moduleLowerShriekAdjunction j (ULift.{u + 1} (ZMod n))).counit.app
          (moduleUnit X (ULift.{u + 1} (ZMod n))))).comp e (zero_add q)) =
      e.mapExactFunctor (moduleInverseImage j (ULift.{u + 1} (ZMod n))) :=
    Functor.extEquiv_mk₀_counit_comp (P := moduleLowerShriek j (ULift.{u + 1} (ZMod n)))
      (moduleLowerShriekAdjunction j (ULift.{u + 1} (ZMod n))) e
  rw [hr]
  exact DFunLike.congr_fun (moduleRootsUnitExtCohomologyPullback_square j n hn hinv q) e


end AlgebraicGeometry.Scheme.EtaleCohomology
