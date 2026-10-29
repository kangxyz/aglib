/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.Stalk.BaseChangeChartRelative

/-! # Target-local invertibility from the original relative exchange square

Three actual invertible exchanges on relative charts force invertibility of
the original target-restricted higher exchange. The argument retains the
literal inverse-image square comparisons. Its ordinary interface is intrinsic;
The compatibility companion retains all eight independent derived models.
No Cartesian or properness condition is needed for this cancellation.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

private theorem isIso_of_relative_exchange_square
    {C : Type*} [Category* C] {A B D E P Q : C}
    (l : A ⟶ B) (β : B ⟶ D) (v : D ⟶ E)
    (u : A ⟶ P) (r : P ⟶ Q) (t : Q ⟶ E)
    [IsIso l] [IsIso v] [IsIso u] [IsIso r] [IsIso t]
    (h : l ≫ β ≫ v = u ≫ r ≫ t) : IsIso β := by
  have hcomp : IsIso (l ≫ β ≫ v) :=
    h.symm ▸ (inferInstance : IsIso (u ≫ r ≫ t))
  have hβv : IsIso (β ≫ v) :=
    (isIso_comp_left_iff l (β ≫ v)).mp hcomp
  exact (isIso_comp_right_iff β v).mp hβv

namespace AlgebraicGeometry.Scheme.EtaleCohomology.Proper

universe u dX dS dX' dS' dZ dU dW dV

attribute [local instance] hasSheafifyLarge

section Ordinary

variable {X S X' S' Z U W V : Scheme.{u}}
  (f : X ⟶ S) (f' : X' ⟶ S') (g : S' ⟶ S) (g' : X' ⟶ X)
  (h : f' ≫ g = g' ≫ f)
  (fU : Z ⟶ U) (fV : W ⟶ V) (aU : U ⟶ S) (aV : V ⟶ S')
  (piU : Z ⟶ X) (piV : W ⟶ X') (b : V ⟶ U) (r : W ⟶ Z)
  (hU : fU ≫ aU = piU ≫ f) (hV : fV ≫ aV = piV ≫ f')
  (hb : aV ≫ g = b ≫ aU) (hr : piV ≫ g' = r ≫ piU)
  (hR : fV ≫ b = r ≫ fU)


include hb hr in
/-- If the two chart exchanges and their relative exchange are invertible,
then the actual original higher exchange is invertible after inverse image
to the target chart. Every comparison is the original native map. -/
theorem higherBaseChangeMap_inverseImage_isIso_of_chartRelative
    (q : ℕ) (F : AbelianSheaf.{u, u + 1} X)
    [IsIso ((higherBaseChangeMap f fU aU piU hU q).app F)]
    [IsIso ((higherBaseChangeMap f' fV aV piV hV q).app ((inverseImage g').obj F))]
    [IsIso ((higherBaseChangeMap fU fV b r hR q).app ((inverseImage piU).obj F))] :
    IsIso ((inverseImage aV).map ((higherBaseChangeMap f f' g g' h q).app F)) :=
  isIso_of_relative_exchange_square
    ((inverseImageSquareIso aU aV g b hb).inv.app ((higherDirectImage f q).obj F))
    ((inverseImage aV).map ((higherBaseChangeMap f f' g g' h q).app F))
    ((higherBaseChangeMap f' fV aV piV hV q).app ((inverseImage g').obj F))
    ((inverseImage b).map ((higherBaseChangeMap f fU aU piU hU q).app F))
    ((higherBaseChangeMap fU fV b r hR q).app ((inverseImage piU).obj F))
    ((higherDirectImage fV q).map ((inverseImageSquareIso piU piV g' r hr).inv.app F))
    (higherBaseChangeMap_chartRelative_square
      f f' g g' h fU fV aU aV piU piV b r hU hV hb hr hR q F)

end Ordinary

section SelectedModels

variable {X S X' S' Z U W V : Scheme.{u}}
  [HasDerivedCategory.{dX} (AbelianSheaf.{u, u + 1} X)]
  [HasDerivedCategory.{dS} (AbelianSheaf.{u, u + 1} S)]
  [HasDerivedCategory.{dX'} (AbelianSheaf.{u, u + 1} X')]
  [HasDerivedCategory.{dS'} (AbelianSheaf.{u, u + 1} S')]
  [HasDerivedCategory.{dZ} (AbelianSheaf.{u, u + 1} Z)]
  [HasDerivedCategory.{dU} (AbelianSheaf.{u, u + 1} U)]
  [HasDerivedCategory.{dW} (AbelianSheaf.{u, u + 1} W)]
  [HasDerivedCategory.{dV} (AbelianSheaf.{u, u + 1} V)]
  (f : X ⟶ S) (f' : X' ⟶ S') (g : S' ⟶ S) (g' : X' ⟶ X)
  (h : f' ≫ g = g' ≫ f)
  (fU : Z ⟶ U) (fV : W ⟶ V) (aU : U ⟶ S) (aV : V ⟶ S')
  (piU : Z ⟶ X) (piV : W ⟶ X') (b : V ⟶ U) (r : W ⟶ Z)
  (hU : fU ≫ aU = piU ≫ f) (hV : fV ≫ aV = piV ≫ f')
  (hb : aV ≫ g = b ≫ aU) (hr : piV ≫ g' = r ≫ piU)
  (hR : fV ≫ b = r ≫ fU)


include hb hr in
/-- Relative cancellation for the original chart transports in eight independent models. -/
theorem higherBaseChangeMapFromDerived_inverseImage_isIso_of_chartRelative
    (q : ℕ) (F : AbelianSheaf.{u, u + 1} X)
    [IsIso ((higherBaseChangeMapFromDerived f fU aU piU hU q).app F)]
    [IsIso ((higherBaseChangeMapFromDerived f' fV aV piV hV q).app ((inverseImage g').obj F))]
    [IsIso ((higherBaseChangeMapFromDerived fU fV b r hR q).app ((inverseImage piU).obj F))] :
    IsIso ((inverseImage aV).map ((higherBaseChangeMapFromDerived f f' g g' h q).app F)) := by
  simp only [higherBaseChangeMapFromDerived_eq] at *
  exact higherBaseChangeMap_inverseImage_isIso_of_chartRelative
    f f' g g' h fU fV aU aV piU piV b r hU hV hb hr hR q F

end SelectedModels

end AlgebraicGeometry.Scheme.EtaleCohomology.Proper
