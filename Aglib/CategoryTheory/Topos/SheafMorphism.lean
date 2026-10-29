/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.CategoryTheory.Topos.GeometricMorphism
public import Aglib.CategoryTheory.Functor.Sections.Initial
public import Mathlib.CategoryTheory.Sites.GlobalSections
public import Mathlib.CategoryTheory.Sites.Pullback

/-!
# Left-exact sheaf adjunctions and intrinsic global points

`GeometricMorphism E F` is native left-exact adjunction data with inverse
image from the actual category `F` to the actual category `E`. Its category
arguments retain independent object and Hom worlds. It has the geometric-
morphism interpretation when `E` and `F` are topoi. The `SheafMorphism`
namespace specializes these same data to the native sheaf categories, with
independent carrier worlds. No automatic topos existence claim is made for
arbitrary site and value universes: classifiers require the native essential-
smallness condition, and sheafification has its own hypotheses. There is one
package and no additional sheaf carrier. Site functors construct the data but
do not occur in its global-point law.

Global points are actual arrows from the native terminal sheaf, without a
terminal object of the site or an enough-points assumption. Native constant-
sheaf Gamma is compared only when its actual universe-level instances exist.
No ringed-module lifting of an arbitrary Set geometric morphism is asserted.
-/

@[expose] public noncomputable section

open CategoryTheory.Limits Opposite

namespace CategoryTheory.Topos

universe u v u' v' w wJ wK

variable {C : Type u} [Category.{v} C] {D : Type u'} [Category.{v'} D]
  {J : GrothendieckTopology C} {K : GrothendieckTopology D}

/-- The existing terminal sheaf, retaining the constant-singleton presheaf. -/
abbrev terminalSheaf (J : GrothendieckTopology C) : Sheaf J (Type w) :=
  Sheaf.terminal J (Types.isTerminalPUnit : IsTerminal (PUnit : Type w))

/-- The chosen sheaf is terminal independently of a terminal site object. -/
abbrev terminalSheafIsTerminal (J : GrothendieckTopology C) :
    IsTerminal (terminalSheaf J : Sheaf J (Type w)) :=
  Sheaf.isTerminalTerminal J Types.isTerminalPUnit

/-- Intrinsic global points are arrows in the original sheaf topos. -/
abbrev GlobalPoint (P : Sheaf J (Type w)) := terminalSheaf J ⟶ P

/-- The intrinsic global-point functor of the actual sheaf category. -/
abbrev globalPointsFunctor (J : GrothendieckTopology C) :
    Sheaf J (Type w) ⥤ Type (max u w) :=
  coyoneda.obj (op (terminalSheaf J))

namespace SheafMorphism

/-- Its inverse image is the same native left-adjoint functor. -/
abbrev inverseImage
    (f : GeometricMorphism (Sheaf K (Type wK)) (Sheaf J (Type wJ))) := f.left.obj

/-- Its direct image is the same native right-adjoint functor. -/
abbrev directImage
    (f : GeometricMorphism (Sheaf K (Type wK)) (Sheaf J (Type wJ))) := f.right

/-- Its unit and counit are the original native adjunction. -/
abbrev adjunction
    (f : GeometricMorphism (Sheaf K (Type wK)) (Sheaf J (Type wJ))) :
    inverseImage f ⊣ directImage f := f.adj

/-- A continuous site map supplies its native same-value-category realization.
The abstract sheaf-morphism interface keeps the two carrier worlds independent. -/
def ofSiteFunctor (F : C ⥤ D) (J : GrothendieckTopology C)
    (K : GrothendieckTopology D) [F.IsContinuous J K]
    [(F.sheafPushforwardContinuous (Type w) J K).IsRightAdjoint]
    [PreservesFiniteLimits (F.sheafPullback (Type w) J K)] :
    GeometricMorphism (Sheaf K (Type w)) (Sheaf J (Type w)) :=
  LeftExactAdjunction.ofAdjunction (F.sheafAdjunctionContinuous (Type w) J K)

@[simp]
theorem ofSiteFunctor_inverseImage (F : C ⥤ D) (J : GrothendieckTopology C)
    (K : GrothendieckTopology D) [F.IsContinuous J K]
    [(F.sheafPushforwardContinuous (Type w) J K).IsRightAdjoint]
    [PreservesFiniteLimits (F.sheafPullback (Type w) J K)] :
    inverseImage (ofSiteFunctor F J K) = F.sheafPullback (Type w) J K := rfl

@[simp]
theorem ofSiteFunctor_directImage (F : C ⥤ D) (J : GrothendieckTopology C)
    (K : GrothendieckTopology D) [F.IsContinuous J K]
    [(F.sheafPushforwardContinuous (Type w) J K).IsRightAdjoint]
    [PreservesFiniteLimits (F.sheafPullback (Type w) J K)] :
    directImage (ofSiteFunctor F J K) = F.sheafPushforwardContinuous (Type w) J K := rfl

/-- Direct image preserves global points through the actual left-exact sheaf adjunction. -/
def directImageGlobalPointEquiv
    (f : GeometricMorphism (Sheaf K (Type wK)) (Sheaf J (Type wJ)))
    (P : Sheaf K (Type wK)) : GlobalPoint ((directImage f).obj P) ≃ GlobalPoint P :=
  f.terminalHomEquiv (terminalSheafIsTerminal J) (terminalSheafIsTerminal K) P

end SheafMorphism

/-- A global point is the original compatible family, without choosing a site object. -/
def globalPointSectionsEquiv (P : Sheaf J (Type w)) : GlobalPoint P ≃ P.obj.sections where
  toFun s := (P.obj.sectionsEquivHom PUnit).symm s.hom
  invFun s := ⟨(P.obj.sectionsEquivHom PUnit) s⟩
  left_inv s := by
    apply Sheaf.hom_ext
    exact (P.obj.sectionsEquivHom PUnit).apply_symm_apply s.hom
  right_inv s := (P.obj.sectionsEquivHom PUnit).symm_apply_apply s

/-- The compatible family is evaluated on the original singleton section. -/
@[simp]
theorem globalPointSectionsEquiv_val (P : Sheaf J (Type w)) (s : GlobalPoint P) (U : Cᵒᵖ) :
    (globalPointSectionsEquiv P s).val U = s.hom.app U PUnit.unit := rfl

/-- Global-point transport is the original coefficient morphism. -/
theorem globalPointSectionsEquiv_naturality {P Q : Sheaf J (Type w)}
    (s : GlobalPoint P) (f : P ⟶ Q) :
    globalPointSectionsEquiv Q (s ≫ f) =
      (Functor.sectionsFunctor Cᵒᵖ).map f.hom (globalPointSectionsEquiv P s) := rfl

/-- Evaluation at a specified terminal site object is only a comparison of global points. -/
def globalPointTerminalEquiv {T : C} (hT : IsTerminal T) (P : Sheaf J (Type w)) :
    GlobalPoint P ≃ P.obj.obj (op T) :=
  (globalPointSectionsEquiv P).trans (P.obj.sectionsEquivOfIsInitial hT.op)

@[simp]
theorem globalPointTerminalEquiv_apply {T : C} (hT : IsTerminal T)
    (P : Sheaf J (Type w)) (s : GlobalPoint P) :
    globalPointTerminalEquiv hT P s = s.hom.app (op T) PUnit.unit := rfl

/-- The old terminal-section wrapper retains every original restriction map. -/
@[simp]
theorem globalPointTerminalEquiv_symm_app {T : C} (hT : IsTerminal T)
    (P : Sheaf J (Type w)) (s : P.obj.obj (op T)) (U : Cᵒᵖ) :
    ((globalPointTerminalEquiv hT P).symm s).hom.app U PUnit.unit =
      P.obj.map (hT.from U.unop).op s := rfl

section NativeGamma

variable [HasWeakSheafify J (Type w)] [HasGlobalSectionsFunctor J (Type w)]

/-- Native constant-sheaf Gamma is intrinsic global points in its actual available world. -/
def nativeGammaGlobalPointEquiv (P : Sheaf J (Type w)) :
    (Sheaf.Γ J (Type w)).obj P ≃ GlobalPoint P :=
  (Sheaf.ΓObjEquivSections J P).trans (globalPointSectionsEquiv P).symm

/-- The comparison keeps the original Gamma coefficient map. -/
theorem nativeGammaGlobalPointEquiv_naturality {P Q : Sheaf J (Type w)}
    (f : P ⟶ Q) (s : (Sheaf.Γ J (Type w)).obj P) :
    nativeGammaGlobalPointEquiv Q ((Sheaf.Γ J (Type w)).map f s) =
      nativeGammaGlobalPointEquiv P s ≫ f := by
  apply (globalPointSectionsEquiv Q).injective
  rw [globalPointSectionsEquiv_naturality]
  simp only [nativeGammaGlobalPointEquiv, Equiv.trans_apply, Equiv.apply_symm_apply]
  exact Sheaf.ΓObjEquivSections_naturality J f s

end NativeGamma
end CategoryTheory.Topos
