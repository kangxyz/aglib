/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Modules.Tensor.Restriction
public import Aglib.Algebra.Category.ModuleCat.Sheaf.TensorPushforwardMap
public import Aglib.Algebra.Category.ModuleCat.Sheaf.Tensor.RightUnit

/-!
Source: `Quillen/AlgebraicGeometry/Scheme/Sheaf/TensorSections.lean` at LOCAL Quillen
`189a8e779f0c68b2dfc6f8195daebb3e684a5905`. Selection: whole_general_prerequisite;
source ranges [[1, 66]]. Actual objects, maps and hypotheses are preserved.
-/

/-!
# Tensor sections on a scheme

Original tensor sections detect morphisms and preserve literal coefficient,
module and open-restriction maps. The original left and right tensor unitors
send a pure section with a structure-sheaf factor to scalar multiplication
(`tensorLeftUnitIso_hom_section`, `tensorRightUnitIso_hom_section`).
-/

@[expose] public section
noncomputable section

section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
open CategoryTheory CategoryTheory.MonoidalCategory AlgebraicGeometry Opposite
  SheafOfModulesOfCommRing
open AlgebraicGeometry.Scheme.Modules

namespace AlgebraicGeometry.Scheme.Modules
/-- The original pure-tensor section followed by module sheafification. -/
def moduleTensorSection (X : Scheme.{u}) (E M : X.Modules) (U : X.Opens)
    (e : Γ(E, U)) (m : Γ(M, U)) : Γ((moduleTensorLeftFunctor X E).obj M, U) :=
  SheafOfModulesOfCommRing.tensorSection X.sheaf E M (op U) e m
/-- Original tensor generators determine a sheaf morphism. -/
theorem moduleTensor_hom_ext {X : Scheme.{u}} {E M N : X.Modules}
    {f g : (moduleTensorLeftFunctor X E).obj M ⟶ N}
    (h : ∀ (U : X.Opens) (e : Γ(E, U)) (m : Γ(M, U)),
      f.app U (moduleTensorSection X E M U e m) =
        g.app U (moduleTensorSection X E M U e m)) : f = g :=
  SheafOfModulesOfCommRing.tensor_hom_ext X.sheaf (fun U => h U.unop)
/-- Tensor generators retain the literal sheaf restriction maps. -/
theorem moduleTensorSection_restrict {X : Scheme.{u}} (E M : X.Modules)
    {U V : X.Opens} (i : U ⟶ V) (e : Γ(E, V)) (m : Γ(M, V)) :
    ((moduleTensorLeftFunctor X E).obj M).presheaf.map i.op
        (moduleTensorSection X E M V e m) =
      moduleTensorSection X E M U (E.presheaf.map i.op e) (M.presheaf.map i.op m) :=
  SheafOfModulesOfCommRing.tensorSection_naturality X.sheaf E M i.op e m
/-- Coefficient arrows act on the first original tensor generator. -/
theorem moduleTensorCoefficientMap_section {X : Scheme.{u}} {E E' : X.Modules}
    (f : E ⟶ E') (M : X.Modules) (U : X.Opens) (e : Γ(E, U)) (m : Γ(M, U)) :
    ((moduleTensorCoefficientMap X f).app M).app U (moduleTensorSection X E M U e m) =
      moduleTensorSection X E' M U (f.app U e) m := by
  exact SheafOfModulesOfCommRing.tensor_map_tensorSection X.sheaf f
    (𝟙 (show SheafOfModulesOfCommRing.{u} X.sheaf from M)) (op U) e m
/-- Module arrows act on the second original tensor generator. -/
theorem moduleTensorLeftFunctor_map_section {X : Scheme.{u}} (E : X.Modules)
    {M N : X.Modules} (g : M ⟶ N) (U : X.Opens) (e : Γ(E, U)) (m : Γ(M, U)) :
    ((moduleTensorLeftFunctor X E).map g).app U (moduleTensorSection X E M U e m) =
      moduleTensorSection X E N U e (g.app U m) := by
  exact SheafOfModulesOfCommRing.tensor_map_tensorSection X.sheaf
    (𝟙 (show SheafOfModulesOfCommRing.{u} X.sheaf from E)) g (op U) e m
/-- The actual open tensor comparison retains the original section generators. -/
theorem tensorRestrictionIso_section {X Y : Scheme.{u}} (j : X ⟶ Y) [IsOpenImmersion j]
    (E M : Y.Modules) (U : X.Opens) (e : Γ(E.restrict j, U)) (m : Γ(M.restrict j, U)) :
    (tensorRestrictionIso j E M).hom.app U
        (moduleTensorSection X (E.restrict j) (M.restrict j) U e m) =
      moduleTensorSection Y E M (j ''ᵁ U) e m := by
  exact SheafOfModulesOfCommRing.pushforwardTensorMap_tensorSection (restrictionRingHom j) E
      M (op U) e m

-- Moved from the invertible-sheaf section leaf, whose file-wide type transparency rule this
-- proof was written under; the rule is kept for this declaration only.
set_option backward.isDefEq.respectTransparency.types false in
/-- The original right tensor unitor sends its original pure section to scalar multiplication. -/
theorem tensorRightUnitIso_hom_section (X : Scheme.{u}) (M : X.Modules) (U : X.Opens)
    (m : Γ(M, U)) (a : Γ(X, U)) :
    ((tensorRightUnitIso X.sheaf).hom.app M).val.app (op U)
        (moduleTensorSection X M (SheafOfModules.unit X.ringCatSheaf) U m a) = a • m := by
  let P := (SheafOfModulesOfCommRing.toPresheaf X.sheaf).obj M
  let adj := PresheafOfModules.sheafificationAdjunction (R := X.ringCatSheaf) (𝟙 _)
  have hunit : (associatedSheafUnit X.sheaf).app P ≫
      (SheafOfModulesOfCommRing.toPresheaf X.sheaf).map (adj.counit.app M) = 𝟙 P := by
    exact adj.right_triangle_components M
  have hn := (associatedSheafUnit X.sheaf).naturality (ρ_ P).hom
  have hfac : (associatedSheafUnit X.sheaf).app (P ⊗ 𝟙_ _) ≫
      (SheafOfModulesOfCommRing.toPresheaf X.sheaf).map
        ((tensorRightUnitIso X.sheaf).hom.app M) = (ρ_ P).hom := by
    erw [tensorRightUnitIso_hom_app X.sheaf M, Functor.map_comp, ← Category.assoc, ← hn,
      Category.assoc, hunit, Category.comp_id]
    rfl
  have hv := congrArg (fun q => q.app (op U) (m ⊗ₜ[Γ(X, U)] a)) hfac
  change ((tensorRightUnitIso X.sheaf).hom.app M).val.app (op U)
      (moduleTensorSection X M (SheafOfModules.unit X.ringCatSheaf) U m a) =
    (ρ_ P).hom.app (op U) (m ⊗ₜ[Γ(X, U)] a) at hv
  have hρ : (ρ_ P).hom.app (op U) (m ⊗ₜ[Γ(X, U)] a) = a • m := by
    let : CommRing (X.ringCatSheaf.obj.obj (op U)) := inferInstanceAs (CommRing Γ(X, U))
    exact ModuleCat.MonoidalCategory.rightUnitor_hom_apply m a
  exact hv.trans hρ

-- Moved from the invertible-sheaf section leaf, whose file-wide type transparency rule this
-- proof was written under; the rule is kept for this declaration only.
set_option backward.isDefEq.respectTransparency.types false in
/-- The original left tensor unitor sends its original pure section to scalar multiplication. -/
theorem tensorLeftUnitIso_hom_section (X : Scheme.{u}) (M : X.Modules) (U : X.Opens)
    (a : Γ(X, U)) (m : Γ(M, U)) :
    ((tensorLeftUnitIso X.sheaf).hom.app M).val.app (op U)
        (moduleTensorSection X (SheafOfModules.unit X.ringCatSheaf) M U a m) = a • m := by
  let P := (SheafOfModulesOfCommRing.toPresheaf X.sheaf).obj M
  let adj := PresheafOfModules.sheafificationAdjunction (R := X.ringCatSheaf) (𝟙 _)
  have hunit : (associatedSheafUnit X.sheaf).app P ≫
      (SheafOfModulesOfCommRing.toPresheaf X.sheaf).map (adj.counit.app M) = 𝟙 P := by
    exact adj.right_triangle_components M
  have hn := (associatedSheafUnit X.sheaf).naturality (λ_ P).hom
  have hfac : (associatedSheafUnit X.sheaf).app (𝟙_ _ ⊗ P) ≫
      (SheafOfModulesOfCommRing.toPresheaf X.sheaf).map
        ((tensorLeftUnitIso X.sheaf).hom.app M) = (λ_ P).hom := by
    erw [tensorLeftUnitIso_hom_app X.sheaf M, Functor.map_comp, ← Category.assoc, ← hn,
      Category.assoc, hunit, Category.comp_id]
    rfl
  have hv := congrArg (fun q => q.app (op U) (a ⊗ₜ[Γ(X, U)] m)) hfac
  change ((tensorLeftUnitIso X.sheaf).hom.app M).val.app (op U)
      (moduleTensorSection X (SheafOfModules.unit X.ringCatSheaf) M U a m) =
    (λ_ P).hom.app (op U) (a ⊗ₜ[Γ(X, U)] m) at hv
  have hleft : (λ_ P).hom.app (op U) (a ⊗ₜ[Γ(X, U)] m) = a • m := by
    let : CommRing (X.ringCatSheaf.obj.obj (op U)) := inferInstanceAs (CommRing Γ(X, U))
    exact ModuleCat.MonoidalCategory.leftUnitor_hom_apply a m
  exact hv.trans hleft

end AlgebraicGeometry.Scheme.Modules
end
