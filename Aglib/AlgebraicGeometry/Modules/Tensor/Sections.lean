/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Modules.Tensor.Restriction
public import Aglib.Algebra.Category.ModuleCat.Sheaf.TensorPushforwardMap

/-!
Source: `Quillen/AlgebraicGeometry/Scheme/Sheaf/TensorSections.lean` at LOCAL Quillen
`189a8e779f0c68b2dfc6f8195daebb3e684a5905`. Selection: whole_general_prerequisite;
source ranges [[1, 66]]. Actual objects, maps and hypotheses are preserved.
-/

/-!
# Tensor sections on a scheme

Original tensor sections detect morphisms and preserve literal coefficient,
module and open-restriction maps.
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
end AlgebraicGeometry.Scheme.Modules
end
