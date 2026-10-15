/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Modules.Tensor.Stalk.Basic

/-!
Source: `Quillen/AlgebraicGeometry/Scheme/Sheaf/TensorStalkNaturality.lean` at LOCAL Quillen
`189a8e779f0c68b2dfc6f8195daebb3e684a5905`. Selection: whole_general;
source ranges [[1, 93]]. Actual objects, maps and hypotheses are preserved.
-/

/-!
# Naturality of the original tensor stalk comparison in both module arguments
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
  AlgebraicGeometry TopologicalSpace Opposite

open AlgebraicGeometry.Scheme.Modules

namespace AlgebraicGeometry.Scheme.Modules

/-- The literal module stalk arrow retains the original germ formula. -/
theorem moduleStalk_map_germ {X : Scheme.{u}} (x : X) {M N : X.Modules} (f : M ⟶ N)
    (U : X.Opens) (hx : x ∈ U) (s : Γ(M, U)) :
    (moduleStalk X x).map f (M.presheaf.germ U x hx s) =
      N.presheaf.germ U x hx (f.app U s) :=
  TopCat.Presheaf.stalkFunctor_map_germ_apply U x hx f.mapPresheaf s

/-- Naturality in the first argument for the original coefficient tensor map. -/
theorem moduleTensorStalkIso_naturality_left (X : Scheme.{u}) (x : X)
    {M M' : X.Modules} (f : M ⟶ M') (N : X.Modules) :
    (moduleStalk X x).map ((moduleTensorCoefficientMap X f).app N) ≫
        (moduleTensorStalkIso X x M' N).hom =
      (moduleTensorStalkIso X x M N).hom ≫
        ((moduleStalk X x).map f ⊗ₘ 𝟙 ((moduleStalk X x).obj N)) := by
  apply moduleTensorStalk_hom_ext X x M N
  intro U hx s t
  change (moduleTensorStalkIso X x M' N).hom
      ((moduleStalk X x).map ((moduleTensorCoefficientMap X f).app N)
        (((moduleTensorLeftFunctor X M).obj N).presheaf.germ U x hx
          (moduleTensorSection X M N U s t))) =
    ((moduleStalk X x).map f ⊗ₘ 𝟙 ((moduleStalk X x).obj N))
      ((moduleTensorStalkIso X x M N).hom
        (((moduleTensorLeftFunctor X M).obj N).presheaf.germ U x hx
          (moduleTensorSection X M N U s t)))
  rw [moduleStalk_map_germ, moduleTensorCoefficientMap_section,
    moduleTensorStalkIso_hom_germ, moduleTensorStalkIso_hom_germ,
    ModuleCat.MonoidalCategory.tensorHom_tmul, moduleStalk_map_germ]
  rfl

/-- Naturality in the second argument for the original tensor functor map. -/
theorem moduleTensorStalkIso_naturality_right (X : Scheme.{u}) (x : X) (M : X.Modules)
    {N N' : X.Modules} (g : N ⟶ N') :
    (moduleStalk X x).map ((moduleTensorLeftFunctor X M).map g) ≫
        (moduleTensorStalkIso X x M N').hom =
      (moduleTensorStalkIso X x M N).hom ≫
        (𝟙 ((moduleStalk X x).obj M) ⊗ₘ (moduleStalk X x).map g) := by
  apply moduleTensorStalk_hom_ext X x M N
  intro U hx s t
  change (moduleTensorStalkIso X x M N').hom
      ((moduleStalk X x).map ((moduleTensorLeftFunctor X M).map g)
        (((moduleTensorLeftFunctor X M).obj N).presheaf.germ U x hx
          (moduleTensorSection X M N U s t))) =
    (𝟙 ((moduleStalk X x).obj M) ⊗ₘ (moduleStalk X x).map g)
      ((moduleTensorStalkIso X x M N).hom
        (((moduleTensorLeftFunctor X M).obj N).presheaf.germ U x hx
          (moduleTensorSection X M N U s t)))
  rw [moduleStalk_map_germ, moduleTensorLeftFunctor_map_section,
    moduleTensorStalkIso_hom_germ, moduleTensorStalkIso_hom_germ,
    ModuleCat.MonoidalCategory.tensorHom_tmul, moduleStalk_map_germ]
  rfl

/-- Natural comparison for the original second-variable tensor functor. -/
def moduleTensorLeftStalkIso (X : Scheme.{u}) (x : X) (M : X.Modules) :
    moduleTensorLeftFunctor X M ⋙ moduleStalk X x ≅
      moduleStalk X x ⋙ tensorLeft ((moduleStalk X x).obj M) :=
  NatIso.ofComponents (moduleTensorStalkIso X x M)
    (fun g => moduleTensorStalkIso_naturality_right X x M g)

/-- The natural comparison is itself natural in the original coefficient morphisms. -/
theorem moduleTensorLeftStalkIso_coefficient_naturality (X : Scheme.{u}) (x : X)
    {M M' : X.Modules} (f : M ⟶ M') :
    Functor.whiskerRight (moduleTensorCoefficientMap X f) (moduleStalk X x) ≫
        (moduleTensorLeftStalkIso X x M').hom =
      (moduleTensorLeftStalkIso X x M).hom ≫
        Functor.whiskerLeft (moduleStalk X x)
          ((curriedTensor (ModuleCat.{u} (X.presheaf.stalk x))).map ((moduleStalk X x).map f)) := by
  apply NatTrans.ext
  funext N
  exact moduleTensorStalkIso_naturality_left X x f N

end AlgebraicGeometry.Scheme.Modules
