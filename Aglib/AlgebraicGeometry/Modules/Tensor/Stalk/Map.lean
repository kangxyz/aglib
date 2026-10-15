/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Modules.Tensor.Stalk.Bilinear

/-!
Source: `Quillen/AlgebraicGeometry/Scheme/Sheaf/TensorStalkMap.lean` at LOCAL Quillen
`189a8e779f0c68b2dfc6f8195daebb3e684a5905`. Selection: whole_general;
source ranges [[1, 142]]. Actual objects, maps and hypotheses are preserved.
-/

/-!
# The canonical map from the original sheaf tensor stalk

The sectionwise tensor of germs defines a morphism to the module skyscraper.
The original module sheafification and stalk universal properties give a
linear map from the original sheaf tensor stalk to the tensor of stalks.
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
  AlgebraicGeometry TopologicalSpace Opposite SheafOfModulesOfCommRing

open AlgebraicGeometry.Scheme.Modules

namespace AlgebraicGeometry.Scheme.Modules

/-- Literal germ scalar compatibility in the scheme's module notation. -/
theorem schemeModule_germ_smul (X : Scheme.{u}) (x : X) (M : X.Modules)
    (U : X.Opens) (hx : x ∈ U) (a : Γ(X, U)) (s : Γ(M, U)) :
    M.presheaf.germ U x hx (a • s) =
      X.presheaf.germ U x hx a • M.presheaf.germ U x hx s :=
  PresheafOfModules.germ_smul M.val x U hx a s

/-- The unchanged presheaf tensor, with its commutative-ring type explicit. -/
def moduleTensorPresheaf (X : Scheme.{u}) (M N : X.Modules) :
    PresheafOfModulesOfCommRing.{u} X.sheaf.obj :=
  (SheafOfModulesOfCommRing.toPresheaf X.sheaf).obj M ⊗ (SheafOfModulesOfCommRing.toPresheaf
      X.sheaf).obj N

/-- Sectionwise tensor of the original germs, with the original germ scalar action. -/
def moduleTensorToPointApp (X : Scheme.{u}) (x : X) (M N : X.Modules) (U : X.Opens) :
    (moduleTensorPresheaf X M N).obj (op U) ⟶
      ((SheafOfModulesOfCommRing.toPresheaf X.sheaf).obj ((moduleSkyscraper X x).obj
        ((moduleStalk X x).obj M ⊗ (moduleStalk X x).obj N))).obj (op U) :=
  ModuleCat.MonoidalCategory.tensorLift
    (M₁ := ModuleCat.of Γ(X, U) Γ(M, U)) (M₂ := ModuleCat.of Γ(X, U) Γ(N, U))
    (M₃ := show ModuleCat Γ(X, U) from
      ((SheafOfModulesOfCommRing.toPresheaf X.sheaf).obj ((moduleSkyscraper X x).obj
        ((moduleStalk X x).obj M ⊗ (moduleStalk X x).obj N))).obj (op U))
    (fun s t (hx : PLift (x ∈ U)) => M.presheaf.germ U x hx.down s ⊗ₜ[X.presheaf.stalk x]
      N.presheaf.germ U x hx.down t)
    (by
      intro s s' t
      funext hx
      change M.presheaf.germ U x hx.down (s + s') ⊗ₜ[X.presheaf.stalk x]
          N.presheaf.germ U x hx.down t =
        M.presheaf.germ U x hx.down s ⊗ₜ[X.presheaf.stalk x] N.presheaf.germ U x hx.down t +
          M.presheaf.germ U x hx.down s' ⊗ₜ[X.presheaf.stalk x] N.presheaf.germ U x hx.down t
      rw [map_add, TensorProduct.add_tmul])
    (by
      intro a s t
      funext hx
      change M.presheaf.germ U x hx.down (a • s) ⊗ₜ[X.presheaf.stalk x]
          N.presheaf.germ U x hx.down t =
        X.presheaf.germ U x hx.down a •
          (M.presheaf.germ U x hx.down s ⊗ₜ[X.presheaf.stalk x] N.presheaf.germ U x hx.down t)
      rw [schemeModule_germ_smul, ← TensorProduct.smul_tmul'])
    (by
      intro s t t'
      funext hx
      change M.presheaf.germ U x hx.down s ⊗ₜ[X.presheaf.stalk x]
          N.presheaf.germ U x hx.down (t + t') =
        M.presheaf.germ U x hx.down s ⊗ₜ[X.presheaf.stalk x] N.presheaf.germ U x hx.down t +
          M.presheaf.germ U x hx.down s ⊗ₜ[X.presheaf.stalk x] N.presheaf.germ U x hx.down t'
      rw [map_add, TensorProduct.tmul_add])
    (by
      intro a s t
      funext hx
      change M.presheaf.germ U x hx.down s ⊗ₜ[X.presheaf.stalk x]
          N.presheaf.germ U x hx.down (a • t) =
        X.presheaf.germ U x hx.down a •
          (M.presheaf.germ U x hx.down s ⊗ₜ[X.presheaf.stalk x] N.presheaf.germ U x hx.down t)
      rw [schemeModule_germ_smul, TensorProduct.tmul_smul])

/-- Original section germs give a morphism from the tensor presheaf to a module skyscraper. -/
def moduleTensorToPointPresheaf (X : Scheme.{u}) (x : X) (M N : X.Modules) :
    moduleTensorPresheaf X M N ⟶
      (SheafOfModulesOfCommRing.toPresheaf X.sheaf).obj
        ((moduleSkyscraper X x).obj ((moduleStalk X x).obj M ⊗ (moduleStalk X x).obj N)) :=
  PresheafOfModulesOfCommRing.homMk (fun U => moduleTensorToPointApp X x M N U.unop)
    (by
      intro U V i
      apply ModuleCat.MonoidalCategory.tensor_ext
      intro s t
      funext hx
      change M.presheaf.germ V.unop x hx.down (M.presheaf.map i s) ⊗ₜ[X.presheaf.stalk x]
          N.presheaf.germ V.unop x hx.down (N.presheaf.map i t) =
        M.presheaf.germ U.unop x (i.unop.le hx.down) s ⊗ₜ[X.presheaf.stalk x]
          N.presheaf.germ U.unop x (i.unop.le hx.down) t
      exact congrArg₂ (fun m n => m ⊗ₜ[X.presheaf.stalk x] n)
        (M.presheaf.germ_res_apply i.unop x hx.down s)
        (N.presheaf.germ_res_apply i.unop x hx.down t))

/-- Extension of the unchanged tensor of section germs through the original sheafification. -/
def moduleTensorToPoint (X : Scheme.{u}) (x : X) (M N : X.Modules) :
    (moduleTensorLeftFunctor X M).obj N ⟶
      (moduleSkyscraper X x).obj ((moduleStalk X x).obj M ⊗ (moduleStalk X x).obj N) :=
  ((PresheafOfModules.sheafificationAdjunction (R := X.ringCatSheaf) (𝟙 _)).homEquiv _ _).symm
    (moduleTensorToPointPresheaf X x M N)

/-- The sheafification extension keeps the formula on the original pure sections. -/
theorem moduleTensorToPoint_section (X : Scheme.{u}) (x : X) (M N : X.Modules)
    (U : X.Opens) (hx : x ∈ U) (s : Γ(M, U)) (t : Γ(N, U)) :
    (moduleTensorToPoint X x M N).app U (moduleTensorSection X M N U s t) ⟨hx⟩ =
      M.presheaf.germ U x hx s ⊗ₜ[X.presheaf.stalk x] N.presheaf.germ U x hx t := by
  have h := ((PresheafOfModules.sheafificationAdjunction (R := X.ringCatSheaf) (𝟙 _)).homEquiv
    (moduleTensorPresheaf X M N)
    ((moduleSkyscraper X x).obj
      ((moduleStalk X x).obj M ⊗ (moduleStalk X x).obj N))).apply_symm_apply
      (moduleTensorToPointPresheaf X x M N)
  rw [Adjunction.homEquiv_unit] at h
  exact congrFun (congrArg (fun p => p.app (op U) (s ⊗ₜ[Γ(X, U)] t)) h) ⟨hx⟩

/-- The canonical scalar-compatible comparison from the original sheaf tensor stalk. -/
def moduleTensorStalkHom (X : Scheme.{u}) (x : X) (M N : X.Modules) :
    (moduleStalk X x).obj ((moduleTensorLeftFunctor X M).obj N) ⟶
      (moduleStalk X x).obj M ⊗ (moduleStalk X x).obj N :=
  moduleSkyscraperFromStalk x ((moduleTensorLeftFunctor X M).obj N)
    ((moduleStalk X x).obj M ⊗ (moduleStalk X x).obj N) (moduleTensorToPoint X x M N)

/-- The canonical comparison sends the original pure-section germ to the tensor of its germs. -/
theorem moduleTensorStalkHom_germ (X : Scheme.{u}) (x : X) (M N : X.Modules)
    (U : X.Opens) (hx : x ∈ U) (s : Γ(M, U)) (t : Γ(N, U)) :
    moduleTensorStalkHom X x M N
        (((moduleTensorLeftFunctor X M).obj N).presheaf.germ U x hx
          (moduleTensorSection X M N U s t)) =
      M.presheaf.germ U x hx s ⊗ₜ[X.presheaf.stalk x] N.presheaf.germ U x hx t := by
  change colimit.desc _ (moduleSkyscraperCocone x ((moduleTensorLeftFunctor X M).obj N)
    ((moduleStalk X x).obj M ⊗ (moduleStalk X x).obj N) (moduleTensorToPoint X x M N)) _ = _
  rw [germ_moduleSkyscraperCocone_desc]
  exact moduleTensorToPoint_section X x M N U hx s t

end AlgebraicGeometry.Scheme.Modules
