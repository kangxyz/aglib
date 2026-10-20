/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Aglib.Algebra.Category.FGModuleCat.Basic
public import Aglib.CategoryTheory.ExactCategory.Abelian
public import Mathlib.Algebra.Category.ModuleCat.ChangeOfRingsExact
public import Mathlib.Algebra.Category.ModuleCat.Descent
public import Mathlib.RingTheory.TensorProduct.Finite
public import Mathlib.Algebra.Category.Ring.Basic
public import Mathlib.Algebra.Category.FGModuleCat.Limits
public import Mathlib.Algebra.Category.FGModuleCat.Colimits

/-!
# Extension of scalars on actual finite modules

The ring map is explicit; the finite-limit and exact interfaces retain flatness and the displayed
Noetherian hypotheses.

Source: `lean/R5Lab/Aglib/Algebra/Category/FGModuleCat/ScalarExtension.lean`
at frozen R5 `f8a3314ddecffcada2ec721d26d56a937bed9690`.
SHA-256: `5bda755e2c9230ead187a987d1a2af980461011c63d53b0c49df9bea083d57ec`.
Native objects and canonical maps are reused; provenance does not select declaration namespaces.
-/

@[expose] public section

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Limits
open scoped TensorProduct
open _root_.CategoryTheory.ExactCategory (ExactFunctor)
open _root_.ModuleCat (FiniteModule finiteModule finiteModuleExactStructure)
attribute [local instance] Abelian.hasFiniteBiproducts
namespace FGModuleCat
universe u
section Affine
variable {R S : CommRingCat.{u}} (φ : R ⟶ S)

/-- Literal extension of scalars restricted to finite modules. -/
def finiteModuleExtension : FiniteModule.{u,u} R ⥤ FiniteModule.{u,u} S :=
  ObjectProperty.lift _ ((finiteModule R).ι ⋙ ModuleCat.extendScalars φ.hom)
    (fun M => by
      let := φ.hom.toAlgebra
      change Module.Finite S (S ⊗[R] M.obj)
      infer_instance)

@[simp] theorem finiteModuleExtension_comp_inclusion :
    finiteModuleExtension φ ⋙ (finiteModule S).ι =
      (finiteModule R).ι ⋙ ModuleCat.extendScalars φ.hom := rfl

instance finiteModuleExtension_additive : (finiteModuleExtension φ).Additive where
  map_add := by
    intro X Y f g
    let := preservesBinaryBiproducts_of_preservesBinaryCoproducts
      (ModuleCat.extendScalars φ.hom)
    let := Functor.additive_of_preservesBinaryBiproducts (ModuleCat.extendScalars φ.hom)
    apply FGModuleCat.hom_ext
    exact congrArg ModuleCat.Hom.hom
      (Functor.map_add (ModuleCat.extendScalars φ.hom) (f := f.hom) (g := g.hom))

variable [IsNoetherianRing R]

theorem finiteModuleExtension_preservesFiniteLimits [IsNoetherianRing S]
    (hφ : φ.hom.Flat) :
    PreservesFiniteLimits (finiteModuleExtension φ) := by
  have := ModuleCat.preservesFiniteLimits_extendScalars_of_flat hφ
  have : PreservesFiniteLimits (finiteModuleExtension φ ⋙ (finiteModule S).ι) := by
    change PreservesFiniteLimits
      (forget₂ (FGModuleCat.{u} R) (ModuleCat.{u} R) ⋙ ModuleCat.extendScalars φ.hom)
    infer_instance
  exact preservesFiniteLimits_of_reflects_of_preserves (finiteModuleExtension φ)
    (finiteModule S).ι

variable [IsNoetherianRing S]

instance finiteModuleExtension_preservesFiniteColimits :
    PreservesFiniteColimits (finiteModuleExtension φ) := by
  have : PreservesFiniteColimits (finiteModuleExtension φ ⋙ (finiteModule S).ι) := by
    change PreservesFiniteColimits
      (forget₂ (FGModuleCat.{u} R) (ModuleCat.{u} R) ⋙ ModuleCat.extendScalars φ.hom)
    infer_instance
  exact preservesFiniteColimits_of_reflects_of_preserves (finiteModuleExtension φ)
    (finiteModule S).ι

/-- Scalar extension is exact when the original ring homomorphism is flat. -/
def finiteModuleExtensionExact (hφ : φ.hom.Flat) :
    ExactFunctor (finiteModuleExactStructure.{u,u} R) (finiteModuleExactStructure.{u,u} S) where
  toFunctor := finiteModuleExtension φ
  map_conflation _ h := by
    have := finiteModuleExtension_preservesFiniteLimits φ hφ
    exact h.map_of_exact _

end Affine
section Fields
variable (K L : Type u) [Field K] [Field L] (f : K →+* L)
/-- The same literal scalar extension used in the affine comparison. -/
def fieldModuleExtensionExact :
    ExactFunctor (finiteModuleExactStructure.{u,u} K) (finiteModuleExactStructure.{u,u} L) :=
  finiteModuleExtensionExact (CommRingCat.ofHom f)
    (RingHom.Flat.of_isField (Field.toIsField K) f)

end Fields
end FGModuleCat
