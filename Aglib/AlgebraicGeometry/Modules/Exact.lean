/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Aglib.CategoryTheory.ExactCategory.Abelian
public import Aglib.CategoryTheory.ExactCategory.Functor
public import Mathlib.AlgebraicGeometry.Modules.Sheaf
public import Mathlib.CategoryTheory.Abelian.SerreClass.Bousfield
/-!
# Exact sheaves of modules and open restriction on an actual scheme

This module uses mathlib's `AlgebraicGeometry.Scheme.Modules`, the category of
sheaves of modules over the structure sheaf. It proves exactness of restriction
to an open subscheme and constructs its actual Serre class of sheaves vanishing
on that open. These are ambient geometric foundations: the category of **all**
module sheaves is not the coherent category defining scheme G-theory, nor the
finite locally free category defining scheme K-theory.
-/
@[expose] public section

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open CategoryTheory.ExactCategory

namespace AlgebraicGeometry.Scheme.Modules

attribute [local instance] Abelian.hasFiniteBiproducts

/-- The actual standard abelian exact structure on `𝒪_X`-module sheaves. -/
abbrev sheafExactStructure (X : Scheme.{u}) : ExactStructure X.Modules :=
  abelianExactStructure X.Modules

variable {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j]

/-- Open restriction, which is defined as a continuous pushforward on the
sites of opens, is also a right adjoint. In particular it preserves limits. -/
instance restrictFunctor_isRightAdjoint :
    (Scheme.Modules.restrictFunctor j).IsRightAdjoint := by
  dsimp [Scheme.Modules.restrictFunctor]
  exact (SheafOfModules.PullbackConstruction.adjunction _).isRightAdjoint

/-- Restriction is additive, as follows already from preservation of products. -/
instance restrictFunctor_additive : (Scheme.Modules.restrictFunctor j).Additive := by
  let := preservesBinaryBiproducts_of_preservesBinaryProducts
    (Scheme.Modules.restrictFunctor j)
  exact Functor.additive_of_preservesBinaryBiproducts _

/-- Open restriction preserves the actual short exact sequences of module sheaves. -/
def exactRestrict : ExactFunctor (sheafExactStructure X) (sheafExactStructure U) where
  toFunctor := Scheme.Modules.restrictFunctor j
  map_conflation _ hS := hS.map_of_exact _

/-- Sheaves supported away from the given open immersion, expressed without any
choice of stalks: their restriction to that open is a zero object. -/
def supportedAway : ObjectProperty X.Modules :=
  (Scheme.Modules.restrictFunctor j).kernel

@[simp]
theorem supportedAway_iff (M : X.Modules) :
    supportedAway j M ↔ IsZero ((Scheme.Modules.restrictFunctor j).obj M) := Iff.rfl

/-- Vanishing on an open is closed under subobjects, quotients, and extensions. -/
instance supportedAway_isSerreClass : (supportedAway j).IsSerreClass := by
  dsimp [supportedAway]
  infer_instance

/-- In a short exact sequence, the middle sheaf vanishes on the open exactly
when both outer sheaves do. -/
theorem supportedAway_iff_of_shortExact {S : ShortComplex X.Modules} (hS : S.ShortExact) :
    supportedAway j S.X₂ ↔ supportedAway j S.X₁ ∧ supportedAway j S.X₃ :=
  (supportedAway j).prop_iff_of_shortExact hS

/-- The *actual* restriction functor presents sheaves on the open as the Serre
localization of all module sheaves by the sheaves vanishing on that open.
This is an ambient sheaf theorem, not yet coherent G-localization. -/
instance restrictFunctor_isLocalization :
    (Scheme.Modules.restrictFunctor j).IsLocalization (supportedAway j).isoModSerre :=
  Abelian.isLocalization_isoModSerre_kernel_of_leftAdjoint
    (Scheme.Modules.restrictAdjunction j)

/-- Restriction inverts precisely the maps whose kernel and cokernel vanish
on the open. -/
theorem supportedAway_isoModSerre_iff {M N : X.Modules} (f : M ⟶ N) :
    (supportedAway j).isoModSerre f ↔ IsIso ((Scheme.Modules.restrictFunctor j).map f) := by
  change (Scheme.Modules.restrictFunctor j).kernel.isoModSerre f ↔ _
  rw [Abelian.isoModSerre_kernel_eq_inverseImage_isomorphisms]
  rfl

end AlgebraicGeometry.Scheme.Modules
