/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Modules.Stalk.Basic
public import Mathlib.Algebra.Category.ModuleCat.Descent
public import Mathlib.AlgebraicGeometry.Morphisms.Flat
/-!
# Flat pullback on arbitrary scheme module sheaves

The actual module stalk of geometric pullback is extension of scalars along
the actual structure-sheaf stalk map. This comparison follows from the
module-stalk/skyscraper adjunction and geometric pullback/pushforward
adjunction. Consequently genuine flatness gives exactness without any
quasicoherence assumption.
-/
@[expose] public section


noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace Opposite
open CategoryTheory.ExactCategory
attribute [local instance] Abelian.hasFiniteBiproducts

namespace AlgebraicGeometry.Scheme.Modules

/-- Pushforward of a module skyscraper is restriction of scalars on its stalk. -/
def moduleSkyscraperPushforwardObjIso {X Y : Scheme.{u}} (f : X ⟶ Y) (x : X)
    (N : ModuleCat.{u} (X.presheaf.stalk x)) :
    (Scheme.Modules.pushforward f).obj ((moduleSkyscraper X x).obj N) ≅
      (moduleSkyscraper Y (f x)).obj ((ModuleCat.restrictScalars (f.stalkMap x).hom).obj N) := by
  apply (Scheme.Modules.fullyFaithfulToPresheafOfModules (X := Y)).preimageIso
  refine _root_.PresheafOfModules.isoMk (fun U => ModuleCat.isoMk (Iso.refl _) ?_) ?_
  · intro r
    ext s
    funext hx
    change f.stalkMap x (Y.presheaf.germ U.unop (f x) hx.down r) • s hx =
      X.presheaf.germ (f ⁻¹ᵁ U.unop) x hx.down (f.app U.unop r) • s hx
    rw [f.germ_stalkMap_apply]
  · intros
    ext s
    funext hx
    rfl

/-- The pushforward/skyscraper comparison is natural in the actual stalk module. -/
def moduleSkyscraperPushforwardIso {X Y : Scheme.{u}} (f : X ⟶ Y) (x : X) :
    moduleSkyscraper X x ⋙ Scheme.Modules.pushforward f ≅
      ModuleCat.restrictScalars (f.stalkMap x).hom ⋙ moduleSkyscraper Y (f x) :=
  NatIso.ofComponents (moduleSkyscraperPushforwardObjIso f x) (by
    intros
    ext U s
    funext hx
    rfl)

/-- Actual geometric pullback commutes with stalks by extension of scalars. -/
def pullbackModuleStalkIso {X Y : Scheme.{u}} (f : X ⟶ Y) (x : X) :
    Scheme.Modules.pullback f ⋙ moduleStalk X x ≅
      moduleStalk Y (f x) ⋙ ModuleCat.extendScalars (f.stalkMap x).hom :=
  Adjunction.leftAdjointUniq
    ((Scheme.Modules.pullbackPushforwardAdjunction f).comp (moduleStalkSkyscraperAdjunction X x))
    (((moduleStalkSkyscraperAdjunction Y (f x)).comp
      (ModuleCat.extendRestrictScalarsAdj (f.stalkMap x).hom)).ofNatIsoRight
        (moduleSkyscraperPushforwardIso f x).symm)

/-- Genuine flatness preserves monomorphisms of arbitrary module sheaves.
The argument detects monicity on actual module stalks and uses flat scalar extension. -/
theorem mono_pullback_of_flat_all {X Y : Scheme.{u}} (f : X ⟶ Y) [Flat f]
    {M N : Y.Modules} (p : M ⟶ N) [Mono p] :
    Mono ((Scheme.Modules.pullback f).map p) := by
  apply mono_of_moduleStalk
  intro x
  have := ModuleCat.preservesFiniteLimits_extendScalars_of_flat (Flat.stalkMap f x)
  let e := pullbackModuleStalkIso f x
  have : Mono (((Scheme.Modules.pullback f ⋙ moduleStalk X x).map p) ≫ e.hom.app N) := by
    rw [e.hom.naturality]
    infer_instance
  let : Mono ((moduleStalk X x).map ((Scheme.Modules.pullback f).map p) ≫ e.hom.app N) := this
  exact mono_of_mono _ (e.hom.app N)

instance pullback_preservesMonomorphisms_of_flat {X Y : Scheme.{u}} (f : X ⟶ Y) [Flat f] :
    (Scheme.Modules.pullback f).PreservesMonomorphisms where
  preserves p hp := by
    let := hp
    exact mono_pullback_of_flat_all f p

/-- Genuine flatness makes actual geometric pullback exact on all module sheaves. -/
instance pullback_preservesFiniteLimits_of_flat {X Y : Scheme.{u}} (f : X ⟶ Y) [Flat f] :
    PreservesFiniteLimits (Scheme.Modules.pullback f) := by
  have := Functor.preservesHomology_of_preservesMonos_and_cokernels (Scheme.Modules.pullback f)
  exact Functor.preservesFiniteLimits_of_preservesHomology (Scheme.Modules.pullback f)

/-- Ambient flat exact pullback on the existing category of all module sheaves. -/
def flatExactPullback {X Y : Scheme.{u}} (f : X ⟶ Y) [Flat f] :
    ExactFunctor (sheafExactStructure Y) (sheafExactStructure X) where
  toFunctor := Scheme.Modules.pullback f
  map_conflation _ h := h.map_of_exact _

/-- Every short exact sequence of module sheaves remains short exact under a flat pullback. -/
theorem shortExact_pullback_of_flat_all {X Y : Scheme.{u}} (f : X ⟶ Y) [Flat f]
    {S : ShortComplex Y.Modules} (hS : S.ShortExact) :
    (S.map (Scheme.Modules.pullback f)).ShortExact := hS.map_of_exact _

end AlgebraicGeometry.Scheme.Modules
