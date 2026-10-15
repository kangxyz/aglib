/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Modules.Flat.Generators
/-!
# Functorial open free module sheaves

The original open free generators form a covariant functor of opens. Their
section-representing equivalences intertwine this functor with the actual
restriction maps. Open inclusions induce monomorphisms: free presheaves preserve
the representable injections, and exact sheafification preserves monomorphisms.
Consequently every injective module sheaf has surjective restrictions on all
opens, on any scheme. No quasicoherence or affineness assumption is used.
-/
@[expose] public section


noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace Opposite

namespace AlgebraicGeometry.Scheme.Modules

/-- The original open free generators, functorial in the open. -/
def openFreeFunctor (X : Scheme.{u}) : X.Opens ⥤ X.Modules :=
  yoneda ⋙ _root_.PresheafOfModules.free X.ringCatSheaf.obj ⋙
    _root_.PresheafOfModules.sheafification (𝟙 X.ringCatSheaf.obj)

/-- The free Yoneda equivalence intertwines precomposition and restriction. -/
lemma freeYonedaEquiv_naturality_source {C : Type u} [Category.{u} C]
    {R : Cᵒᵖ ⥤ RingCat.{u}} {U V : C} (h : U ⟶ V)
    (M : _root_.PresheafOfModules.{u} R)
    (p : (_root_.PresheafOfModules.free R).obj (yoneda.obj V) ⟶ M) :
    _root_.PresheafOfModules.freeYonedaEquiv
      ((_root_.PresheafOfModules.free R).map (yoneda.map h) ≫ p) =
      M.map h.op (_root_.PresheafOfModules.freeYonedaEquiv p) := by
  have H := (_root_.PresheafOfModules.freeAdjunction R).homEquiv_naturality_left (yoneda.map h) p
  change _root_.PresheafOfModules.freeHomEquiv
    ((_root_.PresheafOfModules.free R).map (yoneda.map h) ≫ p) =
      yoneda.map h ≫ _root_.PresheafOfModules.freeHomEquiv p at H
  change yonedaEquiv (_root_.PresheafOfModules.freeHomEquiv
    ((_root_.PresheafOfModules.free R).map (yoneda.map h) ≫ p)) = _
  rw [H]
  exact (yonedaEquiv_naturality _ h).symm

/-- Naturality in the open of the original section-representing equivalence. -/
lemma openFreeHomEquiv_naturality_open (X : Scheme.{u}) {U V : X.Opens}
    (h : U ⟶ V) (M : X.Modules) (p : openFree X V ⟶ M) :
    openFreeHomEquiv X U M ((openFreeFunctor X).map h ≫ p) =
      M.presheaf.map h.op (openFreeHomEquiv X V M p) := by
  dsimp [openFreeHomEquiv, openFreeFunctor]
  erw [Adjunction.homEquiv_naturality_left]
  exact freeYonedaEquiv_naturality_source h _ _

/-- Inclusions of opens induce monomorphisms of their actual free sheaves. -/
instance openFreeFunctor_map_mono (X : Scheme.{u}) {U V : X.Opens} (h : U ⟶ V) :
    Mono ((openFreeFunctor X).map h) := by
  have : Mono ((_root_.PresheafOfModules.free X.ringCatSheaf.obj).map (yoneda.map h)) := by
    apply _root_.PresheafOfModules.mono_of_injective
    intro W
    apply Finsupp.mapDomain_injective
    intro a b hab
    change a ≫ h = b ≫ h at hab
    exact (cancel_mono h).mp hab
  change Mono ((_root_.PresheafOfModules.sheafification (𝟙 X.ringCatSheaf.obj)).map
    ((_root_.PresheafOfModules.free X.ringCatSheaf.obj).map (yoneda.map h)))
  infer_instance

/-- Injective module sheaves have surjective restriction maps on all opens. -/
lemma injective_sections_restrict_surjective (X : Scheme.{u}) (M : X.Modules)
    [Injective M] {U V : X.Opens} (h : U ⟶ V) :
    Function.Surjective (M.presheaf.map h.op) := by
  intro s
  let p := (openFreeHomEquiv X U M).symm s
  let t := Injective.factorThru p ((openFreeFunctor X).map h)
  refine ⟨openFreeHomEquiv X V M t, ?_⟩
  rw [← openFreeHomEquiv_naturality_open]
  change openFreeHomEquiv X U M ((openFreeFunctor X).map h ≫ t) = s
  rw [Injective.comp_factorThru]
  exact Equiv.apply_symm_apply _ s

end AlgebraicGeometry.Scheme.Modules
