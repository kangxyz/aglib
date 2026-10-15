/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Modules.Flat.Locality
public import Mathlib.CategoryTheory.Adjunction.Triple
/-!
# Genuine extension by zero for module sheaves

For any open immersion of schemes, the original restriction functor has a
constructed left adjoint. The actual adjoint triple with geometric pushforward
makes its unit invertible. The accepted restriction-stalk comparison computes
its stalks inside the open. Outside the image, restriction of the actual module
skyscraper is zero; the two genuine adjunctions then force the extension stalk
to vanish. These formulas prove all-sheaf exactness and preservation of
stalkwise flatness. No quasicoherence, compactness or separation hypothesis is
used. The original unit, counit and fully faithful functor are retained.

This is the extension-by-zero input to Thomason--Trobaugh, Section 3.20.4.
-/
@[expose] public section


noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace Opposite

namespace AlgebraicGeometry.Scheme.Modules

/-- Genuine extension by zero, the constructed left adjoint of open restriction. -/
def extensionByZero {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j] :
    U.Modules ⥤ X.Modules := (Scheme.Modules.restrictFunctor j).leftAdjoint

/-- The actual extension-by-zero/restriction adjunction. -/
def extensionByZeroRestrictAdjunction {U X : Scheme.{u}} (j : U ⟶ X)
    [IsOpenImmersion j] : extensionByZero j ⊣ Scheme.Modules.restrictFunctor j :=
  Adjunction.ofIsRightAdjoint _

instance extensionByZero_isLeftAdjoint {U X : Scheme.{u}} (j : U ⟶ X)
    [IsOpenImmersion j] : (extensionByZero j).IsLeftAdjoint :=
  (extensionByZeroRestrictAdjunction j).isLeftAdjoint

/-- The genuine open adjoint triple, with the original geometric pushforward. -/
def extensionByZeroTriple {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j] :
    Adjunction.Triple (extensionByZero j) (Scheme.Modules.restrictFunctor j)
      (Scheme.Modules.pushforward j) :=
  ⟨extensionByZeroRestrictAdjunction j, Scheme.Modules.restrictAdjunction j⟩

instance extensionByZero_unit_isIso {U X : Scheme.{u}} (j : U ⟶ X)
    [IsOpenImmersion j] : IsIso (extensionByZeroRestrictAdjunction j).unit :=
  (extensionByZeroTriple j).isIso_unit_iff_isIso_counit.mpr inferInstance

/-- Restriction of extension by zero is the identity, using the actual adjunction unit. -/
def extensionByZeroRestrictIso {U X : Scheme.{u}} (j : U ⟶ X)
    [IsOpenImmersion j] :
    extensionByZero j ⋙ Scheme.Modules.restrictFunctor j ≅ 𝟭 _ :=
  (asIso (extensionByZeroRestrictAdjunction j).unit).symm

/-- Inside the open, extension by zero retains the original stalk and scalar action. -/
def extensionByZeroModuleStalkIso {U X : Scheme.{u}} (j : U ⟶ X)
    [IsOpenImmersion j] (x : U) :
    extensionByZero j ⋙ moduleStalk X (j x) ≅
      moduleStalk U x ⋙ ModuleCat.restrictScalars (j.stalkMap x).hom :=
  Functor.isoWhiskerLeft (extensionByZero j) (restrictModuleStalkIso j x).symm ≪≫
    (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight (extensionByZeroRestrictIso j) _ ≪≫
    Functor.leftUnitor _

/-- A skyscraper at a point outside the image restricts to the zero module sheaf. -/
lemma isZero_restrict_moduleSkyscraper_of_not_mem {U X : Scheme.{u}} (j : U ⟶ X)
    [IsOpenImmersion j] (x : X) (hx : x ∉ Set.range j)
    (N : ModuleCat.{u} (X.presheaf.stalk x)) :
    IsZero ((Scheme.Modules.restrictFunctor j).obj ((moduleSkyscraper X x).obj N)) := by
  apply (IsZero.iff_id_eq_zero _).mpr
  ext V s
  funext h
  exact (hx (by obtain ⟨y, _, hy⟩ := h.down; exact ⟨y, hy⟩)).elim

/-- Outside the open image the actual module stalk of extension by zero vanishes. -/
lemma isZero_extensionByZero_stalk_of_not_mem {U X : Scheme.{u}} (j : U ⟶ X)
    [IsOpenImmersion j] (x : X) (hx : x ∉ Set.range j) (M : U.Modules) :
    IsZero ((moduleStalk X x).obj ((extensionByZero j).obj M)) := by
  apply (IsZero.iff_id_eq_zero _).mpr
  let N := (moduleStalk X x).obj ((extensionByZero j).obj M)
  let e := ((moduleStalkSkyscraperAdjunction X x).homEquiv _ N).trans
    ((extensionByZeroRestrictAdjunction j).homEquiv M _)
  exact e.injective ((isZero_restrict_moduleSkyscraper_of_not_mem j x hx N).eq_of_tgt _ _)

/-- Extension by zero preserves every monomorphism of actual module sheaves. -/
lemma mono_extensionByZero_map {U X : Scheme.{u}} (j : U ⟶ X)
    [IsOpenImmersion j] {M N : U.Modules} (f : M ⟶ N) [Mono f] :
    Mono ((extensionByZero j).map f) := by
  apply mono_of_moduleStalk
  intro x
  by_cases hx : x ∈ Set.range j
  · obtain ⟨y, rfl⟩ := hx
    let e := extensionByZeroModuleStalkIso j y
    have : Mono (((extensionByZero j ⋙ moduleStalk X (j y)).map f) ≫ e.hom.app N) := by
      rw [e.hom.naturality]
      infer_instance
    let : Mono ((moduleStalk X (j y)).map ((extensionByZero j).map f) ≫ e.hom.app N) := this
    exact mono_of_mono _ (e.hom.app N)
  · exact (isZero_extensionByZero_stalk_of_not_mem j x hx M).mono _

instance extensionByZero_preservesMonomorphisms {U X : Scheme.{u}} (j : U ⟶ X)
    [IsOpenImmersion j] : (extensionByZero j).PreservesMonomorphisms where
  preserves f hf := by let := hf; exact mono_extensionByZero_map j f

instance extensionByZero_additive {U X : Scheme.{u}} (j : U ⟶ X)
    [IsOpenImmersion j] : (extensionByZero j).Additive := by
  let := preservesBinaryBiproducts_of_preservesBinaryCoproducts (extensionByZero j)
  exact Functor.additive_of_preservesBinaryBiproducts (extensionByZero j)

/-- Extension by zero is exact on all module sheaves, with no quasicoherence premise. -/
instance extensionByZero_preservesFiniteLimits {U X : Scheme.{u}} (j : U ⟶ X)
    [IsOpenImmersion j] : PreservesFiniteLimits (extensionByZero j) := by
  have := Functor.preservesHomology_of_preservesMonos_and_cokernels (extensionByZero j)
  exact Functor.preservesFiniteLimits_of_preservesHomology (extensionByZero j)

/-- The original short exact sequence remains short exact after extension by zero. -/
lemma shortExact_extensionByZero {U X : Scheme.{u}} (j : U ⟶ X)
    [IsOpenImmersion j] {S : ShortComplex U.Modules} (hS : S.ShortExact) :
    (S.map (extensionByZero j)).ShortExact := hS.map_of_exact _

/-- Extension by zero preserves genuine stalkwise flatness. -/
lemma stalkwiseFlat_extensionByZero {U X : Scheme.{u}} (j : U ⟶ X)
    [IsOpenImmersion j] {M : U.Modules} (hM : stalkwiseFlat U M) :
    stalkwiseFlat X ((extensionByZero j).obj M) := by
  intro x
  by_cases hx : x ∈ Set.range j
  · obtain ⟨y, rfl⟩ := hx
    let := hM y
    let : Module.Flat (X.presheaf.stalk (j y))
        ((moduleStalk U y ⋙ ModuleCat.restrictScalars (j.stalkMap y).hom).obj M) :=
      flat_restrictScalars (j.stalkMap y).hom (Flat.stalkMap j y) ((moduleStalk U y).obj M)
    exact Module.Flat.of_linearEquiv ((extensionByZeroModuleStalkIso j y).app M).toLinearEquiv
  · let : Subsingleton ((moduleStalk X x).obj ((extensionByZero j).obj M)) :=
      ModuleCat.subsingleton_of_isZero (isZero_extensionByZero_stalk_of_not_mem j x hx M)
    infer_instance

/-- The genuine extension-by-zero functor is fully faithful. -/
def extensionByZeroFullyFaithful {U X : Scheme.{u}} (j : U ⟶ X)
    [IsOpenImmersion j] : (extensionByZero j).FullyFaithful :=
  (extensionByZeroRestrictAdjunction j).fullyFaithfulLOfIsIsoUnit

instance extensionByZero_full {U X : Scheme.{u}} (j : U ⟶ X)
    [IsOpenImmersion j] : (extensionByZero j).Full := (extensionByZeroFullyFaithful j).full

instance extensionByZero_faithful {U X : Scheme.{u}} (j : U ⟶ X)
    [IsOpenImmersion j] : (extensionByZero j).Faithful := (extensionByZeroFullyFaithful j).faithful

/-- The actual restriction of the extension-by-zero counit is invertible. -/
instance restrict_extensionByZero_counit_isIso {U X : Scheme.{u}} (j : U ⟶ X)
    [IsOpenImmersion j] (M : X.Modules) :
    IsIso ((Scheme.Modules.restrictFunctor j).map
      ((extensionByZeroRestrictAdjunction j).counit.app M)) := by
  let a := extensionByZeroRestrictAdjunction j
  have h := a.right_triangle_components M
  have he : (Scheme.Modules.restrictFunctor j).map (a.counit.app M) =
      inv (a.unit.app ((Scheme.Modules.restrictFunctor j).obj M)) :=
    (IsIso.inv_eq_of_hom_inv_id h).symm
  change IsIso ((Scheme.Modules.restrictFunctor j).map (a.counit.app M))
  rw [he]
  infer_instance

end AlgebraicGeometry.Scheme.Modules
