/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Modules.Flat.Generators
public import Aglib.AlgebraicGeometry.Modules.Pullback.FlatMorphism
public import Mathlib.RingTheory.Flat.Equalizer
public import Mathlib.RingTheory.Flat.Stability
/-!
# Arbitrary pullback on genuinely stalkwise-flat sheaves

No flatness of the scheme morphism is assumed. Exactness holds for actual
short exact sequences whose quotient has flat module stalks. Flat kernels
of epimorphisms between flat objects are proved, rather than supplied as data.
-/
@[expose] public section


noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace Opposite
namespace AlgebraicGeometry.Scheme.Modules

/-- Flat modules are closed under kernels of epimorphisms between flat modules. -/
theorem moduleFlat_of_shortExact {R : Type u} [CommRing R]
    {S : ShortComplex (ModuleCat.{u} R)} (hS : S.ShortExact)
    [Module.Flat R S.X₂] [Module.Flat R S.X₃] : Module.Flat R S.X₁ := by
  apply Module.Flat.iff_rTensor_preserves_injective_linearMap.mpr
  intro A B _ _ _ _ p hp
  have hA : Function.Injective (S.f.hom.lTensor A) :=
    LinearMap.lTensor_injective_of_exact_of_flat S.g.hom hS.moduleCat_surjective_g
      S.f.hom hS.moduleCat_injective_f ((ShortComplex.ShortExact.moduleCat_exact_iff_function_exact
        S).mp hS.exact) A
  have h₂ : Function.Injective (p.rTensor S.X₂) :=
    Module.Flat.rTensor_preserves_injective_linearMap p hp
  have hc : (S.f.hom.lTensor B).comp (p.rTensor S.X₁) =
      (p.rTensor S.X₂).comp (S.f.hom.lTensor A) := by
    rw [LinearMap.lTensor_comp_rTensor, LinearMap.rTensor_comp_lTensor]
  exact Function.Injective.of_comp (f := S.f.hom.lTensor B)
    (by rw [← LinearMap.coe_comp, hc]; exact h₂.comp hA)

/-- Scalar extension preserves any short exact sequence with a flat quotient. -/
theorem shortExact_extendScalars_of_flat_quotient {R T : Type u} [CommRing R] [CommRing T]
    (φ : R →+* T) {S : ShortComplex (ModuleCat.{u} R)} (hS : S.ShortExact)
    [Module.Flat R S.X₃] : (S.map (ModuleCat.extendScalars φ)).ShortExact := by
  have hmono : Mono ((ModuleCat.extendScalars φ).map S.f) := by
    apply (ModuleCat.mono_iff_injective _).mpr
    algebraize [φ]
    exact LinearMap.lTensor_injective_of_exact_of_flat S.g.hom hS.moduleCat_surjective_g
      S.f.hom hS.moduleCat_injective_f ((ShortComplex.ShortExact.moduleCat_exact_iff_function_exact
        S).mp hS.exact) T
  let : PreservesBinaryBiproducts (ModuleCat.extendScalars φ) :=
    preservesBinaryBiproducts_of_preservesBinaryCoproducts _
  let : (ModuleCat.extendScalars φ).Additive :=
    Functor.additive_of_preservesBinaryBiproducts _
  have hr := (Functor.preservesFiniteColimits_iff_forall_exact_map_and_epi
    (ModuleCat.extendScalars φ)).mp inferInstance S hS
  exact { exact := hr.1, mono_f := hmono, epi_g := hr.2 }

/-- Genuine flatness of an object is preserved by arbitrary geometric pullback. -/
theorem stalkwiseFlat_pullback {X Y : Scheme.{u}} (f : X ⟶ Y) {M : Y.Modules}
    (hM : stalkwiseFlat Y M) : stalkwiseFlat X ((Scheme.Modules.pullback f).obj M) := by
  intro x
  let := hM (f x)
  let h : Module.Flat (X.presheaf.stalk x)
      ((ModuleCat.extendScalars (f.stalkMap x).hom).obj ((moduleStalk Y (f x)).obj M)) := by
    algebraize [(f.stalkMap x).hom]
    exact Module.Flat.baseChange (Y.presheaf.stalk (f x)) (X.presheaf.stalk x)
      ((moduleStalk Y (f x)).obj M)
  let : Module.Flat (X.presheaf.stalk x)
      ((moduleStalk Y (f x) ⋙ ModuleCat.extendScalars (f.stalkMap x).hom).obj M) := h
  exact Module.Flat.of_linearEquiv ((pullbackModuleStalkIso f x).app M).toLinearEquiv

/-- Stalkwise-flat module sheaves are closed under kernels in actual short exact sequences. -/
theorem stalkwiseFlat_of_shortExact {X : Scheme.{u}} {S : ShortComplex X.Modules}
    (hS : S.ShortExact) (h₂ : stalkwiseFlat X S.X₂) (h₃ : stalkwiseFlat X S.X₃) :
    stalkwiseFlat X S.X₁ := by
  intro x
  let : Module.Flat (X.presheaf.stalk x) (S.map (moduleStalk X x)).X₂ := h₂ x
  let : Module.Flat (X.presheaf.stalk x) (S.map (moduleStalk X x)).X₃ := h₃ x
  exact moduleFlat_of_shortExact (hS.map_of_exact (moduleStalk X x))

/-- Arbitrary geometric pullback preserves actual short exact sequences with
stalkwise-flat quotient. No ambient left exactness is claimed. -/
theorem shortExact_pullback_of_stalkwiseFlat_quotient {X Y : Scheme.{u}} (f : X ⟶ Y)
    {S : ShortComplex Y.Modules} (hS : S.ShortExact) (h₃ : stalkwiseFlat Y S.X₃) :
    (S.map (Scheme.Modules.pullback f)).ShortExact := by
  have hmono : Mono ((Scheme.Modules.pullback f).map S.f) := by
    apply mono_of_moduleStalk
    intro x
    let : Module.Flat (Y.presheaf.stalk (f x))
      (S.map (moduleStalk Y (f x))).X₃ := h₃ (f x)
    have h := shortExact_extendScalars_of_flat_quotient (f.stalkMap x).hom
      (hS.map_of_exact (moduleStalk Y (f x)))
    have hi := ShortComplex.shortExact_of_iso
      ((S.mapNatIso (pullbackModuleStalkIso f x)).symm) h
    exact hi.mono_f
  have hr := (Functor.preservesFiniteColimits_iff_forall_exact_map_and_epi
    (Scheme.Modules.pullback f)).mp inferInstance S hS
  exact { exact := hr.1, mono_f := hmono, epi_g := hr.2 }

end AlgebraicGeometry.Scheme.Modules
