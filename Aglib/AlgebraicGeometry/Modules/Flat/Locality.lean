/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Modules.Flat.Pullback
public import Mathlib.CategoryTheory.Adjunction.FullyFaithful
/-!
# Actual stalkwise-flat locality under open restriction

Open restriction commutes with actual module stalks after restriction of
scalars along the original stalk ring map. The latter is an isomorphism.
This gives pointwise reflection and preservation of flatness and an honest
neighborhood criterion, with no quasicoherence or affineness premise.
-/
@[expose] public section


noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
namespace AlgebraicGeometry.Scheme.Modules

/-- Actual open restriction stalks, viewed over the original stalk ring. -/
def restrictModuleStalkIso {X Y : Scheme.{u}} (f : X ⟶ Y) [IsOpenImmersion f]
    (x : X) :
    Scheme.Modules.restrictFunctor f ⋙ moduleStalk X x ⋙
        ModuleCat.restrictScalars (f.stalkMap x).hom ≅ moduleStalk Y (f x) := by
  let : (ModuleCat.restrictScalars (f.stalkMap x).hom).IsEquivalence :=
    ModuleCat.restrictScalars_isEquivalence_of_ringEquiv
      (asIso (f.stalkMap x)).commRingCatIsoToRingEquiv
  exact (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight (Functor.isoWhiskerRight
      (Scheme.Modules.restrictFunctorIsoPullback f) (moduleStalk X x)) _ ≪≫
    Functor.isoWhiskerRight (pullbackModuleStalkIso f x) _ ≪≫
    Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft _ (asIso (ModuleCat.extendRestrictScalarsAdj
      (f.stalkMap x).hom).unit).symm ≪≫ Functor.rightUnitor _

/-- Flat modules over a flat scalar map remain flat on restriction of scalars. -/
theorem flat_restrictScalars {R S : Type u} [CommRing R] [CommRing S]
    (f : R →+* S) (hf : f.Flat) (N : ModuleCat.{u} S) [Module.Flat S N] :
    Module.Flat R ((ModuleCat.restrictScalars f).obj N) := by
  algebraize [f]
  let : Module.Flat R S := hf
  let : IsScalarTower R S ((ModuleCat.restrictScalars f).obj N) := {
    smul_assoc r s n := by
      change (f r * s) • (n : N) = f r • (s • (n : N))
      exact mul_smul _ _ _ }
  let : Module.Flat S ((ModuleCat.restrictScalars f).obj N) := inferInstanceAs (Module.Flat S N)
  exact Module.Flat.trans R S ((ModuleCat.restrictScalars f).obj N)

/-- Flatness of an actual restricted stalk implies flatness at the same original point. -/
theorem stalk_flat_of_restrict {X Y : Scheme.{u}} (f : X ⟶ Y) [IsOpenImmersion f]
    (x : X) (M : Y.Modules)
    (h : Module.Flat (X.presheaf.stalk x)
      ((moduleStalk X x).obj ((Scheme.Modules.restrictFunctor f).obj M))) :
    Module.Flat (Y.presheaf.stalk (f x)) ((moduleStalk Y (f x)).obj M) := by
  let := h
  let : Module.Flat (Y.presheaf.stalk (f x))
      ((Scheme.Modules.restrictFunctor f ⋙ moduleStalk X x ⋙
        ModuleCat.restrictScalars (f.stalkMap x).hom).obj M) :=
    flat_restrictScalars (f.stalkMap x).hom (Flat.stalkMap f x)
      ((moduleStalk X x).obj ((Scheme.Modules.restrictFunctor f).obj M))
  exact Module.Flat.of_linearEquiv ((restrictModuleStalkIso f x).app M).symm.toLinearEquiv

/-- Genuine flatness is preserved by actual open restriction. -/
theorem stalkwiseFlat_restrict {X Y : Scheme.{u}} (f : X ⟶ Y) [IsOpenImmersion f]
    {M : Y.Modules} (hM : stalkwiseFlat Y M) :
    stalkwiseFlat X ((Scheme.Modules.restrictFunctor f).obj M) := by
  intro x
  let : Module.Flat (X.presheaf.stalk x)
      ((moduleStalk X x).obj ((Scheme.Modules.pullback f).obj M)) :=
    stalkwiseFlat_pullback f hM x
  exact Module.Flat.of_linearEquiv ((moduleStalk X x).mapIso
    ((Scheme.Modules.restrictFunctorIsoPullback f).app M)).toLinearEquiv

/-- Stalkwise flatness can be checked on one actual neighborhood of each point. -/
theorem stalkwiseFlat_of_locally_restrict {X : Scheme.{u}} (M : X.Modules)
    (h : ∀ x : X, ∃ U : X.Opens, x ∈ U ∧
      stalkwiseFlat U.toScheme (M.restrict U.ι)) : stalkwiseFlat X M := by
  intro x
  obtain ⟨U, hx, hU⟩ := h x
  exact stalk_flat_of_restrict U.ι ⟨x, hx⟩ M (hU ⟨x, hx⟩)

end AlgebraicGeometry.Scheme.Modules
