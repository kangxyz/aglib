/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Modules.QuasiCoherent.Affine.TildeExact
public import Aglib.AlgebraicGeometry.Modules.QuasiCoherent.Limits
public import Aglib.RingTheory.AdicCompletion.BoundedKernelSeparation

/-! # Actual finite-stage joint monomorphisms on affine schemes

Global sections are used only between quasicoherent sheaves. No reflection
property for maps into arbitrary inverse-limit sheaves is asserted.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Scheme.Modules

universe u
variable (B : CommRingCat.{u})

/-- Global sections detect monomorphisms between quasicoherent affine sheaves. -/
theorem mono_of_mono_globalSections {M N : (Spec B).Modules}
    [M.IsQuasicoherent] [N.IsQuasicoherent] (f : M ⟶ N)
    [Mono (moduleSpecΓFunctor.map f)] : Mono f := by
  have : IsIso M.fromTildeΓ := isIso_fromTildeΓ_of_isQuasicoherent M
  have : IsIso N.fromTildeΓ := isIso_fromTildeΓ_of_isQuasicoherent N
  have h := fromTildeΓNatTrans.naturality f
  change (tilde.functor B).map (moduleSpecΓFunctor.map f) ≫ N.fromTildeΓ =
    M.fromTildeΓ ≫ f at h
  have : Mono ((tilde.functor B).map (moduleSpecΓFunctor.map f)) :=
    (tilde.functor B).map_mono _
  have : Mono (M.fromTildeΓ ≫ f) := by
    rw [← h]
    infer_instance
  exact (mono_comp_iff_of_isIso M.fromTildeΓ f).mp inferInstance

/-- An actual pair of affine quasicoherent maps is jointly monic if and only
if the two section kernels have trivial intersection; here only the needed
implication is used. -/
theorem mono_prod_lift_of_sections_ker_inf_eq_bot
    {M N P : (Spec B).Modules} [M.IsQuasicoherent]
    [N.IsQuasicoherent] [P.IsQuasicoherent] (a : M ⟶ N) (b : M ⟶ P)
    (h : (moduleSpecΓFunctor.map a).hom.ker ⊓
      (moduleSpecΓFunctor.map b).hom.ker = ⊥) : Mono (prod.lift a b) := by
  have hi : Function.Injective
      ((moduleSpecΓFunctor.map a).hom.prod (moduleSpecΓFunctor.map b).hom) := by
    apply LinearMap.ker_eq_bot.mp
    rw [LinearMap.ker_prod, h]
  have : Mono (moduleSpecΓFunctor.map (prod.lift a b)) := by
    apply (ModuleCat.mono_iff_injective _).mpr
    intro x y hxy
    apply hi
    apply Prod.ext
    · change moduleSpecΓFunctor.map a x = moduleSpecΓFunctor.map a y
      have hp := congrArg (moduleSpecΓFunctor.map (prod.fst : N ⨯ P ⟶ N)) hxy
      simpa only [← ConcreteCategory.comp_apply, ← Functor.map_comp, prod.lift_fst] using hp
    · change moduleSpecΓFunctor.map b x = moduleSpecΓFunctor.map b y
      have hp := congrArg (moduleSpecΓFunctor.map (prod.snd : N ⨯ P ⟶ P)) hxy
      simpa only [← ConcreteCategory.comp_apply, ← Functor.map_comp, prod.lift_snd] using hp
  let : (N ⨯ P).IsQuasicoherent := by
    apply (SheafOfModules.isQuasicoherent (Spec B).ringCatSheaf).prop_of_isLimit
      (prodIsProd N P)
    rintro (_ | _) <;> assumption
  exact mono_of_mono_globalSections B (prod.lift a b)

end AlgebraicGeometry.Scheme.Modules
