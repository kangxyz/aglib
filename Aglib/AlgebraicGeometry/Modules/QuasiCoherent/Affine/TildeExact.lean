/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Modules.QuasiCoherent.Affine.Sections
public import Mathlib.CategoryTheory.Abelian.Exact
public import Mathlib.Algebra.Homology.ShortComplex.PreservesHomology
/-! # Exactness of the actual affine tilde functor

The tilde functor on modules over every commutative ring preserves monomorphisms by
injectivity of localized module maps. Its existing adjunction then gives preservation of
homology and finite limits. No finiteness or noetherianity hypothesis is required.
-/
@[expose] public section

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
namespace AlgebraicGeometry.Scheme.Modules
variable (R : CommRingCat.{u})

lemma tilde_map_app_injective {M N : ModuleCat.{u} R} (f : M ⟶ N)
    (hf : Function.Injective f) (U : (Spec R).Opens) :
    Function.Injective ((tilde.map f).app U) := by
  intro s t h
  apply Subtype.ext
  funext x
  apply IsLocalizedModule.map_injective x.1.asIdeal.primeCompl
    (LocalizedModule.mkLinearMap x.1.asIdeal.primeCompl M)
    (LocalizedModule.mkLinearMap x.1.asIdeal.primeCompl N) f.hom hf
  exact congrArg (fun a => a.val x) h

instance tilde_preservesMonomorphisms : (tilde.functor R).PreservesMonomorphisms where
  preserves {M N} f hf := by
    constructor
    intro P g h hgh
    apply Scheme.Modules.hom_ext
    intro U
    ext s
    apply tilde_map_app_injective R f ((ModuleCat.mono_iff_injective f).mp hf) U
    exact congrArg (fun a => a.app U s) hgh

instance tilde_preservesHomology : (tilde.functor R).PreservesHomology :=
  (tilde.functor R).preservesHomology_of_preservesMonos_and_cokernels

instance tilde_preservesFiniteLimits : PreservesFiniteLimits (tilde.functor R) :=
  (tilde.functor R).preservesFiniteLimits_of_preservesHomology

end AlgebraicGeometry.Scheme.Modules
