/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Modules.Locality.Exactness
/-! # Monomorphisms detected by original open restrictions

The original kernel vanishes if its restrictions vanish on a jointly surjective family
of open immersions. The original restriction-to-pullback comparison also preserves monicity.
-/
@[expose] public section

noncomputable section
universe u v
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

namespace AlgebraicGeometry.Scheme.Modules
/-- Actual restriction detects monomorphisms on a jointly surjective open family. -/
theorem mono_of_restrict_openCover {X : Scheme.{u}} {ι : Type v}
    (Y : ι → Scheme.{u}) (a : ∀ i, Y i ⟶ X) [∀ i, IsOpenImmersion (a i)]
    (hcover : ∀ x : X, ∃ (i : ι) (y : Y i), a i y = x)
    {M N : X.Modules} (f : M ⟶ N)
    (hf : ∀ i, Mono ((Scheme.Modules.restrictFunctor (a i)).map f)) : Mono f := by
  apply Preadditive.mono_of_isZero_kernel
  apply isZero_of_restrict_openCover Y a hcover
  intro i
  let := hf i
  exact (isZero_kernel_of_mono ((Scheme.Modules.restrictFunctor (a i)).map f)).of_iso
    (PreservesKernel.iso (Scheme.Modules.restrictFunctor (a i)) f)
/-- Monicity of the original pullback along an open immersion gives monicity of restriction. -/
theorem mono_restrict_of_mono_pullback {X Y : Scheme.{u}} (j : Y ⟶ X)
    [IsOpenImmersion j] {M N : X.Modules} (f : M ⟶ N)
    [Mono ((Scheme.Modules.pullback j).map f)] :
    Mono ((Scheme.Modules.restrictFunctor j).map f) := by
  let e := Scheme.Modules.restrictFunctorIsoPullback j
  have : Mono ((Scheme.Modules.restrictFunctor j).map f ≫ e.hom.app N) := by
    rw [e.hom.naturality]
    infer_instance
  exact mono_of_mono _ (e.hom.app N)
end AlgebraicGeometry.Scheme.Modules
