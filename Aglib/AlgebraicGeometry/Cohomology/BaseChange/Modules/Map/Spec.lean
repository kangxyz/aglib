/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Cohomology.BaseChange.Modules.Map
public import Aglib.AlgebraicGeometry.Cohomology.BaseChange.Modules.Sections

/-!
# The canonical module cohomology base-change map over spectra

This is the original scalar-adjunction mate on actual `Sheaf.H`, specialized
to the genuine fibre product over a homomorphism of commutative rings. Its
structural actions use the original `ΓSpecIso` and its coefficient arrow is
the native module pullback unit. The specialization is an abbreviation of the
general map, with no flatness or quasicoherence premise for its construction.
-/

@[expose] public section

noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped TensorProduct ChangeOfRings

namespace AlgebraicGeometry.Scheme.Cohomology

universe u

variable {X : Scheme.{u}} {A B : Type u} [CommRing A] [CommRing B]

/-- The original tensor mate on cohomology of the actual fibre product over spectra. -/
abbrev moduleCohomologyBaseChangeMap (f : X ⟶ Spec (CommRingCat.of A)) (σ : A →+* B)
    (M : X.Modules) (n : ℕ) :=
  let p := pullback.fst f (Spec.map (CommRingCat.ofHom σ))
  let q := pullback.snd f (Spec.map (CommRingCat.ofHom σ))
  let α := f.appTop.hom.comp (Scheme.ΓSpecIso (CommRingCat.of A)).inv.hom
  let β := q.appTop.hom.comp (Scheme.ΓSpecIso (CommRingCat.of B)).inv.hom
  moduleCohomologyTensorMap (M := M) (N := (Scheme.Modules.pullback p).obj M) p σ α β
    (moduleSectionsBaseChangeScalars p q f σ pullback.condition)
    ((Scheme.Modules.pullbackPushforwardAdjunction p).unit.app M) n

/-- On the unit pure tensor the canonical map is the original geometric module pullback. -/
theorem moduleCohomologyBaseChangeMap_one_tmul
    (f : X ⟶ Spec (CommRingCat.of A)) (σ : A →+* B) (M : X.Modules) (n : ℕ)
    (x : Sheaf.H.{u + 1} (moduleAddSheaf X M) n) :
    let α := f.appTop.hom.comp (Scheme.ΓSpecIso (CommRingCat.of A)).inv.hom
    let := moduleCohomologyModuleOfHom X α M n
    moduleCohomologyBaseChangeMap f σ M n ((1 : B) ⊗ₜ[A,σ] x) =
      moduleCohomologyPullback (pullback.fst f (Spec.map (CommRingCat.ofHom σ))) M n x := by
  let α := f.appTop.hom.comp (Scheme.ΓSpecIso (CommRingCat.of A)).inv.hom
  let := moduleCohomologyModuleOfHom X α M n
  exact moduleCohomologyTensorMap_one_tmul (M := M) _ _ _ _ _ _ n x

end AlgebraicGeometry.Scheme.Cohomology
