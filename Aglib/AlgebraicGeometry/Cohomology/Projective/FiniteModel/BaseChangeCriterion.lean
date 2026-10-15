/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Cohomology.Projective.FiniteModel.BaseChange

/-!
# Detecting original cohomology base change on the actual projective model

The proved linear square identifies invertibility and surjectivity of the
original geometric cohomology base-change map with the same properties of
the native homology mate of the constructed model. The original cohomology
carriers stay in universe `u+1`, and the actual model stays in universe `u`.
The comparisons use the existing scalar-extension linear equivalences;
no alternate cohomology object or new base-change map is introduced.
-/

@[expose] public section

noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry HomologicalComplex
open AlgebraicGeometry.ProjectiveSpace

namespace AlgebraicGeometry.Scheme.Cohomology.ProjectiveCohomologyModel

universe u

variable {R : Type u} [CommRing R] {ι : Type u} {X : Scheme.{u}}
    {i : X ⟶ ProjectiveSpace R ι} [IsClosedImmersion i]
    {f : X ⟶ Spec (CommRingCat.of R)} {M : X.Modules} [M.IsQuasicoherent] {n : ℕ}
    (D : ProjectiveCohomologyModel R ι i f M n) (e : ι ≃ Fin (n + 1))
    (hflat : Scheme.Modules.relativeFlat f M) {B : Type u} [CommRing B] (σ : R →+* B)

include e hflat

/-- Invertibility of the original cohomology base-change map is detected by the native
homology mate on the same actual finite-projective model. -/
theorem moduleCohomologyBaseChangeMap_isIso_iff (q : ℕ) :
    IsIso (moduleCohomologyBaseChangeMap f σ M q) ↔
      IsIso (extendScalarsHomologyMap σ D.complex (q : ℤ)) := by
  let := σ.toAlgebra
  let α := f.appTop.hom.comp (Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom
  let Y := pullback f (Spec.map (CommRingCat.ofHom σ))
  let p := pullback.fst f (Spec.map (CommRingCat.ofHom σ))
  let r := pullback.snd f (Spec.map (CommRingCat.ofHom σ))
  let N := (Scheme.Modules.pullback p).obj M
  let β := r.appTop.hom.comp (Scheme.ΓSpecIso (CommRingCat.of B)).inv.hom
  let := moduleCohomologyModuleOfHom X α M q
  let := moduleCohomologyModuleOfHom Y β N q
  let a := (D.cohomologyLinearEquiv e q).baseChange R B _ _
  let b := D.baseChangeCohomologyLinearEquiv e hflat σ q
  let ψ := moduleCohomologyBaseChangeMap f σ M q
  let ρ := extendScalarsHomologyMap σ D.complex (q : ℤ)
  have hs : ψ.hom.comp a.toLinearMap = b.toLinearMap.comp ρ.hom :=
    D.baseChangeCohomologyLinearEquiv_homologyBaseChangeMap e hflat σ q
  have hs' : (fun x => ψ (a x)) = fun x => b (ρ x) :=
    funext (fun x => LinearMap.congr_fun hs x)
  change IsIso ψ ↔ IsIso ρ
  rw [ConcreteCategory.isIso_iff_bijective, ConcreteCategory.isIso_iff_bijective]
  calc
    Function.Bijective ψ ↔ Function.Bijective (fun x => ψ (a x)) :=
      (Function.Bijective.of_comp_iff ψ a.bijective).symm
    _ ↔ Function.Bijective (fun x => b (ρ x)) := by rw [hs']
    _ ↔ Function.Bijective ρ := Function.Bijective.of_comp_iff' b.bijective ρ

/-- Surjectivity of the original cohomology base-change map is detected by the original
native model mate. This applies to arbitrary ring maps before a degreewise isomorphism
criterion is known. -/
theorem moduleCohomologyBaseChangeMap_epi_iff (q : ℕ) :
    Epi (moduleCohomologyBaseChangeMap f σ M q) ↔
      Epi (extendScalarsHomologyMap σ D.complex (q : ℤ)) := by
  let := σ.toAlgebra
  let α := f.appTop.hom.comp (Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom
  let Y := pullback f (Spec.map (CommRingCat.ofHom σ))
  let p := pullback.fst f (Spec.map (CommRingCat.ofHom σ))
  let r := pullback.snd f (Spec.map (CommRingCat.ofHom σ))
  let N := (Scheme.Modules.pullback p).obj M
  let β := r.appTop.hom.comp (Scheme.ΓSpecIso (CommRingCat.of B)).inv.hom
  let := moduleCohomologyModuleOfHom X α M q
  let := moduleCohomologyModuleOfHom Y β N q
  let a := (D.cohomologyLinearEquiv e q).baseChange R B _ _
  let b := D.baseChangeCohomologyLinearEquiv e hflat σ q
  let ψ := moduleCohomologyBaseChangeMap f σ M q
  let ρ := extendScalarsHomologyMap σ D.complex (q : ℤ)
  have hs : ψ.hom.comp a.toLinearMap = b.toLinearMap.comp ρ.hom :=
    D.baseChangeCohomologyLinearEquiv_homologyBaseChangeMap e hflat σ q
  have hs' : (fun x => ψ (a x)) = fun x => b (ρ x) :=
    funext (fun x => LinearMap.congr_fun hs x)
  change Epi ψ ↔ Epi ρ
  rw [ModuleCat.epi_iff_surjective, ModuleCat.epi_iff_surjective]
  calc
    Function.Surjective ψ ↔ Function.Surjective (fun x => ψ (a x)) :=
      (Function.Surjective.of_comp_iff ψ a.surjective).symm
    _ ↔ Function.Surjective (fun x => b (ρ x)) := by rw [hs']
    _ ↔ Function.Surjective ρ := Function.Surjective.of_comp_iff' b.bijective ρ

end AlgebraicGeometry.Scheme.Cohomology.ProjectiveCohomologyModel
