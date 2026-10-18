/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Cohomology.BaseChange.Modules.Map.Spec
public import Aglib.AlgebraicGeometry.Cohomology.Functoriality.Modules.Composition
public import Aglib.AlgebraicGeometry.Cohomology.Modules.Functor

/-!
# Naturality of cohomology base change in the coefficients

The original cohomology base-change map `B ⊗_A H^n(X, M) ⟶ H^n(X_B, M_B)` over spectra is natural
in the coefficient module (`moduleCohomologyBaseChangeMap_naturality`). The input is the
naturality of geometric module pullback on cohomology, `moduleCohomologyPullback_map` (in
`Cohomology/Functoriality/Modules/Composition`), which rests on the naturality of the actual
inverse-image map for commuting coefficient squares, `zariskiCohomologyMap_map` (in
`Cohomology/Functoriality/Pullback`). No flatness, quasicoherence or finiteness is used.
-/

@[expose] public section

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace
open scoped TensorProduct ChangeOfRings

universe u

namespace AlgebraicGeometry.Scheme.Cohomology

/-- **Naturality of the cohomology base-change map** over spectra, in the coefficient module:
for `φ : M ⟶ M'` on `X` over `Spec A` and `σ : A →+* B`, the square formed by
`B ⊗_A H^n(X, φ)`, the base-change maps of `M` and `M'`, and `H^n(X_B, φ_B)` commutes. -/
theorem moduleCohomologyBaseChangeMap_naturality {X : Scheme.{u}} {A B : Type u} [CommRing A]
    [CommRing B] (f : X ⟶ Spec (CommRingCat.of A)) (σ : A →+* B) {M M' : X.Modules}
    (φ : M ⟶ M') (n : ℕ) :
    let α := f.appTop.hom.comp (Scheme.ΓSpecIso (CommRingCat.of A)).inv.hom
    let p := pullback.fst f (Spec.map (CommRingCat.ofHom σ))
    let β := (pullback.snd f (Spec.map (CommRingCat.ofHom σ))).appTop.hom.comp
      (Scheme.ΓSpecIso (CommRingCat.of B)).inv.hom
    letI := moduleCohomologyModuleOfHom X α M n
    letI := moduleCohomologyModuleOfHom X α M' n
    letI := moduleCohomologyModuleOfHom (pullback f (Spec.map (CommRingCat.ofHom σ))) β
      ((Scheme.Modules.pullback p).obj M) n
    letI := moduleCohomologyModuleOfHom (pullback f (Spec.map (CommRingCat.ofHom σ))) β
      ((Scheme.Modules.pullback p).obj M') n
    (ModuleCat.extendScalars σ).map (ModuleCat.ofHom (moduleCohomologyMapOfHom X α φ n)) ≫
        moduleCohomologyBaseChangeMap f σ M' n =
      moduleCohomologyBaseChangeMap f σ M n ≫
        ModuleCat.ofHom (moduleCohomologyMapOfHom _ β ((Scheme.Modules.pullback p).map φ) n) := by
  intro α p β
  simp only [moduleCohomologyBaseChangeMap, moduleCohomologyTensorMap]
  rw [← Adjunction.homEquiv_naturality_left_symm, ← Adjunction.homEquiv_naturality_right_symm]
  congr 1
  let := moduleCohomologyModuleOfHom X α M n
  refine ModuleCat.hom_ext (LinearMap.ext fun x => ?_)
  exact moduleCohomologyPullback_map p φ n x

end AlgebraicGeometry.Scheme.Cohomology
