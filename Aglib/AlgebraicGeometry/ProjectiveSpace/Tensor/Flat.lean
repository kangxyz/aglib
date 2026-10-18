/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Modules.Flat.Relative.Coproduct
public import Aglib.AlgebraicGeometry.Modules.Flat.Relative.Tensor
public import Aglib.AlgebraicGeometry.Modules.Flat.Relative.Unit
public import Aglib.AlgebraicGeometry.ProjectiveSpace.Flat
public import Aglib.AlgebraicGeometry.ProjectiveSpace.Tensor.Equivalence

/-!
# Relative flatness of twists on projective space

Let `P = ProjectiveSpace R ι` and `f : P ⟶ Y` any morphism. The twisting sheaf `𝒪(d)` is trivial
on each standard chart (`twistingRestrictUnitIso`), so twisting preserves relative flatness over
`Y` (`twistingTensor_relativeFlat`). Over `Spec R`, the structure morphism is flat (`flat_toSpec`),
so every twisting sheaf and every sum of twisting sheaves is relatively flat over `Spec R`
(`twistingSheaf_relativeFlat`, `twistingCoproduct_relativeFlat`). No finiteness or Noetherian
hypothesis is used. The flatness of the structure module over a flat morphism is
`relativeFlat_unit_of_flat` (`Modules/Flat/Relative/Unit`).
-/

@[expose] public section

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open AlgebraicGeometry.Scheme.Modules

universe u

namespace AlgebraicGeometry.ProjectiveSpace

/-- **Twists of a relatively flat module are relatively flat**: the twisting sheaf `𝒪(d)` is
trivial on each standard chart (`twistingRestrictUnitIso`). -/
theorem twistingTensor_relativeFlat {R : Type u} [CommRing R] {ι : Type u} {Y : Scheme.{u}}
    (f : ProjectiveSpace R ι ⟶ Y) (M : (ProjectiveSpace R ι).Modules) (hM : relativeFlat f M)
    (d : ℤ) :
    relativeFlat f ((moduleTensorLeftFunctor (ProjectiveSpace R ι) (twistingSheaf R ι d)).obj M) :=
  relativeFlat_tensor_of_locallyTrivial f _ M (fun x => by
    obtain ⟨i, hi⟩ := TopologicalSpace.Opens.mem_iSup.mp
      (show x ∈ iSup (coordinateOpen R ι) by
        rw [iSup_coordinateOpen_eq_top]
        trivial)
    exact ⟨coordinateOpen R ι i, hi, ⟨twistingRestrictUnitIso R ι d i⟩⟩) hM

/-- The twisting sheaves are relatively flat over the base: `𝒪(d) ≅ 𝒪(d) ⊗ 𝒪` and
`P^n_R ⟶ Spec R` is flat. -/
theorem twistingSheaf_relativeFlat (R : Type u) [CommRing R] (ι : Type u) (d : ℤ) :
    relativeFlat (toSpec R ι) (twistingSheaf R ι d) :=
  relativeFlat_of_iso (toSpec R ι)
    (tensorSheafBraiding _ (twistingSheaf R ι d) (SheafOfModules.unit _) ≪≫
      tensorSheafLeftUnit _ (twistingSheaf R ι d)).symm
    (twistingTensor_relativeFlat (toSpec R ι) (SheafOfModules.unit _)
      (relativeFlat_unit_of_flat (toSpec R ι)) d)

/-- A sum of twists is relatively flat over the base. -/
theorem twistingCoproduct_relativeFlat (R : Type u) [CommRing R] (ι : Type u) {I : Type u}
    (d : I → ℤ) : relativeFlat (toSpec R ι) (∐ fun i => twistingSheaf R ι (d i)) :=
  relativeFlat_coproduct _ _ fun i => twistingSheaf_relativeFlat R ι (d i)

end AlgebraicGeometry.ProjectiveSpace
