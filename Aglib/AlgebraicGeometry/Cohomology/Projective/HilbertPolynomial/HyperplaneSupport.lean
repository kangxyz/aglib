/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Modules.Coherent.Support.Hypersurface
public import Aglib.AlgebraicGeometry.ProjectiveSpace.Tensor.Monoidal.FreeDegree

/-!
# Support of the original projective section-multiplication cokernel

The original map formed from `twistingTensorZeroIso` and
`twistingTensorMultiply` is native `unitMultiply` followed by an actual
tensor isomorphism. Its original cokernel therefore has exactly the support
given by the finite-type line-section theorem. No replacement multiplication
map, monomorphism or regularity premise is used.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open AlgebraicGeometry.Scheme.Modules AlgebraicGeometry.Scheme.Modules.QuasiCoherent
open AlgebraicGeometry.Scheme.Modules.Invertible

universe u

namespace AlgebraicGeometry.ProjectiveSpace

-- Native twist tensor functors and the original monoidal tensor have the same module carrier.
set_option backward.isDefEq.respectTransparency false in
/-- The native twist-multiplication cokernel is supported precisely on
the original coefficient support where the original twist section vanishes. -/
theorem support_cokernel_twistingTensorMultiply
    (R : Type u) [CommRing R] (ι : Type u) (a : ℤ)
    (s : Γ(twistingSheaf R ι a, ⊤)) (F : (ProjectiveSpace R ι).Modules)
    (hF : affineLocallyFiniteType (ProjectiveSpace R ι) F) :
    support (cokernel ((twistingTensorZeroIso R ι).inv.app F ≫
      (twistingTensorMultiply R ι a 0 s).app F)) =
      support F ∩ (nonvanishingOpen (twistingLineBundle R ι a) s : Set (ProjectiveSpace R ι))ᶜ := by
  let A := twistingSheaf R ι a
  let B := twistingSheaf R ι 0
  let e₀ : F ≅ B ⊗ F := ((twistingTensorZeroIso R ι).app F).symm
  let σ : (𝟙_ (ProjectiveSpace R ι).Modules) ⟶ A := twistingSectionUnitHom s
  let E : A ⊗ F ≅ twistingSheaf R ι (a + 0) ⊗ F :=
    whiskerLeftIso A e₀ ≪≫ (α_ A B F).symm ≪≫
      whiskerRightIso (twistingTensorIso R ι a 0) F
  let ν := (twistingTensorZeroIso R ι).inv.app F ≫
    (twistingTensorMultiply R ι a 0 s).app F
  have hν : ν = unitMultiply σ F ≫ E.hom := by
    change e₀.hom ≫ (twistingTensorMultiply R ι a 0 s).app F = _
    rw [twistingTensorMultiply_app_eq_unitMultiply]
    have hn := congrArg (fun z : F ⟶ A ⊗ (B ⊗ F) =>
      z ≫ (α_ A B F).inv ≫ (twistingTensorIso R ι a 0).hom ▷ F)
        (unitMultiply_naturality σ e₀.hom)
    simpa only [E, Iso.trans_hom, Iso.symm_hom, whiskerLeftIso_hom,
      whiskerRightIso_hom, twistingTensorIso_hom, Category.assoc] using hn
  let eC := cokernelIsoOfEq hν ≪≫ cokernelCompIsIso (unitMultiply σ F) E.hom
  exact (support_eq_of_iso eC).trans
    (support_cokernel_tensor_section (twistingLineBundle R ι a) s F hF)

end AlgebraicGeometry.ProjectiveSpace
