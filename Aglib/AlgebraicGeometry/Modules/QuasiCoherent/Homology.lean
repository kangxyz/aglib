/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Modules.QuasiCoherent.Limits
public import Mathlib.Algebra.Homology.ShortComplex.HomologicalComplex

/-! # Local quasicoherence and homology

Quasicoherence can be checked on actual open neighborhoods. The homology of
a termwise quasicoherent complex is quasicoherent on every scheme; no
Noetherianity or boundedness hypothesis is imposed.

Source: `Quillen/AlgebraicGeometry/PerfectComplexes/Homology.lean`,
archive SHA-256
`16c127c5b7a5874cb4d841e1161b436190c35aeb08802b89cb19fd8c76ad1d48`,
source SHA-256 `bfb93dda9ff5df57674129b0a5255631ac11bebebaab26d50426b51f4fdbaf34`.
The accepted consumer-retargeted input has SHA-256
`5c3aa2c2a65dfad3868fb1cb2e0114e3bf41693497a51c3497640d7e6d0b5d8a`.
Admitted subset: quasicoherent_of_openNeighborhoods and quasicoherent_homology.
-/

@[expose] public section

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

open TopologicalSpace

namespace AlgebraicGeometry.Scheme.Modules.QuasiCoherent

/-- Quasicoherence is local on actual open neighborhoods. -/
theorem quasicoherent_of_openNeighborhoods {X : Scheme.{u}} (M : X.Modules)
    (hM : ∀ x : X, ∃ U : X.Opens, x ∈ U ∧ (M.restrict U.ι).IsQuasicoherent) :
    M.IsQuasicoherent := by
  classical
  have h (x : X) : ∃ V : X.affineOpens, x ∈ V.1 ∧
      (M.restrict V.2.fromSpec).IsQuasicoherent := by
    obtain ⟨U, hxU, hU⟩ := hM x
    obtain ⟨_, ⟨V : X.Opens, hV, rfl⟩, hxV, hVU⟩ :=
      X.isBasis_affineOpens.exists_subset_of_mem_open hxU U.isOpen
    let j := X.homOfLE hVU
    have : ((M.restrict U.ι).restrict j).IsQuasicoherent := inferInstance
    let e : (M.restrict U.ι).restrict j ≅ M.restrict V.ι :=
      ((Scheme.Modules.restrictFunctorComp j U.ι).app M).symm ≪≫
        (Scheme.Modules.restrictFunctorCongr (by simp [j])).app M
    have : (M.restrict V.ι).IsQuasicoherent :=
      (SheafOfModules.isQuasicoherent V.toScheme.ringCatSheaf).prop_of_iso e inferInstance
    have : ((M.restrict V.ι).restrict hV.isoSpec.inv).IsQuasicoherent := inferInstance
    let e' : (M.restrict V.ι).restrict hV.isoSpec.inv ≅ M.restrict hV.fromSpec :=
      ((Scheme.Modules.restrictFunctorComp hV.isoSpec.inv V.ι).app M).symm
    exact ⟨⟨V, hV⟩, hxV,
      (SheafOfModules.isQuasicoherent (Spec Γ(X, V)).ringCatSheaf).prop_of_iso e' inferInstance⟩
  choose V hV hq using h
  let q : M.QuasicoherentData :=
    { I := X
      X := fun x => (V x).1
      coversTop := by
        rw [Opens.coversTop_iff, IsOpenCover]
        apply top_unique
        intro x _
        exact Opens.mem_iSup.mpr ⟨x, hV x⟩
      presentation x := affinePresentationToOver M (V x)
        (affineQuasicoherent_exists_presentation _ (M.restrict (V x).2.fromSpec)).some }
  exact q.isQuasicoherent

/-- Homology of an actual termwise quasicoherent sheaf complex is
quasicoherent, on an arbitrary scheme. -/
theorem quasicoherent_homology {X : Scheme.{u}} (K : CochainComplex X.Modules ℤ)
    (hK : ∀ i, (K.X i).IsQuasicoherent) (i : ℤ) : (K.homology i).IsQuasicoherent := by
  let S := K.sc i
  have : S.X₁.IsQuasicoherent := hK _
  have : S.X₂.IsQuasicoherent := hK _
  have : S.X₃.IsQuasicoherent := hK _
  have : (kernel S.g).IsQuasicoherent := quasicoherent_kernel S.g
  have h := quasicoherent_cokernel (kernel.lift S.g S.f S.zero)
  exact (SheafOfModules.isQuasicoherent X.ringCatSheaf).prop_of_iso
    S.homologyIsoCokernelLift.symm h

end AlgebraicGeometry.Scheme.Modules.QuasiCoherent
