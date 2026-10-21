/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Modules.Rees.Image
public import Aglib.AlgebraicGeometry.Modules.QuasiCoherent.Extensions.AffineSections

/-!
# Actual affine sections of quasicoherent images

Global sections identify the actual image sheaf with the linear-map range
of the original section map. The statement is restricted to quasicoherent
source and target; it does not assert exactness of sections on all sheaves.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

universe u
open CategoryTheory Limits

namespace AlgebraicGeometry.Scheme.Modules

variable (R : CommRingCat.{u}) {M N : (Spec R).Modules}
  [M.IsQuasicoherent] [N.IsQuasicoherent] (φ : M ⟶ N)

/-- The canonical map to the image remains surjective on affine sections. -/
theorem affineSections_factorThruImage_surjective :
    Function.Surjective ((moduleSpecΓFunctor (R := R)).map (Abelian.factorThruImage φ)) := by
  let := QuasiCoherent.quasicoherent_kernel φ
  let κ : kernel φ ⟶ M := kernel.ι φ
  have hS : (ShortComplex.mk κ (cokernel.π κ) (cokernel.condition κ)).ShortExact :=
    { exact := ShortComplex.exact_cokernel κ }
  have hs := (ModuleCat.epi_iff_surjective _).mp
    (AffineCech.epi_globalSections_of_quasicoherent_kernel hS)
  let e := (moduleSpecΓFunctor (R := R)).mapIso (Abelian.coimageIsoImage φ)
  have hfac : cokernel.π κ ≫ (Abelian.coimageIsoImage φ).hom =
      Abelian.factorThruImage φ := by
    apply (cancel_mono (Abelian.image.ι φ)).mp
    exact (Abelian.coimage_image_factorisation φ).trans (Abelian.image.fac φ).symm
  have hm := congrArg (moduleSpecΓFunctor (R := R)).map hfac
  rw [Functor.map_comp] at hm
  intro x
  obtain ⟨m, hmx⟩ := hs (e.inv x)
  refine ⟨m, ?_⟩
  rw [← hm]
  change e.hom ((moduleSpecΓFunctor (R := R)).map (cokernel.π κ) m) = x
  rw [hmx]
  exact e.toLinearEquiv.apply_symm_apply x

/-- The sectionwise range of the actual image inclusion equals that of the original map. -/
theorem affineSections_image_range :
    LinearMap.range ((moduleSpecΓFunctor (R := R)).map (Abelian.image.ι φ)).hom =
      LinearMap.range ((moduleSpecΓFunctor (R := R)).map φ).hom := by
  ext n
  constructor
  · rintro ⟨x, rfl⟩
    obtain ⟨m, rfl⟩ := affineSections_factorThruImage_surjective R φ x
    refine ⟨m, ?_⟩
    have h := congrArg (moduleSpecΓFunctor (R := R)).map (Abelian.image.fac φ)
    rw [Functor.map_comp] at h
    exact (congrArg (fun k => k m) h).symm
  · rintro ⟨m, rfl⟩
    refine ⟨((moduleSpecΓFunctor (R := R)).map (Abelian.factorThruImage φ)) m, ?_⟩
    have h := congrArg (moduleSpecΓFunctor (R := R)).map (Abelian.image.fac φ)
    rw [Functor.map_comp] at h
    exact congrArg (fun k => k m) h

end AlgebraicGeometry.Scheme.Modules
