/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Modules.QuasiCoherent.Affine.TildeExact
/-! # Exactness detected by actual affine global sections

For quasicoherent module sheaves on an arbitrary affine scheme, the original tilde counit
transports exactness and epimorphisms of the original global-section maps to sheaf maps.
-/
@[expose] public section

noncomputable section
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

namespace AlgebraicGeometry.Scheme.Modules
/-- Actual global-section exactness detects exactness of quasicoherent affine sheaves. -/
theorem exact_of_exact_globalSections (R : CommRingCat.{u})
    (S : ShortComplex (Spec R).Modules)
    [S.X₁.IsQuasicoherent] [S.X₂.IsQuasicoherent] [S.X₃.IsQuasicoherent]
    (h : (S.map moduleSpecΓFunctor).Exact) : S.Exact := by
  have : IsIso S.X₁.fromTildeΓ := Scheme.Modules.isIso_fromTildeΓ_of_isQuasicoherent S.X₁
  have : IsIso S.X₂.fromTildeΓ := Scheme.Modules.isIso_fromTildeΓ_of_isQuasicoherent S.X₂
  have : IsIso S.X₃.fromTildeΓ := Scheme.Modules.isIso_fromTildeΓ_of_isQuasicoherent S.X₃
  let e : (S.map moduleSpecΓFunctor).map (tilde.functor R) ≅ S :=
    ShortComplex.isoMk (asIso S.X₁.fromTildeΓ) (asIso S.X₂.fromTildeΓ)
      (asIso S.X₃.fromTildeΓ)
      (Scheme.Modules.fromTildeΓNatTrans.naturality S.f).symm
      (Scheme.Modules.fromTildeΓNatTrans.naturality S.g).symm
  exact ShortComplex.exact_of_iso e (h.map (tilde.functor R))
/-- Surjectivity of the original global-section map detects an affine quasicoherent epimorphism. -/
theorem epi_of_epi_globalSections (R : CommRingCat.{u})
    {M N : (Spec R).Modules} [M.IsQuasicoherent] [N.IsQuasicoherent]
    (f : M ⟶ N) [Epi (moduleSpecΓFunctor.map f)] : Epi f := by
  have : IsIso M.fromTildeΓ := Scheme.Modules.isIso_fromTildeΓ_of_isQuasicoherent M
  have : IsIso N.fromTildeΓ := Scheme.Modules.isIso_fromTildeΓ_of_isQuasicoherent N
  have h := Scheme.Modules.fromTildeΓNatTrans.naturality f
  change (tilde.functor R).map (moduleSpecΓFunctor.map f) ≫ N.fromTildeΓ =
    M.fromTildeΓ ≫ f at h
  have : Epi (M.fromTildeΓ ≫ f) := by
    rw [← h]
    infer_instance
  exact epi_of_epi M.fromTildeΓ f
end AlgebraicGeometry.Scheme.Modules
