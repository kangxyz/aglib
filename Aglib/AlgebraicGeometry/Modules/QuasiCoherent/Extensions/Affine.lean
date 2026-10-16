/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Modules.QuasiCoherent.Extensions.AffineSections
public import Aglib.AlgebraicGeometry.Modules.QuasiCoherent.Affine.TildeExact
public import Aglib.AlgebraicGeometry.Modules.QuasiCoherent.Affine.FiniteTypeProperty

/-!
# Actual affine quasicoherent extension closure

The original tilde/global-section counits form a morphism of actual short
exact sequences. Quasicoherence of the two end coefficients makes their
counits invertible, and the native short five lemma makes the original
middle counit invertible. Thus quasicoherence of the middle is a conclusion.
Finite actual global sections also extend, over every commutative ring.
-/

@[expose] public section

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u

namespace AlgebraicGeometry.Scheme.Modules.QuasiCoherent

variable {R : CommRingCat.{u}} {S : ShortComplex (Spec R).Modules}

/-- The original affine tilde counit of the middle coefficient is
invertible in an extension of two quasicoherent module sheaves. -/
theorem isIso_fromTildeΓ_middle_of_shortExact (hS : S.ShortExact)
    [S.X₁.IsQuasicoherent] [S.X₃.IsQuasicoherent] : IsIso S.X₂.fromTildeΓ := by
  let T := (S.map moduleSpecΓFunctor).map (tilde.functor R)
  have hT : T.ShortExact :=
    (AffineCech.shortExact_globalSections_of_quasicoherent_kernel hS).map_of_exact
      (tilde.functor R)
  let τ : T ⟶ S :=
    { τ₁ := S.X₁.fromTildeΓ
      τ₂ := S.X₂.fromTildeΓ
      τ₃ := S.X₃.fromTildeΓ
      comm₁₂ := (fromTildeΓNatTrans.naturality S.f).symm
      comm₂₃ := (fromTildeΓNatTrans.naturality S.g).symm }
  change IsIso τ.τ₂
  exact ShortComplex.isIso₂_of_shortExact_of_isIso₁₃ τ hT hS

/-- Actual quasicoherent affine module sheaves are closed under extensions
inside all module sheaves. No quasicoherence of the middle is assumed. -/
theorem quasicoherent_middle_of_shortExact (hS : S.ShortExact)
    [S.X₁.IsQuasicoherent] [S.X₃.IsQuasicoherent] : S.X₂.IsQuasicoherent :=
  (isQuasicoherent_iff_isIso_fromTildeΓ S.X₂).mpr
    (isIso_fromTildeΓ_middle_of_shortExact hS)

/-- Finite-type quasicoherent affine sheaves are extension-closed over every
commutative ring. No Noetherian hypothesis is required for extensions. -/
theorem affineFiniteSheaf_middle_of_shortExact (hS : S.ShortExact)
    (h₁ : affineFiniteSheaf R S.X₁) (h₃ : affineFiniteSheaf R S.X₃) :
    affineFiniteSheaf R S.X₂ := by
  let := h₁.1
  let := h₃.1
  let : Module.Finite R (S.map moduleSpecΓFunctor).X₁ := h₁.2
  let : Module.Finite R (S.map moduleSpecΓFunctor).X₃ := h₃.2
  refine ⟨quasicoherent_middle_of_shortExact hS, ?_⟩
  have hΓ := AffineCech.shortExact_globalSections_of_quasicoherent_kernel hS
  exact Module.Finite.of_exact
    ((ShortComplex.ShortExact.moduleCat_exact_iff_function_exact _).mp hΓ.exact)
    hΓ.moduleCat_surjective_g

instance affineFiniteSheaf_isClosedUnderExtensions :
    (affineFiniteSheaf R).IsClosedUnderExtensions where
  prop_X₂_of_shortExact hS h₁ h₃ := affineFiniteSheaf_middle_of_shortExact hS h₁ h₃

end AlgebraicGeometry.Scheme.Modules.QuasiCoherent
