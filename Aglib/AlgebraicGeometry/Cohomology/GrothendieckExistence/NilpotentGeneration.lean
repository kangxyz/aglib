/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Modules.Locality.Sections
public import Aglib.AlgebraicGeometry.Modules.Rees.AffineOpenImage
public import Aglib.AlgebraicGeometry.Modules.ClosedImmersion.Killed
public import Aglib.RingTheory.AdicCompletion.CompatibleSystemGenerators

/-! # Finite-stage generation without flatness

Original affine section maps and nilpotent ideal actions detect epimorphisms.
The reduction map need only have kernel contained in the ideal multiple;
it need not exhibit a cartesian reduction. This is the common algebraic
criterion for formal coefficient towers and ordinary relation towers.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.Scheme.Modules

universe u

variable {X : Scheme.{u}} {P M N : X.Modules}

/-- Surjectivity on all original affine sections detects an epimorphism,
without any quasicoherence condition on its endpoints. -/
theorem epi_of_affineSections_surjective (p : P ⟶ M)
    (hp : ∀ U : X.affineOpens, Function.Surjective (p.app U.val)) : Epi p where
  left_cancellation g h e := by
    apply moduleHom_ext_affine
    intro U
    ext x
    obtain ⟨y, rfl⟩ := hp U x
    exact congrArg (fun k => k.app U.val y) e

/-- A nilpotent ideal acting on the target allows generation to be tested
through any map whose affine section kernel lies in the ideal multiple. -/
theorem epi_of_nilpotent_reduction (K : X.IdealSheafData)
    (p : P ⟶ M) (t : M ⟶ N)
    (hpt : ∀ U : X.affineOpens, Function.Surjective ((p ≫ t).app U.val))
    (hker : ∀ U : X.affineOpens,
      LinearMap.ker (t.val.app (op U.val)).hom ≤
        K.ideal U • (⊤ : Submodule Γ(X, U.val) Γ(M, U.val)))
    (n : ℕ) (hn : killedByIdealSheaf (K ^ n) M) : Epi p := by
  apply epi_of_affineSections_surjective p
  intro U
  have hnil : (K.ideal U) ^ n • (⊤ : Submodule Γ(X, U.val) Γ(M, U.val)) = ⊥ := by
    apply le_bot_iff.mp
    apply Submodule.smul_le.mpr
    intro a ha x _
    exact hn U a ha x
  exact LinearMap.surjective_of_surjective_comp_of_ker_le_smul
    (K.ideal U) (p.val.app (op U.val)).hom (t.val.app (op U.val)).hom (hpt U) (hker U) n hnil

/-- For quasicoherent kernels, an epimorphic composite supplies the affine
surjectivity premise of nilpotent generation automatically. -/
theorem epi_of_epi_comp_of_nilpotent_reduction (K : X.IdealSheafData)
    (p : P ⟶ M) (t : M ⟶ N) [Epi (p ≫ t)] [(kernel (p ≫ t)).IsQuasicoherent]
    (hker : ∀ U : X.affineOpens,
      LinearMap.ker (t.val.app (op U.val)).hom ≤
        K.ideal U • (⊤ : Submodule Γ(X, U.val) Γ(M, U.val)))
    (n : ℕ) (hn : killedByIdealSheaf (K ^ n) M) : Epi p :=
  epi_of_nilpotent_reduction K p t
    (fun U => affineOpenSections_epi_surjective U (p ≫ t)) hker n hn

end AlgebraicGeometry.Scheme.Modules
