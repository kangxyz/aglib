/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Cohomology.BaseChange.Modules.Sections.AffineGlobal

/-! # The original section tensor comparison on affine schemes

The actual presheaf comparison is identified with the native scalar base-change
mate and the original affine pullback-section isomorphism. A pushout of the
displayed structural rings therefore gives invertibility, without flatness.
-/

@[expose] public section

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
open scoped TensorProduct ChangeOfRings

namespace AlgebraicGeometry.Scheme.Cohomology

variable {X Y : Scheme.{u}} [IsAffine X] [IsAffine Y]
  {A B : Type u} [CommRing A] [CommRing B]
  (p : Y ⟶ X) (α : A →+* Γ(X, ⊤)) (β : B →+* Γ(Y, ⊤)) (σ : A →+* B)
  (hσ : p.appTop.hom.comp α = β.comp σ)

set_option maxRecDepth 2000 in
/-- The original affine section tensor comparison is the canonical scalar mate. -/
theorem moduleSectionsTensorComparison_top_eq_scalar (M : X.Modules) [M.IsQuasicoherent] :
    (moduleSectionsTensorComparison p α β σ hσ M).app (op ⊤) =
      (ModuleCat.extendScalars σ).map (moduleAffineTopSectionsIso X α M).hom ≫
        ModuleCat.scalarBaseChangeMap (CommRingCat.ofHom α) (CommRingCat.ofHom σ)
          p.appTop (CommRingCat.ofHom β) (by ext a; exact DFunLike.congr_fun hσ a)
          ((Scheme.Modules.affineΓFunctor X).obj M) ≫
        (ModuleCat.restrictScalars β).map (Scheme.Modules.affinePullbackSectionsIso p M).hom ≫
        (moduleAffineTopSectionsIso Y β ((Scheme.Modules.pullback p).obj M)).inv := by
  apply ModuleCat.ExtendScalars.hom_ext
  intro m
  erw [moduleSectionsTensorComparison_one_tmul p α β σ hσ M ⊤ m]
  change (((Scheme.Modules.pullbackPushforwardAdjunction p).unit.app M).app ⊤) m =
    (moduleAffineTopSectionsIso Y β ((Scheme.Modules.pullback p).obj M)).inv
      ((Scheme.Modules.affinePullbackSectionsIso p M).hom
        (ModuleCat.scalarBaseChangeMap (CommRingCat.ofHom α) (CommRingCat.ofHom σ)
          p.appTop (CommRingCat.ofHom β) (by ext a; exact DFunLike.congr_fun hσ a)
          ((Scheme.Modules.affineΓFunctor X).obj M)
          ((1 : B) ⊗ₜ[A,σ] ((moduleAffineTopSectionsIso X α M).hom m))))
  rw [moduleAffineTopSectionsIso_hom_apply, ModuleCat.scalarBaseChangeMap_one_tmul,
    Scheme.Modules.affinePullbackSectionsIso_one_tmul, moduleAffineTopSectionsIso_inv_apply]

/-- A pushout of the actual structural rings makes the original affine section tensor map
invertible for every quasicoherent coefficient. -/
theorem moduleSectionsTensorComparison_top_isIso
    (hpush : IsPushout (CommRingCat.ofHom α) (CommRingCat.ofHom σ)
      p.appTop (CommRingCat.ofHom β)) (M : X.Modules) [M.IsQuasicoherent] :
    IsIso ((moduleSectionsTensorComparison p α β σ hσ M).app (op ⊤)) := by
  rw [moduleSectionsTensorComparison_top_eq_scalar p α β σ hσ M]
  let := ModuleCat.scalarBaseChangeMap_isIso_of_isPushout
    (CommRingCat.ofHom α) (CommRingCat.ofHom σ) p.appTop (CommRingCat.ofHom β)
    hpush ((Scheme.Modules.affineΓFunctor X).obj M)
  infer_instance

end AlgebraicGeometry.Scheme.Cohomology
