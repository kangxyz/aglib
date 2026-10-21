/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Modules.Coherent.Affine.SectionQuotient

/-! # Naturality of canonical affine section quotients -/

@[expose] public noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry.Scheme.Modules

namespace AlgebraicGeometry.Scheme.Modules.Coherent

universe u
variable {R : CommRingCat.{u}} {M M' : (Spec R).Modules}
  [M.IsQuasicoherent] [M'.IsQuasicoherent] {N N' : ModuleCat.{u} R}

/-- A square of original section presentations induces the same square of
canonical sheaf quotients. This retains coefficient morphisms in realization. -/
@[reassoc]
theorem affineQuotientFromSections_naturality
    (q : moduleSpecΓFunctor.obj M ⟶ N) (q' : moduleSpecΓFunctor.obj M' ⟶ N')
    (a : M ⟶ M') (b : N ⟶ N') (h : moduleSpecΓFunctor.map a ≫ q' = q ≫ b) :
    a ≫ affineQuotientFromSections M' N' q' =
      affineQuotientFromSections M N q ≫ tilde.map b := by
  apply (cancel_epi M.fromTildeΓ).mp
  have hn : tilde.map (moduleSpecΓFunctor.map a) ≫ M'.fromTildeΓ =
      M.fromTildeΓ ≫ a := fromTildeΓNatTrans.naturality a
  dsimp only [affineQuotientFromSections]
  rw [← Category.assoc, ← hn]
  simp only [Category.assoc, asIso_inv, IsIso.hom_inv_id_assoc]
  change (tilde.functor R).map (moduleSpecΓFunctor.map a) ≫
      (tilde.functor R).map q' = (tilde.functor R).map q ≫ (tilde.functor R).map b
  rw [← Functor.map_comp, ← Functor.map_comp, h]

end AlgebraicGeometry.Scheme.Modules.Coherent
