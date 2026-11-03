/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Modules.InternalHom.AffineSections

/-! # Inverse -/

@[expose] public section
noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory Opposite AlgebraicGeometry
universe u

namespace AlgebraicGeometry.Scheme.Modules.InternalHom

/-- The inverse affine Hom comparison has exactly the supplied original section map. -/
theorem affineGlobalHomEquiv_symm_apply (R : CommRingCat.{u}) (M N : (Spec R).Modules)
    [M.IsQuasicoherent]
    (q : moduleSpecΓFunctor.obj M →ₗ[R] moduleSpecΓFunctor.obj N) :
    (moduleSpecΓFunctor.map ((affineGlobalHomEquiv R M N).symm q)).hom = q := by
  exact (affineGlobalHomEquiv_apply R M N _).symm.trans
    ((affineGlobalHomEquiv R M N).apply_symm_apply q)

end AlgebraicGeometry.Scheme.Modules.InternalHom
