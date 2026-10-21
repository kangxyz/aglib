/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Modules.IdealPowers.Basic
public import Aglib.AlgebraicGeometry.Modules.QuasiCoherent.Coproduct
public import Aglib.AlgebraicGeometry.Modules.QuasiCoherent.Limits

/-! # Quasicoherence of actual ideal multiples and quotients -/

@[expose] public section

noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Scheme.Modules

universe u

variable (X : Scheme.{u}) {A : Type u} [CommRing A]
variable (α : A →+* Γ(X, ⊤)) (F : X.Modules) [F.IsQuasicoherent]

/-- Ideal multiples of quasicoherent coefficients are quasicoherent on arbitrary schemes. -/
theorem idealMultiple_isQuasicoherent (J : Ideal A) :
    (idealMultiple X α F J).IsQuasicoherent := by
  let := QuasiCoherent.quasicoherent_coproduct (fun _ : J => F)
  let e := idealEvaluation X α F J
  let := QuasiCoherent.quasicoherent_cokernel e
  have h := QuasiCoherent.quasicoherent_kernel (cokernel.π e)
  exact (SheafOfModules.isQuasicoherent X.ringCatSheaf).prop_of_iso
    (Abelian.imageIsoImage e) h

/-- Quotients by actual ideal multiples remain quasicoherent. -/
theorem idealQuotient_isQuasicoherent (J : Ideal A) :
    (idealQuotient X α F J).IsQuasicoherent := by
  let := idealMultiple_isQuasicoherent X α F J
  exact QuasiCoherent.quasicoherent_cokernel (idealMultipleι X α F J)

end AlgebraicGeometry.Scheme.Modules
