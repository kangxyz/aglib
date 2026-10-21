/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Modules.InternalHom.Gluing
public import Aglib.AlgebraicGeometry.Modules.Locality.Exactness

/-! # Gluing original module-sheaf isomorphisms on open covers -/

@[expose] public noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

open CategoryTheory

namespace AlgebraicGeometry.Scheme.Modules.InternalHom

universe u v
variable {X : Scheme.{u}} {ι : Type v}
  (Y : ι → Scheme.{u}) (a : ∀ i, Y i ⟶ X) [∀ i, IsOpenImmersion (a i)]
  (hcover : ∀ x : X, ∃ (i : ι) (y : Y i), a i y = x)
  (M N : X.Modules) (e : ∀ i, M.restrict (a i) ≅ N.restrict (a i))
  (he : RestrictionHomCompatible a M N (fun i => (e i).hom))

/-- Compatible original local isomorphisms glue to a genuine global isomorphism. -/
def glueRestrictionIso : M ≅ N := by
  let q := glueRestrictionHom Y a hcover M N (fun i => (e i).hom) he
  let : IsIso q := isIso_of_restrict_openCover Y a hcover q (by
    intro i
    change IsIso ((restrictFunctor (a i)).map
      (glueRestrictionHom Y a hcover M N (fun i => (e i).hom) he))
    rw [glueRestrictionHom_restrict]
    infer_instance)
  exact asIso q

/-- The global comparison retains every original local comparison exactly. -/
theorem glueRestrictionIso_hom_restrict (i : ι) :
    (restrictFunctor (a i)).map (glueRestrictionIso Y a hcover M N e he).hom = (e i).hom :=
  glueRestrictionHom_restrict Y a hcover M N (fun i => (e i).hom) he i

end AlgebraicGeometry.Scheme.Modules.InternalHom
