/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Compactification.Basic
public import Mathlib.AlgebraicGeometry.Pullbacks

/-!
Actual base change and source-isomorphism transport of compactifications.
Every resulting structural map and factorization triangle is specified.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory Limits
universe u

namespace AlgebraicGeometry.Scheme.Hom.Compactification

variable {X S T : Scheme.{u}} {f : X ⟶ S}

/-- Base change uses the literal pullback of the proper compactification and
its canonical map from the pullback of the original source. -/
def baseChange (C : Compactification f) (b : T ⟶ S) :
    Compactification (pullback.fst b f) where
  Xbar := pullback b C.p
  j := pullback.map b f b C.p (𝟙 T) C.j (𝟙 S) (by simp) (by simp)
  p := pullback.fst b C.p
  isOpenImmersion_j := inferInstance
  isProper_p := inferInstance
  fac := (pullback.lift_fst _ _ _).trans (Category.comp_id _)

/-- Transport a compactification along an actual source isomorphism, retaining
the specified original structural morphism exactly. -/
def ofSourceIso (C : Compactification f) {X' : Scheme.{u}} (f' : X' ⟶ S)
    (e : X' ≅ X) (h : e.hom ≫ f = f') : Compactification f' where
  Xbar := C.Xbar
  j := e.hom ≫ C.j
  p := C.p
  isOpenImmersion_j := inferInstance
  isProper_p := inferInstance
  fac := by rw [Category.assoc, C.fac, h]

/-- The new open embedding retains the original projection to the new base. -/
@[reassoc (attr := simp)]
theorem baseChange_j_fst {X S T : Scheme.{u}} {f : X ⟶ S}
    (C : Compactification f) (b : T ⟶ S) :
    (C.baseChange b).j ≫ pullback.fst b C.p = pullback.fst b f :=
  (C.baseChange b).fac

/-- The other projection of the new open embedding is the original embedding
after the actual source projection. -/
@[reassoc (attr := simp)]
theorem baseChange_j_snd {X S T : Scheme.{u}} {f : X ⟶ S}
    (C : Compactification f) (b : T ⟶ S) :
    (C.baseChange b).j ≫ pullback.snd b C.p = pullback.snd b f ≫ C.j := by
  simp [baseChange, pullback.map]

end AlgebraicGeometry.Scheme.Hom.Compactification
