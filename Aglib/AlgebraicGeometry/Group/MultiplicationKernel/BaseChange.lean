/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Group.Kernel.BaseChange
public import Aglib.AlgebraicGeometry.Group.MultiplicationKernel
public import Mathlib.CategoryTheory.Monoidal.CommMon_

/-! # Base change of the original multiplication kernel

The native monoidal pullback preserves the multiplication arrow. The
kernel comparison uses this equality and the original kernel comparison.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open CategoryTheory.MonObj Scheme.OverField
open scoped CategoryTheory.MonObj

universe u

namespace AlgebraicGeometry.Scheme.Group.MultiplicationKernel

attribute [local instance] Over.cartesianMonoidalCategory

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable {F K : Type u} [Field F] [Field K] (b : Spec (.of K) ⟶ Spec (.of F))
  (E : Grp (FScheme F)) [IsCommMonObj E.X]

/-- The actual pulled-back group retains commutativity by the native braided functor. -/
theorem baseChange_isCommMonObj : IsCommMonObj ((Over.pullback b).mapGrp.obj E).X := by
  let P := Over.pullback b
  let : GrpObj (P.obj E.X) := (P.mapGrp.obj E).grp
  exact inferInstanceAs (IsCommMonObj (P.obj E.X))

attribute [local instance] baseChange_isCommMonObj

/-- Pullback preserves the actual multiplication arrow as a group morphism. -/
theorem map_multiplicationHom (n : ℕ) :
    (Over.pullback b).mapGrp.map (multiplicationHom E n) =
      multiplicationHom ((Over.pullback b).mapGrp.obj E) n := by
  let P := Over.pullback b
  let : GrpObj (P.obj E.X) := (P.mapGrp.obj E).grp
  apply Grp.hom_ext
  change P.map (multiplicationHom E n).hom.hom =
    (multiplicationHom (P.mapGrp.obj E) n).hom.hom
  simp only [multiplicationHom_hom, multiplication]
  calc
    _ = (P.map (𝟙 E.X)) ^ n := (P.homMonoidHom (X := E.X) (M := E.X)).map_pow _ _
    _ = _ := by rw [P.map_id]; rfl

private theorem eqToIso_hom_inclusion {A B : Grp (FScheme K)} {f g : A ⟶ B} (h : f = g) :
    (eqToIso (congrArg (fun q : A ⟶ B => Kernel.group q) h)).hom ≫
      Kernel.inclusion g = Kernel.inclusion f := by
  subst g
  simp

/-- The native comparison between the base-changed original multiplication
kernel and the actual multiplication kernel of the base-changed group. -/
@[no_expose]
def baseChangeIso (n : ℕ) :
    (Over.pullback b).mapGrp.obj (kernelGroup E n) ≅
      kernelGroup ((Over.pullback b).mapGrp.obj E) n :=
  Kernel.baseChangeIso b (multiplicationHom E n) ≪≫
    eqToIso (congrArg (fun q : (Over.pullback b).mapGrp.obj E ⟶ (Over.pullback b).mapGrp.obj E =>
      Kernel.group q) (map_multiplicationHom b E n))

/-- The forward map is the original kernel comparison followed by transport
along the actual multiplication-map equality. -/
theorem baseChangeIso_hom_factor (n : ℕ) :
    (baseChangeIso b E n).hom =
      (Kernel.baseChangeIso b (multiplicationHom E n)).hom ≫
        (eqToIso (congrArg
          (fun q : (Over.pullback b).mapGrp.obj E ⟶ (Over.pullback b).mapGrp.obj E =>
            Kernel.group q) (map_multiplicationHom b E n))).hom := by
  unfold baseChangeIso
  exact Iso.trans_hom _ _

/-- The native multiplication-kernel comparison preserves the original inclusion. -/
@[reassoc (attr := simp)]
theorem baseChangeIso_hom_inclusion (n : ℕ) :
    (baseChangeIso b E n).hom ≫
        Kernel.inclusion (multiplicationHom ((Over.pullback b).mapGrp.obj E) n) =
      (Over.pullback b).mapGrp.map (Kernel.inclusion (multiplicationHom E n)) := by
  unfold baseChangeIso
  rw [Iso.trans_hom, Category.assoc, eqToIso_hom_inclusion (map_multiplicationHom b E n),
    Kernel.baseChangeIso_hom_inclusion]

end AlgebraicGeometry.Scheme.Group.MultiplicationKernel
