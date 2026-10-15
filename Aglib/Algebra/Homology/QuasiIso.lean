/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Mathlib.Algebra.Homology.HomologicalComplexAbelian
public import Mathlib.Algebra.Homology.QuasiIso

/-! # Maps between acyclic cochain complexes

Source:
`Quillen/AlgebraicGeometry/PerfectComplexes/FlasqueShift.lean`
at LOCAL Quillen
`189a8e779f0c68b2dfc6f8195daebb3e684a5905`.
Source SHA-256:
`78944f4baecd627e51378eba3c20d6c215bd1e010a46566c0bfc2cf673a8fd62`.
Selected declarations: quasiIso_of_two_acyclic.
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

universe v u
open CategoryTheory HomologicalComplex
namespace CochainComplex
variable {A : Type u} [Category.{v} A] [Abelian A]

lemma quasiIso_of_two_acyclic {K L : CochainComplex A ℤ} (f : K ⟶ L)
    (hK : K.Acyclic) (hL : L.Acyclic) : QuasiIso f :=
  (quasiIso_iff f).mpr (fun n => (quasiIsoAt_iff_exactAt f n (hK n)).mpr (hL n))

end CochainComplex
