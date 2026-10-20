/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Modules.Invertible.Dual

/-!
Native migration from `R5Lab.Aglib.AlgebraicGeometry.Picard.Torsion` at R5 revision
`f8a3314ddecffcada2ec721d26d56a937bed9690`, SHA-256
`9fece9342fe451dec6ab3ae639dffd99dd6f684b926ac2caff68db30c46b2e81`.
Original objects, maps, universes and explicit hypotheses are retained.
Native providers replace duplicate implementations.
-/

@[expose] public section

noncomputable section
open AlgebraicGeometry
open _root_.AlgebraicGeometry.Scheme.Modules.Invertible (PicardGroup)
open AlgebraicGeometry.Scheme.Hom AlgebraicGeometry.Scheme.Modules
open AlgebraicGeometry.Scheme.Modules.Hom
open AlgebraicGeometry.Scheme.Modules.Invertible
namespace AlgebraicGeometry.Scheme.Modules.Invertible.Torsion
universe u
variable (X : Scheme.{u}) (n : ℕ)
/-- Actual nth torsion in the ordinary invertible-sheaf Picard group. -/
def picardTorsion : AddSubgroup (PicardGroup X) := (nsmulAddMonoidHom (α := PicardGroup X) n).ker

end AlgebraicGeometry.Scheme.Modules.Invertible.Torsion
