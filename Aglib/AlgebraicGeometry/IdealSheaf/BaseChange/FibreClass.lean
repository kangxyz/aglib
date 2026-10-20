/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.IdealSheaf.BaseChange.Fibre
public import Aglib.AlgebraicGeometry.IdealSheaf.BaseChange.Family

/-!
# The Picard class of the actual fibre ideal

The native fibre-ideal isomorphism compares the actual pulled module and the
actual fibre ideal. Passing that isomorphism to Picard classes gives the
incoming class formula on every test scheme, with the same explicit canonical
Cartier base-change input. No representability or Noetherian premise is used.

Source: `R5Lab.Aglib.AlgebraicGeometry.Divisors.Relative.Fibre`, declaration
`R5Lab.AlgebraicGeometry.Curves.RelativeDivisors.fibreIdealLineBundle_class`,
R5 revision `f8a3314ddecffcada2ec721d26d56a937bed9690`, source SHA-256
`a651054528852e771ad73a69fd93297e23c0cfbd09e9de49a4f715689ec7a340`.
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false

open CategoryTheory Limits AlgebraicGeometry
open Scheme.Modules.Invertible
namespace AlgebraicGeometry.Scheme.Hom
universe u
variable {S T X D : Scheme.{u}} (p : X ⟶ S) (i : D ⟶ X) (t : T ⟶ S)
variable (hbase : RelativeCartierIdealBaseChange.{u}) [IsClosedImmersion i] [Flat (i ≫ p)]
variable (hI : IsLocallyRankOne X (idealModule i))

/-- The actual fibre ideal has the pullback class on every test scheme. -/
theorem fibreIdealLineBundle_class :
    classOf (pullback p t) (fibreIdealLineBundle p i t hbase hI) =
      pullbackClass (pullback.fst p t) (classOf X ⟨idealModule i, hI⟩) := by
  apply Quotient.sound
  let e := (fibreIdealIso p i t hbase hI).symm
  exact ⟨⟨e.hom, e.inv, e.hom_inv_id, e.inv_hom_id⟩⟩

end AlgebraicGeometry.Scheme.Hom
