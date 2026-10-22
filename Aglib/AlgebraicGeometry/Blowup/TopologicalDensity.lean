/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Blowup.SchematicDensity
public import Aglib.AlgebraicGeometry.Blowup.Properness

/-!
# Topological density under native blowups

The exceptional complement is schematically dense, and maps by an open
immersion to the base. Thus the inverse image of a topologically dense open
is dense on a locally Noetherian blowup, without reducedness assumptions.
-/

@[expose] public noncomputable section

open CategoryTheory Limits

universe u

namespace AlgebraicGeometry.Scheme.Blowup

/-- Every native blowup over a locally Noetherian base preserves topological
density of opens. Schematic density of the given open is not required. -/
theorem BlowupDatum.preimage_open_dense {X : Scheme.{u}} [IsLocallyNoetherian X]
    {I : X.IdealSheafData} (B : BlowupDatum I) (U : X.Opens)
    (hU : Dense (U : Set X)) : Dense ((B.map ⁻¹ᵁ U) : Set B.Y) := by
  let : IsProper B.map := B.isProper_of_isLocallyNoetherian
  let : IsLocallyNoetherian B.Y := LocallyOfFiniteType.isLocallyNoetherian B.map
  let V : X.Opens := I.support.compl
  let E := B.exceptionalComplement
  let e : E.toScheme ⟶ X := E.ι ≫ B.map
  let : IsIso (B.map ∣_ V) := B.restrict_isIso_of_disjoint V
    (Set.disjoint_left.mpr fun _ hx hy => hx hy)
  have he : e = (B.map ∣_ V) ≫ V.ι := (morphismRestrict_ι B.map V).symm
  have hOpen : IsOpenImmersion ((B.map ∣_ V) ≫ V.ι) := inferInstance
  let : IsOpenImmersion e := he.symm ▸ hOpen
  let : IsSchemeTheoreticallyDominant E.ι :=
    B.exceptionalComplement_isSchemeTheoreticallyDominant
  have hd : Dense (e ⁻¹' (U : Set X)) := hU.preimage e.isOpenEmbedding.isOpenMap
  exact E.ι.denseRange.dense_of_mapsTo E.ι.continuous hd (fun _ hx => hx)

end AlgebraicGeometry.Scheme.Blowup
