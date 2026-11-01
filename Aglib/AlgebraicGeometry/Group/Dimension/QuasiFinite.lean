/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Dimension.QuasiFiniteSurjective
public import Aglib.AlgebraicGeometry.Group.Dimension
public import Mathlib.RingTheory.RegularLocalRing.Defs

/-!
# Local dimension and cotangent bounds for group morphisms

The actual unit of a field monoid is rational, so its residue-field cotangent dimension equals
the dimension over the original field. Its local Krull dimension is at most this number.
Locally quasi-finite unit-preserving morphisms give the opposite local-dimension comparison.
For a connected smooth source, a cotangent upper bound on the target therefore gives equality
of both unit dimensions and regularity of the target's actual unit stalk.

The target is not assumed smooth or proper. The displayed cotangent inequality remains an
explicit structural-criterion hypothesis for subsequent geometric suppliers.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory Order
open scoped CategoryTheory.MonObj
open AlgebraicGeometry.Scheme.OverField

universe u

namespace AlgebraicGeometry.Scheme.Group

attribute [local instance] Over.cartesianMonoidalCategory

variable {k : Type u} [Field k]

/-- The original unit-preserving morphism carries the actual unit point to the actual unit. -/
theorem hom_unitPoint {G H : FScheme k} [MonObj G] [MonObj H]
    (f : G ⟶ H) [IsMonHom f] : f.left (unitPoint G) = unitPoint H := by
  have h := congrArg (fun a : 𝟙_ (FScheme k) ⟶ H => a.left (IsLocalRing.closedPoint k))
    (IsMonHom.one_hom f)
  change f.left ((MonObj.one (X := G)).left (IsLocalRing.closedPoint k)) =
    (MonObj.one (X := H)).left (IsLocalRing.closedPoint k)
  change f.left ((MonObj.one (X := G)).left (IsLocalRing.closedPoint k)) =
    (MonObj.one (X := H)).left (IsLocalRing.closedPoint k) at h
  exact h

-- The quotient-module parent structures are the original rational-point scalar structures.
set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- The rational unit identifies its actual residue-field cotangent rank with its rank over
the original base field, using the native section-induced residue equivalence. -/
theorem finrank_residueCotangent_eq_finrank_identityCotangent (G : FScheme k) [MonObj G] :
    Module.finrank (IsLocalRing.ResidueField (G.left.presheaf.stalk (unitPoint G)))
        (IsLocalRing.CotangentSpace (G.left.presheaf.stalk (unitPoint G))) =
      Module.finrank k (Cotangent.Space η[G]) := by
  let q := Cotangent.pointData η[G]
  let R := q.localRing
  let K := IsLocalRing.ResidueField R
  let := q.constants.toAlgebra
  let : Algebra k K := Ideal.Quotient.algebra k (I := IsLocalRing.maximalIdeal R)
  let : IsScalarTower k R K := Ideal.Quotient.isScalarTower k R (IsLocalRing.maximalIdeal R)
  let : IsScalarTower k K (IsLocalRing.CotangentSpace R) :=
    IsScalarTower.of_algebraMap_smul fun a v =>
      (IsScalarTower.algebraMap_smul K (algebraMap k R a) v).trans
        (IsScalarTower.algebraMap_smul R a v)
  let e : K ≃ₐ[k] k :=
    { q.residueEquiv with commutes' := fun a => q.residueEquiv_constants a }
  have hK : Module.finrank k K = 1 := by
    rw [e.toLinearEquiv.finrank_eq]
    exact Module.finrank_self k
  change Module.finrank K (IsLocalRing.CotangentSpace R) =
    Module.finrank k (IsLocalRing.CotangentSpace R)
  rw [← Module.finrank_mul_finrank k K _, hK, one_mul]

/-- The actual unit-stalk Krull dimension is at most the original identity cotangent rank. -/
theorem ringKrullDim_unit_le_finrank_identityCotangent (G : FScheme k) [MonObj G]
    [LocallyOfFiniteType G.hom] :
    ringKrullDim (G.left.presheaf.stalk (unitPoint G)) ≤
      Module.finrank k (Cotangent.Space η[G]) := by
  have : IsLocallyNoetherian G.left := LocallyOfFiniteType.isLocallyNoetherian G.hom
  have h := ringKrullDim_le_spanFinrank_maximalIdeal
    (G.left.presheaf.stalk (unitPoint G))
  rw [IsLocalRing.spanFinrank_maximalIdeal_eq_finrank_cotangentSpace,
    finrank_residueCotangent_eq_finrank_identityCotangent G] at h
  exact h

/-- A locally quasi-finite unit-preserving morphism cannot lower the actual unit-stalk
dimension. This is the coheight comparison for its original specialization-order map. -/
theorem ringKrullDim_unit_le_of_locallyQuasiFinite {G H : FScheme k}
    [MonObj G] [MonObj H] (f : G ⟶ H) [IsMonHom f] [LocallyQuasiFinite f.left] :
    ringKrullDim (G.left.presheaf.stalk (unitPoint G)) ≤
      ringKrullDim (H.left.presheaf.stalk (unitPoint H)) := by
  rw [← hom_unitPoint f, ringKrullDim_stalk_eq_coheight, ringKrullDim_stalk_eq_coheight]
  exact_mod_cast Order.coheight_le_coheight_apply_of_strictMono f.left
    f.left.strictMono_of_locallyQuasiFinite (unitPoint G)

/-- The original closed unit stalk of a connected smooth group has dimension equal to its
original identity cotangent rank. -/
theorem ringKrullDim_unit_eq_finrank_identityCotangent_of_preconnected
    (G : FScheme k) [GrpObj G] [Smooth G.hom] [PreconnectedSpace G.left] :
    ringKrullDim (G.left.presheaf.stalk (unitPoint G)) =
      Module.finrank k (Cotangent.Space η[G]) := by
  let hd := smoothOfRelativeDimension_finrank_identityCotangent_of_preconnected G
  exact Scheme.smoothClosedPointDimension k G.left G.hom _ hd (unitPoint G)
    (Cotangent.pointData η[G]).point_isClosed

/-- A cotangent upper bound on the target of an actual locally quasi-finite group morphism
from a connected smooth source forces equality of the unit dimensions and target regularity. -/
theorem unit_dimension_cotangent_and_regular_of_locallyQuasiFinite
    (G H : FScheme k) [GrpObj G] [MonObj H] [Smooth G.hom]
    [PreconnectedSpace G.left] [LocallyOfFiniteType H.hom]
    (f : G ⟶ H) [IsMonHom f] [LocallyQuasiFinite f.left]
    (hcot : Module.finrank k (Cotangent.Space η[H]) ≤
      Module.finrank k (Cotangent.Space η[G])) :
    ringKrullDim (H.left.presheaf.stalk (unitPoint H)) =
        Module.finrank k (Cotangent.Space η[G]) ∧
      Module.finrank k (Cotangent.Space η[H]) = Module.finrank k (Cotangent.Space η[G]) ∧
      IsRegularLocalRing (H.left.presheaf.stalk (unitPoint H)) := by
  have hG := ringKrullDim_unit_eq_finrank_identityCotangent_of_preconnected G
  have hlower := ringKrullDim_unit_le_of_locallyQuasiFinite f
  rw [hG] at hlower
  have hupper := ringKrullDim_unit_le_finrank_identityCotangent H
  have hcot' : (Module.finrank k (Cotangent.Space η[H]) : WithBot ℕ∞) ≤
      Module.finrank k (Cotangent.Space η[G]) := by exact_mod_cast hcot
  have hdim := le_antisymm (hupper.trans hcot') hlower
  have hrev : Module.finrank k (Cotangent.Space η[G]) ≤
      Module.finrank k (Cotangent.Space η[H]) := by exact_mod_cast hlower.trans hupper
  have : IsLocallyNoetherian H.left := LocallyOfFiniteType.isLocallyNoetherian H.hom
  have hreg : IsRegularLocalRing (H.left.presheaf.stalk (unitPoint H)) := by
    apply IsRegularLocalRing.of_spanFinrank_maximalIdeal_le
    rw [IsLocalRing.spanFinrank_maximalIdeal_eq_finrank_cotangentSpace,
      finrank_residueCotangent_eq_finrank_identityCotangent H]
    exact hcot'.trans hlower
  exact ⟨hdim, Nat.le_antisymm hcot hrev, hreg⟩

end AlgebraicGeometry.Scheme.Group
