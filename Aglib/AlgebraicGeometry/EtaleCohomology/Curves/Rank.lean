/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Curves.Jacobian.Kummer
public import Aglib.Algebra.Homology.DerivedCategory.Ext.ZMod

/-!
# Intrinsic proper-curve H1 cardinalities and noncanonical coordinates

For a smooth proper geometrically connected curve over an algebraically
closed field and every positive invertible level n, original roots and
constant H1 have cardinality n^(2g). They admit linear coordinates and a
basis indexed by Fin (2g) for their original annihilation ZMod actions.

The proof chooses one existing Picard representative internally and uses
the cardinality at every divisor of n in the same rational point group.
The Kummer and constant-root maps are the existing original maps.
Coordinates, including the primitive root in the constant-root map, are
noncanonical. Level one and genus zero are included; no finrank assertion
over ZMod 1 or Galois equivariance is asserted.
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry MonoidalCategory MonObj
open scoped CategoryTheory.MonObj
open AlgebraicGeometry.Scheme.OverField AlgebraicGeometry.Scheme.OverField.Curve
open AlgebraicGeometry.Scheme.RelativePicard AlgebraicGeometry.Scheme.Group
open AlgebraicGeometry.Scheme.Modules.Invertible
open AlgebraicGeometry.Scheme.Modules.Invertible.Torsion (picardTorsion)
open GroupCohomology.Kummer.Coefficients

universe u w

namespace AlgebraicGeometry.Scheme.EtaleCohomology.Curves

attribute [local instance] Over.cartesianMonoidalCategory hasSheafifyLarge

variable {k : Type u} [Field k] [IsAlgClosed k] {X : FScheme k} (hX : Curve.Properties X)

include hX in
/-- Intrinsic Picard torsion coordinates. One original Picard representative
is used for all divisor-level cardinalities in the torsion criterion. -/
theorem nonempty_picardTorsionRankAddEquiv (n : ℕ) (hn : 0 < n)
    (hunit : IsUnit (n : k)) :
    Nonempty (picardTorsion X.left n ≃+ (Fin (2 * coherentGenus k X) → ZMod n)) := by
  obtain ⟨P, R, hP, hsep, -⟩ := exists_representableBy_fppfPicardSheaf_properties hX
  let := picardCommGrpObj X.hom P R
  let T := Additive (𝟙_ (Over (Spec (.of k))) ⟶ identityComponentOver P.obj)
  have hcard (d : ℕ) (hdn : d ∣ n) :
      Nat.card (AddSubgroup.torsionBy T (d : ℤ)) = d ^ (2 * coherentGenus k X) := by
    have hd : IsUnit (d : k) := by
      apply isUnit_iff_ne_zero.mpr
      intro hzero
      apply hunit.ne_zero
      obtain ⟨a, ha⟩ := hdn
      rw [ha, Nat.cast_mul, hzero, zero_mul]
    exact card_rationalTorsion_identityComponentOver_of_isUnit hX P R d hd
  obtain ⟨e⟩ := AddSubgroup.TorsionBy.nonempty_torsionEquiv_of_card_pow T
    (2 * coherentGenus k X) n hn hcard
  exact ⟨(picardTorsionJacobianPointAddEquiv hX P R n hn).trans e⟩

variable [HasExt.{w} (AbelianSheaf.{u, u + 1} X.left)]

/-- Noncanonical coordinates on the original roots H1, through the
original Kummer equivalence and intrinsic Picard torsion coordinates. -/
def rootsOneRankAddEquiv (n : ℕ) (hn : 0 < n) (hunit : IsUnit (n : k)) :
    Sheaf.H.{w} (mu X.left n) 1 ≃+ (Fin (2 * coherentGenus k X) → ZMod n) :=
  (rootsOneAddEquiv hX n hn (by
    simpa only [map_natCast] using hunit.map (Scheme.constants X))).trans
      (Classical.choice (nonempty_picardTorsionRankAddEquiv hX n hn hunit))

include hX in
/-- The actual roots H1 has the expected cardinality at every positive
invertible level, including composite levels and level one. -/
theorem card_rootsOne (n : ℕ) (hn : 0 < n) (hunit : IsUnit (n : k)) :
    Nat.card (Sheaf.H.{w} (mu X.left n) 1) = n ^ (2 * coherentGenus k X) := by
  rw [Nat.card_congr (rootsOneRankAddEquiv hX n hn hunit).toEquiv,
    Nat.card_fun, Nat.card_fin, Nat.card_zmod]

/-- The canonical action from original roots-coefficient annihilation.
This construction uses no coordinates or choice of Picard representative. -/
abbrev rootsOneZModModule (n : ℕ) : Module (ZMod n) (Sheaf.H.{w} (mu X.left n) 1) :=
  AddCommGroup.zmodModule (nsmul_h1_eq_zero_of_killedBy (mu_killedBy X.left n))

/-- The chosen roots coordinates are linear for the original action. -/
def rootsOneRankLinearEquiv (n : ℕ) (hn : 0 < n) (hunit : IsUnit (n : k)) :
    letI := rootsOneZModModule (X := X) n
    Sheaf.H.{w} (mu X.left n) 1 ≃ₗ[ZMod n] (Fin (2 * coherentGenus k X) → ZMod n) := by
  let := rootsOneZModModule (X := X) n
  let e := rootsOneRankAddEquiv hX n hn hunit
  exact { e with map_smul' := (e.toAddMonoidHom.toZModLinearMap n).map_smul }

/-- The linear coordinates have exactly the chosen original additive map. -/
theorem rootsOneRankLinearEquiv_toAddEquiv (n : ℕ) (hn : 0 < n)
    (hunit : IsUnit (n : k)) :
    letI := rootsOneZModModule (X := X) n
    (rootsOneRankLinearEquiv hX n hn hunit).toAddEquiv =
      rootsOneRankAddEquiv hX n hn hunit := rfl

/-- A basis on original roots H1, including n=1 and g=0. -/
def rootsOneBasis (n : ℕ) (hn : 0 < n) (hunit : IsUnit (n : k)) :
    letI := rootsOneZModModule (X := X) n
    Module.Basis (Fin (2 * coherentGenus k X)) (ZMod n) (Sheaf.H.{w} (mu X.left n) 1) := by
  let := rootsOneZModModule (X := X) n
  exact AddSubgroup.TorsionBy.basisOfEquivRank _ n (rootsOneRankAddEquiv hX n hn hunit)

/-- Noncanonical constant H1 coordinates, using the original chosen
constant-root coefficient isomorphism. -/
def constantOneRankAddEquiv (n : ℕ) (hn : 0 < n) (hunit : IsUnit (n : k)) :
    Sheaf.H.{w} (ConstantFinite.coefficient (ULift.{u} (ZMod n)) X.left) 1 ≃+
      (Fin (2 * coherentGenus k X) → ZMod n) :=
  (constantRootsAddEquiv (X := X) n hn hunit 1).trans
    (rootsOneRankAddEquiv hX n hn hunit)

/-- The whole constant-coordinate map factors through the actual
constant-root coefficient map on the original cohomology. -/
theorem constantOneRankAddEquiv_coefficientMap (n : ℕ) (hn : 0 < n)
    (hunit : IsUnit (n : k)) :
    (constantOneRankAddEquiv hX n hn hunit).toAddMonoidHom =
      (rootsOneRankAddEquiv hX n hn hunit).toAddMonoidHom.comp
        (Sheaf.H.map (constantRootIso (X := X) n hn hunit).hom 1) := rfl

include hX in
/-- Original constant H1 has cardinality n^(2g). -/
theorem card_constantOne (n : ℕ) (hn : 0 < n) (hunit : IsUnit (n : k)) :
    Nat.card (Sheaf.H.{w} (ConstantFinite.coefficient (ULift.{u} (ZMod n)) X.left) 1) =
      n ^ (2 * coherentGenus k X) := by
  rw [Nat.card_congr (constantOneRankAddEquiv hX n hn hunit).toEquiv,
    Nat.card_fun, Nat.card_fin, Nat.card_zmod]

omit hX [IsAlgClosed k] [HasExt.{w} (AbelianSheaf.{u, u + 1} X.left)] in
/-- Original constant ZMod coefficients are annihilated by n, before
choosing any root of unity or cohomology coordinates. -/
theorem constantZMod_killedBy (n : ℕ) :
    KilledBy n (ConstantFinite.coefficient (ULift.{u} (ZMod n)) X.left) := by
  apply (constantSheaf (Scheme.smallEtaleTopology X.left)
    AddCommGrpCat.{u + 1}).nsmul_id_eq_zero_obj
  ext a
  exact ZModModule.char_nsmul_eq_zero n a.down.down

/-- The canonical constant H1 action from original coefficient annihilation. -/
abbrev constantOneZModModule (n : ℕ) :
    Module (ZMod n)
      (Sheaf.H.{w} (ConstantFinite.coefficient (ULift.{u} (ZMod n)) X.left) 1) :=
  AddCommGroup.zmodModule (nsmul_h1_eq_zero_of_killedBy (constantZMod_killedBy (X := X) n))

/-- The chosen constant coordinates are linear for the original action. -/
def constantOneRankLinearEquiv (n : ℕ) (hn : 0 < n) (hunit : IsUnit (n : k)) :
    letI := constantOneZModModule (X := X) n
    Sheaf.H.{w} (ConstantFinite.coefficient (ULift.{u} (ZMod n)) X.left) 1 ≃ₗ[ZMod n]
      (Fin (2 * coherentGenus k X) → ZMod n) := by
  let := constantOneZModModule (X := X) n
  let e := constantOneRankAddEquiv hX n hn hunit
  exact { e with map_smul' := (e.toAddMonoidHom.toZModLinearMap n).map_smul }

/-- The constant linear coordinates retain the same original additive map. -/
theorem constantOneRankLinearEquiv_toAddEquiv (n : ℕ) (hn : 0 < n)
    (hunit : IsUnit (n : k)) :
    letI := constantOneZModModule (X := X) n
    (constantOneRankLinearEquiv hX n hn hunit).toAddEquiv =
      constantOneRankAddEquiv hX n hn hunit := rfl

/-- A basis on original constant H1, including n=1 and g=0. -/
def constantOneBasis (n : ℕ) (hn : 0 < n) (hunit : IsUnit (n : k)) :
    letI := constantOneZModModule (X := X) n
    Module.Basis (Fin (2 * coherentGenus k X)) (ZMod n)
      (Sheaf.H.{w} (ConstantFinite.coefficient (ULift.{u} (ZMod n)) X.left) 1) := by
  let := constantOneZModModule (X := X) n
  exact AddSubgroup.TorsionBy.basisOfEquivRank _ n (constantOneRankAddEquiv hX n hn hunit)

end AlgebraicGeometry.Scheme.EtaleCohomology.Curves
