/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.AbelianScheme.OverField.Multiplication.Torsion
public import Aglib.AlgebraicGeometry.Curves.Jacobian.Dimension
public import Aglib.AlgebraicGeometry.Curves.Jacobian.ProjectivityField
public import Aglib.AlgebraicGeometry.Group.IdentityComponent.Commutative

/-!
# Native multiplication rank and torsion of the same Jacobian

The same supplied locally Noetherian Picard representative P/R has an
actual smooth, geometrically integral, projective identity component.
Its original identity cotangent dimension is the coherent genus g of the
original curve. General all-field multiplication therefore has native
locally free rank n^(2g) at every positive level, as does its native kernel.

At invertible levels the actual geometric torsion has cardinality n^(2g)
and a noncanonical free description. The general theorem supplies every
divisor-level cardinality before applying the torsion classification. The
ZMod action below is the existing action from the actual annihilation law;
no transported module structure or canonical/Galois-equivariant basis is chosen.
Level one and genus zero are retained.
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry MonoidalCategory MonObj
open scoped CategoryTheory.MonObj
open AlgebraicGeometry.Scheme.RelativePicard AlgebraicGeometry.Scheme.Group
open AlgebraicGeometry.Scheme.FiniteEtale

universe u

namespace AlgebraicGeometry.Scheme.OverField.Curve

attribute [local instance] Over.cartesianMonoidalCategory

variable {k : Type u} [Field k] {X : FScheme k} (hX : Properties X)
  (P : LocallyNoetherianOver (Spec (.of k))) [LocallyOfFiniteType P.obj.hom]
  [IsSeparated P.obj.hom]
  (R : ((locallyNoetherianOverInclusion (Spec (.of k))).op ⋙
    (fppfPicardSheaf X.hom).obj ⋙
      CategoryTheory.forget AddCommGrpCat.{u + 1}).RepresentableBy P)

include hX in
/-- Positive multiplication on the same original Jacobian has native
locally free rank n^(2g) over every field, including inseparable levels. -/
theorem hasLocallyFreeRank_multiplication_identityComponentOver_of_pos
    (n : ℕ) (hn : 0 < n) :
    letI := picardCommGrpObj X.hom P R
    Hom.HasLocallyFreeRank ((𝟙 (identityComponentOver P.obj)) ^ n).left
      (n ^ (2 * coherentGenus k X)) := by
  let := picardCommGrpObj X.hom P R
  let := isHProjective_identityComponentOver hX P R
  let := geometricallyIntegral_identityComponentOver hX P R
  let := smooth_identityComponentOver hX P R
  simpa only [finrank_identityComponentCotangent_eq_coherentGenus hX P R] using
    Multiplication.multiplication_hasLocallyFreeRank (Grp.mk (identityComponentOver P.obj)) n hn

include hX in
/-- The existing native multiplication kernel of the same Jacobian has
rank n^(2g) on its original identity fibre square at every positive level. -/
theorem hasLocallyFreeRank_nativeMultiplicationKernel_identityComponentOver_of_pos
    (n : ℕ) (hn : 0 < n) :
    letI := picardCommGrpObj X.hom P R
    Hom.HasLocallyFreeRank
      (MultiplicationKernel.kernelGroup (Grp.mk (identityComponentOver P.obj)) n).X.hom
      (n ^ (2 * coherentGenus k X)) := by
  let := picardCommGrpObj X.hom P R
  let := isHProjective_identityComponentOver hX P R
  let := geometricallyIntegral_identityComponentOver hX P R
  let := smooth_identityComponentOver hX P R
  simpa only [finrank_identityComponentCotangent_eq_coherentGenus hX P R] using
    Multiplication.kernelGroup_hasLocallyFreeRank (Grp.mk (identityComponentOver P.obj)) n hn

include hX in
/-- Invertible multiplication on the original Jacobian has geometric
degree n^(2g), with the original scalar and original Picard representative. -/
theorem hasGeometricDegree_multiplication_identityComponentOver_of_isUnit
    (n : ℕ) (hn : IsUnit (n : k)) :
    letI := picardCommGrpObj X.hom P R
    HasGeometricDegree ((𝟙 (identityComponentOver P.obj)) ^ n)
      (n ^ (2 * coherentGenus k X)) := by
  let := picardCommGrpObj X.hom P R
  let := isHProjective_identityComponentOver hX P R
  let := geometricallyIntegral_identityComponentOver hX P R
  let := smooth_identityComponentOver hX P R
  simpa only [finrank_identityComponentCotangent_eq_coherentGenus hX P R] using
    Multiplication.multiplication_hasGeometricDegree_of_isUnit
      (Grp.mk (identityComponentOver P.obj)) n hn

include hX in
/-- The actual geometric n-torsion of the same Jacobian has cardinality
n^(2g) when n is invertible in the original field. -/
theorem card_torsionBy_identityComponentOver_of_isUnit
    (n : ℕ) (hn : IsUnit (n : k)) :
    letI := picardCommGrpObj X.hom P R
    Nat.card (AddSubgroup.torsionBy
      (MultiplicationKernel.geometricPoints (Grp.mk (identityComponentOver P.obj))) (n : ℤ)) =
      n ^ (2 * coherentGenus k X) := by
  let := picardCommGrpObj X.hom P R
  let := isHProjective_identityComponentOver hX P R
  let := geometricallyIntegral_identityComponentOver hX P R
  let := smooth_identityComponentOver hX P R
  simpa only [finrank_identityComponentCotangent_eq_coherentGenus hX P R] using
    Multiplication.card_geometric_torsionBy_of_isUnit (Grp.mk (identityComponentOver P.obj)) n hn

include hX in
/-- The actual algebraic-closure points of the existing native Jacobian
multiplication kernel have the same n^(2g) cardinality. -/
theorem card_nativeMultiplicationKernel_points_identityComponentOver_of_isUnit
    (n : ℕ) (hn : IsUnit (n : k)) :
    letI := picardCommGrpObj X.hom P R
    Nat.card (Over.mk (FieldGalois.geometricPoint k) ⟶
      (MultiplicationKernel.kernelGroup (Grp.mk (identityComponentOver P.obj)) n).X) =
      n ^ (2 * coherentGenus k X) := by
  let := picardCommGrpObj X.hom P R
  let := isHProjective_identityComponentOver hX P R
  let := geometricallyIntegral_identityComponentOver hX P R
  let := smooth_identityComponentOver hX P R
  simpa only [finrank_identityComponentCotangent_eq_coherentGenus hX P R] using
    Multiplication.card_nativeKernelPoints_of_isUnit (Grp.mk (identityComponentOver P.obj)) n hn

include hX in
/-- The same Jacobian's geometric n-torsion admits the noncanonical
free torsion description, using all divisor cardinalities from native degree. -/
theorem nonempty_torsionEquiv_identityComponentOver_of_isUnit
    (n : ℕ) (hn : IsUnit (n : k)) :
    letI := picardCommGrpObj X.hom P R
    Nonempty (AddSubgroup.torsionBy
      (MultiplicationKernel.geometricPoints (Grp.mk (identityComponentOver P.obj))) (n : ℤ) ≃+
      (Fin (2 * coherentGenus k X) → ZMod n)) := by
  let := picardCommGrpObj X.hom P R
  let := isHProjective_identityComponentOver hX P R
  let := geometricallyIntegral_identityComponentOver hX P R
  let := smooth_identityComponentOver hX P R
  rw [← finrank_identityComponentCotangent_eq_coherentGenus hX P R]
  exact Multiplication.nonempty_geometric_torsionEquiv_of_isUnit
    (Grp.mk (identityComponentOver P.obj)) n hn

include hX in
/-- The original torsionBy carries its native ZMod action from its
annihilation law and admits a basis indexed by Fin(2g). Only existence is
asserted, including the zero coefficient ring at level one. -/
theorem nonempty_torsionBasis_identityComponentOver_of_isUnit
    (n : ℕ) (hn : IsUnit (n : k)) :
    letI := picardCommGrpObj X.hom P R
    let T := AddSubgroup.torsionBy
      (MultiplicationKernel.geometricPoints (Grp.mk (identityComponentOver P.obj))) (n : ℤ)
    letI : Module (ZMod n) T := AddCommGroup.zmodModule
      (fun x : T => Subtype.ext (AddSubgroup.torsionBy.nsmul_iff.mp x.property))
    Nonempty (Module.Basis (Fin (2 * coherentGenus k X)) (ZMod n) T) := by
  let := picardCommGrpObj X.hom P R
  let T := AddSubgroup.torsionBy
    (MultiplicationKernel.geometricPoints (Grp.mk (identityComponentOver P.obj))) (n : ℤ)
  let : Module (ZMod n) T := AddCommGroup.zmodModule
    (fun x : T => Subtype.ext (AddSubgroup.torsionBy.nsmul_iff.mp x.property))
  obtain ⟨e⟩ := nonempty_torsionEquiv_identityComponentOver_of_isUnit hX P R n hn
  exact ⟨AddSubgroup.TorsionBy.basisOfEquivRank (2 * coherentGenus k X) n e⟩

end AlgebraicGeometry.Scheme.OverField.Curve
