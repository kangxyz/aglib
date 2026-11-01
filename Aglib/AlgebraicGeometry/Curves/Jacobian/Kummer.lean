/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Curves.Jacobian.DegreeZero
public import Aglib.AlgebraicGeometry.Curves.Jacobian.Torsion
public import Aglib.AlgebraicGeometry.EtaleCohomology.Curves.Proper
public import Aglib.AlgebraicGeometry.EtaleCohomology.H1.FiniteLocallyConstant
public import Aglib.GroupTheory.Torsion.Equivalence

/-!
# The original Kummer H1 and the same Jacobian's rational torsion

Over an algebraically closed field, the original proper-curve Kummer
map identifies H1(mu_n) with actual Picard torsion. Positive torsion has
zero integer degree. The existing degree-zero point equivalence therefore
identifies it with torsion in the SAME supplied P/R identity component.
The original Picard point and representability maps are retained explicitly.

The original geometric-degree family is evaluated at the original field
and its identity map. No algebraic-closure point group is identified with
the rational point group without a field map. The canonical ZMod action
comes from original coefficient annihilation, not from coordinates.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory MonObj
open scoped CategoryTheory.MonObj
open AlgebraicGeometry.Scheme.RelativePicard AlgebraicGeometry.Scheme.Group
open AlgebraicGeometry.Scheme.Modules.Invertible
open AlgebraicGeometry.Scheme.Modules.Invertible.Torsion (picardTorsion)
open AlgebraicGeometry.Scheme.EtaleCohomology
open GroupCohomology.Kummer.Coefficients

universe u w

namespace AlgebraicGeometry.Scheme.OverField.Curve

attribute [local instance] Over.cartesianMonoidalCategory hasSheafifyLarge

variable {k : Type u} [Field k] {X : FScheme k} (hX : Properties X)

/-- Positive torsion in the original Picard group has zero integer degree. -/
theorem picardTorsion_degree_eq_zero (n : ℕ) (hn : 0 < n)
    (c : picardTorsion X.left n) :
    curveDegree smoothFieldNormality normalComponentsOpen smoothFieldRegularity
      smoothClosedPointDimension smoothFieldDimension Picard.Degree.properCurveProductFormula
      X hX c.val = 0 := by
  let d := curveDegree smoothFieldNormality normalComponentsOpen smoothFieldRegularity
    smoothClosedPointDimension smoothFieldDimension Picard.Degree.properCurveProductFormula X hX
  have hc : n • c.val = 0 := c.property
  have hd : n • d c.val = 0 := by
    rw [← map_nsmul, hc, map_zero]
  have hn0 : (n : ℤ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.ne_of_gt hn)
  exact (mul_eq_zero.mp (show (n : ℤ) * d c.val = 0 by
    simpa only [nsmul_eq_mul] using hd)).resolve_left hn0

/-- Original Picard torsion is the torsion subgroup of the original
degree kernel. Both directions retain the same Picard class. -/
def picardTorsionDegreeZeroAddEquiv (n : ℕ) (hn : 0 < n) :
    picardTorsion X.left n ≃+ AddSubgroup.torsionBy
      (curveDegree smoothFieldNormality normalComponentsOpen smoothFieldRegularity
        smoothClosedPointDimension smoothFieldDimension Picard.Degree.properCurveProductFormula
        X hX).ker (n : ℤ) where
  toFun c := ⟨⟨c.val, picardTorsion_degree_eq_zero hX n hn c⟩,
    AddSubgroup.torsionBy.nsmul_iff.mpr (Subtype.ext c.property)⟩
  invFun c := ⟨c.val.val,
    congrArg Subtype.val (AddSubgroup.torsionBy.nsmul_iff.mp c.property)⟩
  left_inv _ := Subtype.ext rfl
  right_inv _ := Subtype.ext (Subtype.ext rfl)
  map_add' _ _ := rfl

variable [IsAlgClosed k]
  (P : LocallyNoetherianOver (Spec (.of k))) [LocallyOfFiniteType P.obj.hom]
  [IsSeparated P.obj.hom]
  (R : ((locallyNoetherianOverInclusion (Spec (.of k))).op ⋙
    (fppfPicardSheaf X.hom).obj ⋙
      CategoryTheory.forget AddCommGrpCat.{u + 1}).RepresentableBy P)

/-- Positive Picard torsion is the actual rational torsion of the same
identity component, through the original degree-zero point equivalence. -/
def picardTorsionJacobianPointAddEquiv (n : ℕ) (hn : 0 < n) :
    letI := picardCommGrpObj X.hom P R
    picardTorsion X.left n ≃+ AddSubgroup.torsionBy
      (Additive (𝟙_ (Over (Spec (.of k))) ⟶ identityComponentOver P.obj)) (n : ℤ) := by
  let := picardCommGrpObj X.hom P R
  exact (picardTorsionDegreeZeroAddEquiv hX n hn).trans
    ((degreeZeroAddEquivOfIsAlgClosed hX P R).torsionByNat n)

/-- The point equivalence retains the original inclusion and Picard point. -/
theorem picardTorsionJacobianPointAddEquiv_inclusion (n : ℕ) (hn : 0 < n)
    (c : picardTorsion X.left n) :
    letI := picardCommGrpObj X.hom P R
    (picardTorsionJacobianPointAddEquiv hX P R n hn c).val.toMul ≫
      identityComponentι P.obj = picardPoint P R c.val := by
  let := picardCommGrpObj X.hom P R
  have hsub : Set.range (picardPoint P R c.val).left ⊆ identityComponent P.obj := by
    rintro _ ⟨x, rfl⟩
    have hx : x = IsLocalRing.closedPoint k := Subsingleton.elim (α := Spec (.of k)) _ _
    rw [hx]
    exact (picardPoint_mem_identityComponent_iff_of_isAlgClosed hX P R c.val).mpr
      (picardTorsion_degree_eq_zero hX n hn c)
  change (liftIdentityComponent P.obj (picardPoint P R c.val) hsub) ≫
    identityComponentι P.obj = _
  exact liftIdentityComponent_ι _ _ hsub

include hX in
/-- The original k-rational Jacobian torsion has cardinality n^(2g).
The existing geometric-degree family is evaluated at K=k and s=id. -/
theorem card_rationalTorsion_identityComponentOver_of_isUnit
    (n : ℕ) (hunit : IsUnit (n : k)) :
    letI := picardCommGrpObj X.hom P R
    Nat.card (AddSubgroup.torsionBy
      (Additive (𝟙_ (Over (Spec (.of k))) ⟶ identityComponentOver P.obj)) (n : ℤ)) =
      n ^ (2 * coherentGenus k X) := by
  let := picardCommGrpObj X.hom P R
  let G := Grp.mk (identityComponentOver P.obj)
  let T := 𝟙_ (Over (Spec (.of k)))
  let e : AddSubgroup.torsionBy (Additive (T ⟶ G.X)) (n : ℤ) ≃
      {x : T ⟶ G.X // x ≫ ((𝟙 G.X) ^ n) = 1} :=
    { toFun := fun x => ⟨x.val.toMul,
        (MultiplicationKernel.point_multiplication G n x.val.toMul).trans
          (show x.val.toMul ^ n = 1 from
            AddSubgroup.torsionBy.nsmul_iff.mp x.property)⟩
      invFun := fun x => ⟨Additive.ofMul x.val,
        AddSubgroup.torsionBy.nsmul_iff.mpr
          ((MultiplicationKernel.point_multiplication G n x.val).symm.trans x.property)⟩
      left_inv := fun x => Subtype.ext rfl
      right_inv := fun x => Subtype.ext rfl }
  exact (Nat.card_congr e).trans
    (hasGeometricDegree_multiplication_identityComponentOver_of_isUnit hX P R n hunit
      k (𝟙 (Spec (.of k))) 1)

variable [HasExt.{w} (AbelianSheaf.{u, u + 1} X.left)]

/-- Original roots H1 identifies with the same Jacobian's original rational
torsion. Global-unit divisibility and the Picard comparison are proved suppliers. -/
def rootsOneJacobianTorsionAddEquiv (n : ℕ) (hn : 0 < n) (hunit : IsUnit (n : k)) :
    letI := picardCommGrpObj X.hom P R
    Sheaf.H.{w} (mu X.left n) 1 ≃+ AddSubgroup.torsionBy
      (Additive (𝟙_ (Over (Spec (.of k))) ⟶ identityComponentOver P.obj)) (n : ℤ) := by
  let := picardCommGrpObj X.hom P R
  have hinv : IsUnit (n : Γ(X.left, ⊤)) := by
    simpa only [map_natCast] using hunit.map (Scheme.constants X)
  exact (EtaleCohomology.Curves.rootsOneAddEquiv hX n hn hinv).trans
    (picardTorsionJacobianPointAddEquiv hX P R n hn)

/-- The whole roots-to-Jacobian map, followed by the original inclusion,
is exactly the original Kummer-to-Picard map followed by the supplied R point map. -/
theorem rootsOneJacobianTorsionAddEquiv_comp_inclusion
    (n : ℕ) (hn : 0 < n) (hunit : IsUnit (n : k)) :
    letI := picardCommGrpObj X.hom P R
    (fun x : Sheaf.H.{w} (mu X.left n) 1 =>
      (rootsOneJacobianTorsionAddEquiv hX P R n hn hunit x).val.toMul ≫
        identityComponentι P.obj) =
      fun x => picardPoint P R (Kummer.rootsPicardMap X.left n x) := by
  let := picardCommGrpObj X.hom P R
  have hinv : IsUnit (n : Γ(X.left, ⊤)) := by
    simpa only [map_natCast] using hunit.map (Scheme.constants X)
  funext x
  have h := picardTorsionJacobianPointAddEquiv_inclusion hX P R n hn
    (EtaleCohomology.Curves.rootsOneAddEquiv hX n hn hinv x)
  change (rootsOneJacobianTorsionAddEquiv hX P R n hn hunit x).val.toMul ≫
    identityComponentι P.obj = _ at h
  refine h.trans (congrArg (picardPoint P R) ?_)
  exact DFunLike.congr_fun
    (EtaleCohomology.Curves.rootsOneAddEquiv_subtype hX n hn hinv) x

/-- The original representing equivalence R sees precisely the actual Kummer class. -/
theorem homEquiv_rootsOneJacobianTorsionAddEquiv
    (n : ℕ) (hn : 0 < n) (hunit : IsUnit (n : k))
    (x : Sheaf.H.{w} (mu X.left n) 1) :
    letI := picardCommGrpObj X.hom P R
    R.homEquiv (ObjectProperty.homMk
      ((rootsOneJacobianTorsionAddEquiv hX P R n hn hunit x).val.toMul ≫
        identityComponentι P.obj) : locallyNoetherianRationalPoint k ⟶ P) =
      picardPointClass X (Kummer.rootsPicardMap X.left n x) := by
  let := picardCommGrpObj X.hom P R
  rw [congrFun (rootsOneJacobianTorsionAddEquiv_comp_inclusion hX P R n hn hunit) x]
  exact homEquiv_picardPoint P R _

/-- The same actual Kummer equivalence is linear for the native annihilation
ZMod actions. The source action comes directly from mu_n coefficient annihilation. -/
def rootsOneJacobianTorsionLinearEquiv (n : ℕ) (hn : 0 < n) (hunit : IsUnit (n : k)) :
    letI := picardCommGrpObj X.hom P R
    letI : Module (ZMod n) (Sheaf.H.{w} (mu X.left n) 1) := AddCommGroup.zmodModule
      (EtaleCohomology.nsmul_h1_eq_zero_of_killedBy (mu_killedBy X.left n))
    letI := AddSubgroup.torsionBy.zmodModule
      (A := Additive (𝟙_ (Over (Spec (.of k))) ⟶ identityComponentOver P.obj)) (n := n)
    Sheaf.H.{w} (mu X.left n) 1 ≃ₗ[ZMod n] AddSubgroup.torsionBy
      (Additive (𝟙_ (Over (Spec (.of k))) ⟶ identityComponentOver P.obj)) (n : ℤ) := by
  let := picardCommGrpObj X.hom P R
  let : Module (ZMod n) (Sheaf.H.{w} (mu X.left n) 1) := AddCommGroup.zmodModule
    (EtaleCohomology.nsmul_h1_eq_zero_of_killedBy (mu_killedBy X.left n))
  let := AddSubgroup.torsionBy.zmodModule
    (A := Additive (𝟙_ (Over (Spec (.of k))) ⟶ identityComponentOver P.obj)) (n := n)
  let e := rootsOneJacobianTorsionAddEquiv hX P R n hn hunit
  exact { e with map_smul' := (e.toAddMonoidHom.toZModLinearMap n).map_smul }

end AlgebraicGeometry.Scheme.OverField.Curve
