/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Group.PointDivisor
public import Aglib.AlgebraicGeometry.Group.MultiplicationInvertible
public import Aglib.AlgebraicGeometry.IdealSheaf.BaseChange.Isomorphism
public import Aglib.AlgebraicGeometry.Modules.BaseChange.Affine
public import Aglib.AlgebraicGeometry.Morphisms.FiniteFlat.GeometricDegreeRank

/-!
# Identity and diagonal divisor classes for multiplication

The actual difference map identifies the diagonal ideal with the pullback
of the identity ideal. This supplies geometric input to the multiplication
degree calculation on the original group scheme.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open MonoidalCategory CartesianMonoidalCategory MonObj
open scoped CategoryTheory.MonObj
open AlgebraicGeometry.Scheme AlgebraicGeometry.Scheme.Hom AlgebraicGeometry.Scheme.OverField
open AlgebraicGeometry.Scheme.Modules.Invertible

universe u

namespace AlgebraicGeometry.Scheme.Group.Multiplication

attribute [local instance] Over.cartesianMonoidalCategory

variable {k : Type u} [Field k] (G : Grp (FScheme k))

/-- The original group difference morphism on the actual product. -/
def difference : G.X ⊗ G.X ⟶ G.X := fst G.X G.X / snd G.X G.X

/-- The difference and the second projection are product coordinates. -/
theorem difference_snd_isPullback :
    IsPullback (difference G) (snd G.X G.X) (toUnit G.X) (toUnit G.X) := by
  apply IsPullback.mk' (Subsingleton.elim _ _)
  · intro T a b hab hsecond
    apply CartesianMonoidalCategory.hom_ext
    · have h := hab
      simp only [difference, GrpObj.comp_div] at h
      rw [hsecond] at h
      exact (div_left_inj).mp h
    · exact hsecond
  · intro T a b _
    refine ⟨lift (a * b) b, ?_, by simp only [lift_snd]⟩
    simp only [difference, GrpObj.comp_div, lift_fst, lift_snd, mul_div_cancel_right]

/-- The diagonal is the actual fibre of difference over the identity. -/
theorem difference_identity_isPullback :
    IsPullback (toUnit G.X) (lift (𝟙 G.X) (𝟙 G.X)) η[G.X] (difference G) := by
  apply IsPullback.mk'
    (by simp only [difference, GrpObj.comp_div, lift_fst, lift_snd, div_self', Hom.one_def])
  · intro T a b _ hab
    have h := congrArg (fun f => f ≫ fst G.X G.X) hab
    simpa only [Category.assoc, lift_fst, Category.comp_id] using h
  · intro T a b hab
    refine ⟨b ≫ snd G.X G.X, Subsingleton.elim _ _, ?_⟩
    have h : b ≫ fst G.X G.X = b ≫ snd G.X G.X := by
      apply div_eq_one.mp
      rw [← GrpObj.comp_div]
      exact hab.symm.trans (congrArg (fun q => q ≫ η[G.X]) (Subsingleton.elim a (toUnit T)))
    apply CartesianMonoidalCategory.hom_ext
    · simpa only [Category.assoc, lift_fst, Category.comp_id] using h.symm
    · simp only [Category.assoc, lift_snd, Category.comp_id]

/-- The constant first-coordinate section is the identity fibre of the
first projection. -/
theorem fst_identity_isPullback :
    IsPullback (toUnit G.X) (lift (1 : G.X ⟶ G.X) (𝟙 G.X)) η[G.X] (fst G.X G.X) := by
  apply IsPullback.mk' (by simp only [lift_fst, Hom.one_def])
  · intro T a b _ hab
    have h := congrArg (fun f => f ≫ snd G.X G.X) hab
    simpa only [Category.assoc, lift_snd, Category.comp_id] using h
  · intro T a b hab
    refine ⟨b ≫ snd G.X G.X, Subsingleton.elim _ _, ?_⟩
    apply CartesianMonoidalCategory.hom_ext
    · simp only [Category.assoc, lift_fst, MonObj.comp_one]
      exact (hab.symm.trans
        (congrArg (fun q => q ≫ η[G.X]) (Subsingleton.elim a (toUnit T)))).symm
    · simp only [Category.assoc, lift_snd, Category.comp_id]

variable [SmoothOfRelativeDimension 1 G.X.hom] [IsSeparated G.X.hom]

/-- The actual invertible ideal sheaf of the identity section. -/
def identityIdealLineBundle : LineBundle G.X.left :=
  ⟨idealModule η[G.X].left,
    sectionIdeal_isLocallyRankOne smoothRelativeDivisorIdeal G.X.hom η[G.X].left (Over.w _)⟩

/-- Its class in the native Picard group. -/
def identityIdealClass : PicardGroup G.X.left := classOf _ (identityIdealLineBundle G)

/-- Pullback to a constant identity point factors through the field's
trivial Picard group. -/
theorem pullback_identityIdealClass_one (T : FScheme k) :
    pullbackClass (1 : T ⟶ G.X).left (identityIdealClass G) = 0 := by
  rw [Hom.one_def, Over.comp_left, pullbackClass_comp,
    fieldPicard_eq_zero k (pullbackClass η[G.X].left (identityIdealClass G)), pullbackClass_zero]

/-- Inversion fixes the identity ideal class through the original square of
identity sections and its canonical pullback map. -/
theorem pullback_identityIdealClass_inv :
    pullbackClass (ι[G.X]).left (identityIdealClass G) = identityIdealClass G := by
  have h : (𝟙 (Base k)) ≫ η[G.X].left = η[G.X].left ≫ (ι[G.X]).left := by
    simpa only [Category.id_comp, ← Over.comp_left] using congrArg Over.Hom.left
      (GrpObj.one_inv (G := G.X)).symm
  let : IsIso (idealPullbackMap η[G.X].left η[G.X].left (ι[G.X]).left
      (𝟙 (Base k)) h) := idealPullbackMap_isIso_of_iso_square _ _ _ _ h
  exact Quotient.sound ⟨asIso (idealPullbackMap η[G.X].left η[G.X].left (ι[G.X]).left
    (𝟙 (Base k)) h)⟩

/-- The actual diagonal ideal is the pullback of the identity ideal under
the original difference morphism. -/
theorem pullback_identityIdealClass_difference :
    pullbackClass (difference G).left (identityIdealClass G) =
      classOf _ (diagonalIdealLineBundle smoothRelativeDivisorIdeal G.X.hom) := by
  have H := (difference_snd_isPullback G).map (Over.forget (Base k))
  have H' := (difference_identity_isPullback G).map (Over.forget (Base k))
  have hc : IsClosedImmersion η[G.X].left :=
    AlgebraicGeometry.isClosedImmersion_of_comp_eq_id G.X.hom η[G.X].left (Over.w _)
  have hf : Flat (η[G.X].left ≫ G.X.hom) := by rw [Over.w]; infer_instance
  have hi := relativeCartierIdealBaseChange (Base k) G.X.left G.X.left
    (G.X ⊗ G.X).left (Base k) G.X.left G.X.hom G.X.hom (snd G.X G.X).left
    (difference G).left η[G.X].left (lift (𝟙 G.X) (𝟙 G.X)).left G.X.hom H'.w H H' hc
    (identityIdealLineBundle G).property hf
  let := hi
  exact Quotient.sound ⟨asIso (idealPullbackMap η[G.X].left
    (lift (𝟙 G.X) (𝟙 G.X)).left (difference G).left G.X.hom H'.w)⟩

/-- The constant-origin graph ideal is the first-projection pullback of
the actual identity ideal. -/
theorem pullback_identityIdealClass_fst :
    pullbackClass (fst G.X G.X).left (identityIdealClass G) =
      classOf _ (originIdealLineBundle smoothRelativeDivisorIdeal G.X.hom η[G.X].left
        (Over.w _) G.X.hom) := by
  have H : IsPullback (fst G.X G.X).left (snd G.X G.X).left G.X.hom G.X.hom :=
    IsPullback.of_hasPullback _ _
  have H' := (fst_identity_isPullback G).map (Over.forget (Base k))
  have hc : IsClosedImmersion η[G.X].left :=
    AlgebraicGeometry.isClosedImmersion_of_comp_eq_id G.X.hom η[G.X].left (Over.w _)
  have hf : Flat (η[G.X].left ≫ G.X.hom) := by rw [Over.w]; infer_instance
  have hi := relativeCartierIdealBaseChange (Base k) G.X.left G.X.left
    (G.X ⊗ G.X).left (Base k) G.X.left G.X.hom G.X.hom (snd G.X G.X).left
    (fst G.X G.X).left η[G.X].left (lift (1 : G.X ⟶ G.X) (𝟙 G.X)).left G.X.hom H'.w H H'
    hc (identityIdealLineBundle G).property hf
  let := hi
  exact Quotient.sound ⟨asIso (idealPullbackMap η[G.X].left
    (lift (1 : G.X ⟶ G.X) (𝟙 G.X)).left (fst G.X G.X).left G.X.hom H'.w)⟩

/-- The normalized diagonal divisor class, expressed through the actual
identity ideal and difference map. -/
def normalizedDiagonalClass : PicardGroup (G.X ⊗ G.X).left :=
  -pullbackClass (difference G).left (identityIdealClass G) +
    pullbackClass (fst G.X G.X).left (identityIdealClass G) +
      pullbackClass (snd G.X G.X).left (identityIdealClass G)

/-- Interchanging the factors fixes the normalized diagonal class. -/
theorem normalizedDiagonalClass_symmetry :
    pullbackClass (β_ G.X G.X).hom.left (normalizedDiagonalClass G) =
      normalizedDiagonalClass G := by
  have hd : (β_ G.X G.X).hom ≫ difference G = difference G ≫ ι[G.X] := by
    change (β_ G.X G.X).hom ≫ difference G = (difference G)⁻¹
    simp only [difference, GrpObj.comp_div, braiding_hom_fst, braiding_hom_snd, inv_div]
  change (pullbackHom moduleTensorPullback (β_ G.X G.X).hom.left)
    (-pullbackClass (difference G).left (identityIdealClass G) +
      pullbackClass (fst G.X G.X).left (identityIdealClass G) +
        pullbackClass (snd G.X G.X).left (identityIdealClass G)) = _
  rw [map_add, map_add, map_neg]
  simp only [pullbackHom_apply, ← pullbackClass_comp, ← Over.comp_left,
    hd, braiding_hom_fst, braiding_hom_snd]
  simp only [Over.comp_left, pullbackClass_comp, pullback_identityIdealClass_inv,
    normalizedDiagonalClass]
  abel

/-- Restricting the normalized diagonal class to the diagonal gives twice
the actual identity ideal class. The self-intersection term is trivial
because difference is constant on the diagonal. -/
theorem normalizedDiagonalClass_diagonal :
    pullbackClass (lift (𝟙 G.X) (𝟙 G.X)).left (normalizedDiagonalClass G) =
      2 • identityIdealClass G := by
  have hd : lift (𝟙 G.X) (𝟙 G.X) ≫ difference G = (1 : G.X ⟶ G.X) := by
    simp only [difference, GrpObj.comp_div, lift_fst, lift_snd, div_self']
  change (pullbackHom moduleTensorPullback (lift (𝟙 G.X) (𝟙 G.X)).left)
    (-pullbackClass (difference G).left (identityIdealClass G) +
      pullbackClass (fst G.X G.X).left (identityIdealClass G) +
        pullbackClass (snd G.X G.X).left (identityIdealClass G)) = _
  rw [map_add, map_add, map_neg]
  simp only [pullbackHom_apply, ← pullbackClass_comp, ← Over.comp_left,
    hd, lift_fst, lift_snd, Over.id_left, pullbackClass_id, pullback_identityIdealClass_one,
    neg_zero, zero_add, two_nsmul]

/-- The diagonal class above is precisely the previously constructed
normalized Abel class of the identity morphism. -/
theorem degreeZeroPointClass_id_val (hG : Curve.Properties G.X) :
    (PointDivisor.degreeZeroPointClass G hG G.X (𝟙 G.X)).val.val =
      normalizedDiagonalClass G := by
  let s : G.X ⟶ G.X ⊗ G.X := lift (1 : G.X ⟶ G.X) (𝟙 G.X)
  have hd : s ≫ difference G = ι[G.X] := by
    simp only [s, difference, GrpObj.comp_div, lift_fst, lift_snd, one_div, Hom.inv_def,
      Category.id_comp]
  have ha : abelClass smoothRelativeDivisorIdeal G.X.hom η[G.X].left (Over.w _)
      G.X.hom (𝟙 G.X.left) (Category.id_comp _) =
        -pullbackClass (difference G).left (identityIdealClass G) +
          pullbackClass (fst G.X G.X).left (identityIdealClass G) := by
    rw [abelClass_eq, pullback_identityIdealClass_difference, pullback_identityIdealClass_fst]
    rfl
  have hs : pullbackClass s.left
      (-pullbackClass (difference G).left (identityIdealClass G) +
        pullbackClass (fst G.X G.X).left (identityIdealClass G)) = -identityIdealClass G := by
    change (pullbackHom moduleTensorPullback s.left)
      (-pullbackClass (difference G).left (identityIdealClass G) +
        pullbackClass (fst G.X G.X).left (identityIdealClass G)) = -identityIdealClass G
    rw [map_add, map_neg]
    simp only [pullbackHom_apply, ← pullbackClass_comp, ← Over.comp_left, hd,
      pullback_identityIdealClass_inv]
    have hfst : s ≫ fst G.X G.X = (1 : G.X ⟶ G.X) := lift_fst _ _
    rw [hfst, pullback_identityIdealClass_one, add_zero]
  change (show PicardGroup (G.X ⊗ G.X).left from
      abelClass smoothRelativeDivisorIdeal G.X.hom η[G.X].left (Over.w _)
        G.X.hom (𝟙 G.X.left) (Category.id_comp _)) -
    pullbackClass (snd G.X G.X).left (pullbackClass s.left
      (abelClass smoothRelativeDivisorIdeal G.X.hom η[G.X].left (Over.w _)
        G.X.hom (𝟙 G.X.left) (Category.id_comp _))) = _
  rw [ha, hs, pullbackClass_neg moduleTensorPullback]
  dsimp only [normalizedDiagonalClass]
  abel

/-- Multiplication in the second coordinate scales the actual normalized
diagonal Picard class. This is the proved point/divisor group bridge applied
to the literal scheme multiplication power. -/
theorem normalizedDiagonalClass_whiskerLeft [IsAlgClosed k] (hG : Curve.Properties G.X)
    (hg : Curve.coherentGenus k G.X = 1) (n : ℕ) :
    pullbackClass (G.X ◁ ((𝟙 G.X) ^ n)).left (normalizedDiagonalClass G) =
      n • normalizedDiagonalClass G := by
  have h := PointDivisor.degreeZeroPointClass_pow G hG hg G.X (𝟙 G.X) n
  have hn := Curve.Abel.degreeZeroAbelClass_naturality smoothFieldNormality normalComponentsOpen
    smoothFieldRegularity smoothClosedPointDimension smoothFieldDimension
    Curve.Picard.Degree.properCurveProductFormula moduleTensorPullback
    Curve.Abel.FiniteCartierDegree.finiteCartierIdealDegree relativeCartierIdealBaseChange
    smoothRelativeDivisorIdeal G.X hG η[G.X].left (Over.w _) ((𝟙 G.X) ^ n) (𝟙 G.X)
  rw [Category.comp_id] at hn
  dsimp only [PointDivisor.degreeZeroPointClass] at h
  rw [hn] at h
  have h' := congrArg (fun a => a.val.val) h
  change pullbackClass (G.X ◁ ((𝟙 G.X) ^ n)).left
      (PointDivisor.degreeZeroPointClass G hG G.X (𝟙 G.X)).val.val =
    n • (PointDivisor.degreeZeroPointClass G hG G.X (𝟙 G.X)).val.val at h'
  simpa only [degreeZeroPointClass_id_val] using h'

/-- Scaling the second point scales the pullback of the normalized
diagonal class on an arbitrary test scheme. -/
theorem normalizedDiagonalClass_lift_pow_right [IsAlgClosed k] (hG : Curve.Properties G.X)
    (hg : Curve.coherentGenus k G.X = 1) (T : FScheme k)
    (f g : T ⟶ G.X) (n : ℕ) :
    pullbackClass (lift f (g ^ n)).left (normalizedDiagonalClass G) =
      n • pullbackClass (lift f g).left (normalizedDiagonalClass G) := by
  have hc : lift f g ≫ (G.X ◁ ((𝟙 G.X) ^ n)) = lift f (g ^ n) := by
    apply CartesianMonoidalCategory.hom_ext <;>
      simp only [Category.assoc, whiskerLeft_fst, whiskerLeft_snd, lift_fst, lift_snd,
        MonObj.comp_pow, Category.comp_id]
  calc
    _ = pullbackClass (lift f g).left
        (pullbackClass (G.X ◁ ((𝟙 G.X) ^ n)).left (normalizedDiagonalClass G)) := by
      rw [← pullbackClass_comp, ← Over.comp_left, hc]
    _ = n • pullbackClass (lift f g).left (normalizedDiagonalClass G) := by
      rw [normalizedDiagonalClass_whiskerLeft G hG hg n]
      exact map_nsmul (pullbackHom moduleTensorPullback (lift f g).left) _ _

/-- Symmetry of the normalized diagonal class on arbitrary pairs of
scheme-valued points. -/
theorem normalizedDiagonalClass_lift_swap (T : FScheme k) (f g : T ⟶ G.X) :
    pullbackClass (lift f g).left (normalizedDiagonalClass G) =
      pullbackClass (lift g f).left (normalizedDiagonalClass G) := by
  have hc : lift f g ≫ (β_ G.X G.X).hom = lift g f := by
    apply CartesianMonoidalCategory.hom_ext <;>
      simp only [Category.assoc, braiding_hom_fst, braiding_hom_snd, lift_fst, lift_snd]
  calc
    _ = pullbackClass (lift f g).left
        (pullbackClass (β_ G.X G.X).hom.left (normalizedDiagonalClass G)) := by
      rw [normalizedDiagonalClass_symmetry]
    _ = _ := by rw [← pullbackClass_comp, ← Over.comp_left, hc]

/-- The actual multiplication morphism scales twice the identity ideal
class by the square of the level. This is a Picard-class equality proved
from the diagonal geometry and the actual Abel group-law bridge. -/
theorem pullback_twice_identityIdealClass [IsAlgClosed k] (hG : Curve.Properties G.X)
    (hg : Curve.coherentGenus k G.X = 1) (n : ℕ) :
    pullbackClass ((𝟙 G.X) ^ n).left (2 • identityIdealClass G) =
      (n * n) • (2 • identityIdealClass G) := by
  rw [← normalizedDiagonalClass_diagonal G]
  rw [← pullbackClass_comp, ← Over.comp_left]
  have hc : ((𝟙 G.X) ^ n) ≫ lift (𝟙 G.X) (𝟙 G.X) =
      lift ((𝟙 G.X) ^ n) ((𝟙 G.X) ^ n) := by
    simp only [comp_lift, Category.comp_id]
  rw [hc, normalizedDiagonalClass_lift_pow_right G hG hg G.X ((𝟙 G.X) ^ n) (𝟙 G.X) n,
    normalizedDiagonalClass_lift_swap G G.X ((𝟙 G.X) ^ n) (𝟙 G.X),
    normalizedDiagonalClass_lift_pow_right G hG hg G.X (𝟙 G.X) (𝟙 G.X) n,
    smul_smul]

local notation "curveDegree" => Curve.curveDegree smoothFieldNormality normalComponentsOpen
  smoothFieldRegularity smoothClosedPointDimension smoothFieldDimension
  Curve.Picard.Degree.properCurveProductFormula G.X

/-- The identity ideal has degree minus one in the original residue-weighted
curve degree. The positive identity divisor is the actual rational section
and has finite-scheme degree one. -/
theorem identityIdealClass_curveDegree (hG : Curve.Properties G.X) :
    curveDegree hG (identityIdealClass G) = -1 := by
  let : IsIntegral G.X.left := hG.isIntegral
  let : IsNoetherian G.X.left := Curve.curveProperties_isNoetherian hG
  let (x : ClosedPoint G.X.left) : IsDiscreteValuationRing (G.X.left.presheaf.stalk x.val) :=
    Curve.curveProperties_closedPoint_stalk_dvr smoothFieldNormality smoothFieldRegularity
      smoothClosedPointDimension hG x.val x.property
  let : IsProper G.X.hom := hG.proper
  have hc : IsClosedImmersion η[G.X].left :=
    AlgebraicGeometry.isClosedImmersion_of_comp_eq_id G.X.hom η[G.X].left (Over.w _)
  have hf : IsFinite (η[G.X].left ≫ G.X.hom) := by
    rw [Over.w]
    change IsFinite (𝟙 (Base k))
    infer_instance
  let hd := Curve.curveProperties_dimension smoothFieldDimension hG
  have h := Curve.Abel.FiniteCartierDegree.finiteCartierIdealDegree k G.X.left (Base k)
    G.X.hom η[G.X].left (le_of_eq hd)
    (Curve.Picard.Degree.properCurveProductFormula k G.X.left G.X.hom hd)
    (identityIdealLineBundle G).property hG.proper hc hf
  rw [Over.w, Over.tensorUnit_hom, finiteSchemeDegree_id, Nat.cast_one,
    Curve.Picard.Degree.lineBundleDegree_dual] at h
  change -(curveDegree hG (identityIdealClass G)) = 1 at h
  omega

omit [SmoothOfRelativeDimension 1 G.X.hom] [IsSeparated G.X.hom] in
/-- Every geometric fibre of the literal multiplication morphism has
cardinality `n*n` over an algebraically closed base field. The only geometric
inputs are the actual curve properties and actual coherent genus one. -/
theorem multiplication_hasGeometricDegree_of_isAlgClosed [IsAlgClosed k]
    (hG : Curve.Properties G.X) (hg : Curve.coherentGenus k G.X = 1)
    (n : ℕ) (hn : IsUnit (n : k)) : HasGeometricDegree ((𝟙 G.X) ^ n) (n * n) := by
  let : SmoothOfRelativeDimension 1 G.X.hom := hG.smooth
  let : IsProper G.X.hom := hG.proper
  let : ConnectedSpace G.X.left := Curve.curveProperties_connectedSpace hG
  obtain ⟨hf, he, hs⟩ := multiplication_finite_etale_of_invertible G hG n hn
  let := hf
  let := he
  let := hs
  have hfree := finiteLocallyFree_of_finite_etale finiteFlatPresentationLocallyFree
    ((𝟙 G.X) ^ n).left
  obtain ⟨d, hd⟩ := exists_hasLocallyFreeRank ((𝟙 G.X) ^ n).left hfree
  have hscale := Curve.curveDegree_pullback_of_hasLocallyFreeRank smoothFieldNormality
    normalComponentsOpen smoothFieldRegularity smoothClosedPointDimension smoothFieldDimension
    Curve.Picard.Degree.properCurveProductFormula Scheme.Modules.affineModuleBaseChange
    FiniteFlat.finiteDominantGenericFibre Curve.Picard.NormDegree.finiteMorphismNormOrder
    ((𝟙 G.X) ^ n) hG hG d hd (2 • identityIdealClass G)
  have hI := identityIdealClass_curveDegree G hG
  have hQ : curveDegree hG (2 • identityIdealClass G) = -2 := by
    rw [map_nsmul, hI]
    norm_num
  rw [pullback_twice_identityIdealClass G hG hg n, map_nsmul, hQ] at hscale
  have hd' : d = n * n := by
    have heq : (d : ℤ) = (n * n : ℕ) := by
      simp only [nsmul_eq_mul] at hscale
      linarith
    exact_mod_cast heq
  subst d
  exact (hasLocallyFreeRank_iff_hasGeometricDegree finiteFlatPresentationLocallyFree
    Scheme.Modules.affineModuleBaseChange ((𝟙 G.X) ^ n) (n * n)).mp hd

omit [SmoothOfRelativeDimension 1 G.X.hom] [IsSeparated G.X.hom] in
/-- Multiplication by an invertible natural level has every geometric
fibre of cardinality `n*n`, over the original arbitrary field. Coherent
genus one is the explicit genus hypothesis of the elliptic-curve source. -/
theorem multiplication_hasGeometricDegree (hG : Curve.Properties G.X)
    (hg : Curve.coherentGenus k G.X = 1) (n : ℕ) (hn : IsUnit (n : k)) :
    HasGeometricDegree ((𝟙 G.X) ^ n) (n * n) := by
  obtain ⟨hf, he, hs⟩ := multiplication_finite_etale_of_invertible G hG n hn
  let := hf
  let := he
  let := hs
  let : IsMonHom ((𝟙 G.X) ^ n) :=
    Curve.pointedMorphism_of_curveProperties G G hG hG _ (multiplication_pointed G n)
  let f : G ⟶ G := Grp.ofHom ((𝟙 G.X) ^ n)
  let : IsFinite f.hom.hom.left := hf
  let : Etale f.hom.hom.left := he
  let K := AlgebraicClosure k
  let s : Spec (.of K) ⟶ Base k := Spec.algebraMap k K
  let P := Over.pullback s
  let B := Scheme.Group.BaseChange.groupSchemeBaseChange s
  let G' := B.functor.obj G
  let f' := B.functor.map f
  let : GrpObj (P.obj G.X) := Functor.grpObjObj
  have hSquare : IsPullback (pullback.fst G.X.hom s) f'.hom.hom.left
      f.hom.hom.left (pullback.fst G.X.hom s) := by
    apply IsPullback.flip
    apply IsPullback.of_right (h₁₂ := pullback.snd G.X.hom s)
      (h₂₂ := G.X.hom) (v₁₃ := s)
      _ (Scheme.Group.BaseChange.groupSchemeBaseChange_map_left_fst s f)
      (IsPullback.of_hasPullback G.X.hom s).flip
    simpa only [Scheme.Group.BaseChange.groupSchemeBaseChange_map_left_snd, Over.w] using
      (IsPullback.of_hasPullback G.X.hom s).flip
  have hG' : Curve.Properties G'.X :=
    { smooth := MorphismProperty.pullback_snd G.X.hom s hG.smooth
      proper := MorphismProperty.pullback_snd G.X.hom s hG.proper
      connected := MorphismProperty.pullback_snd G.X.hom s hG.connected }
  have hg' : Curve.coherentGenus K G'.X = 1 :=
    (Curve.coherentGenus_fieldBaseChange K Cohomology.properStructureCohomologyBaseChange
      G.X hG).trans hg
  have hpow : f'.hom.hom = (𝟙 G'.X) ^ n := by
    change P.map ((𝟙 G.X) ^ n) = (𝟙 (P.obj G.X)) ^ n
    calc
      _ = (P.map (𝟙 G.X)) ^ n :=
        (P.homMonoidHom (X := G.X) (M := G.X)).map_pow _ _
      _ = _ := by rw [CategoryTheory.Functor.map_id]
  have hn' : IsUnit (n : K) := by
    simpa only [map_natCast] using hn.map (algebraMap k K)
  have hdeg' : HasGeometricDegree f'.hom.hom (n * n) := by
    rw [hpow]
    exact multiplication_hasGeometricDegree_of_isAlgClosed G' hG' hg' n hn'
  let : IsFinite f'.hom.hom.left := MorphismProperty.of_isPullback hSquare hf
  let : Etale f'.hom.hom.left := MorphismProperty.of_isPullback hSquare he
  let : Surjective s := ⟨Function.surjective_to_subsingleton s⟩
  have hrank (y : G.X.left) : ((𝟙 G.X) ^ n).left.finrank y = n * n := by
    obtain ⟨y', hy'⟩ := (pullback.fst G.X.hom s).surjective y
    change f.hom.hom.left.finrank y = n * n
    rw [← hy']
    exact (Scheme.Hom.finrank_of_isPullback _ _ _ _ hSquare y').symm.trans
      (nativeRank_eq_of_hasGeometricDegree f'.hom.hom (n * n) hdeg' y')
  apply (hasGeometricFibreRank_iff_hasGeometricDegree ((𝟙 G.X) ^ n) (n * n)).mp
  intro L _ _ t y
  exact (FiniteFlat.nativeRank_geometricFibre ((𝟙 G.X) ^ n).left L y.left).symm.trans
    (hrank (y.left (default : Spec (.of L))))

omit [SmoothOfRelativeDimension 1 G.X.hom] [IsSeparated G.X.hom] in
/-- The actual finite-flat rank of multiplication is `n*n` at every
point of the original curve. -/
theorem multiplication_nativeRank (hG : Curve.Properties G.X)
    (hg : Curve.coherentGenus k G.X = 1) (n : ℕ) (hn : IsUnit (n : k))
    (y : G.X.left) : ((𝟙 G.X) ^ n).left.finrank y = n * n := by
  obtain ⟨hf, he, _⟩ := multiplication_finite_etale_of_invertible G hG n hn
  let := hf
  let := he
  exact nativeRank_eq_of_hasGeometricDegree ((𝟙 G.X) ^ n) (n * n)
    (multiplication_hasGeometricDegree G hG hg n hn) y

omit [SmoothOfRelativeDimension 1 G.X.hom] [IsSeparated G.X.hom] in
/-- The complete native multiplication-geometry conjunction for the original
group scheme: finite, etale and geometric degree the square of the level. -/
theorem multiplication_finite_etale_degree (hG : Curve.Properties G.X)
    (hg : Curve.coherentGenus k G.X = 1) (n : ℕ) (hn : IsUnit (n : k)) :
    IsFinite ((𝟙 G.X) ^ n).left ∧ Etale ((𝟙 G.X) ^ n).left ∧
      HasGeometricDegree ((𝟙 G.X) ^ n) (n * n) :=
  ⟨(multiplication_finite_etale_of_invertible G hG n hn).1,
    (multiplication_finite_etale_of_invertible G hG n hn).2.1,
    multiplication_hasGeometricDegree G hG hg n hn⟩

end AlgebraicGeometry.Scheme.Group.Multiplication
