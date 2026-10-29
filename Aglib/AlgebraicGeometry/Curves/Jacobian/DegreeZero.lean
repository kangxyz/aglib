/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Curves.Jacobian.DegreeStrata
public import Aglib.AlgebraicGeometry.Curves.Jacobian.IdentityComponent

/-!
# The Jacobian of a curve: the identity component of the Picard scheme is the degree-zero part

Let `k` be an algebraically closed field, `X` a smooth proper geometrically connected curve over
`k` (`Curve.Properties X`) of genus `g`, and let `P`, locally of finite type and separated over
`k`, represent `Pic_{X/k,(fppf)}` on locally Noetherian test schemes through `R` (for instance the
Picard scheme of `exists_representableBy_fppfPicardSheaf_properties`), with group law
`picardCommGrpObj X.hom P R` and identity component `J = Pic⁰_{X/k}`. Then (Stacks, Picard Schemes
of Curves, Lemma 6.7, Tag 0BA0, and its proof; Milne, *Jacobian Varieties*, §1, p. 3):

* `exists_isClopen_degreeZero`: the degree-zero stratum of `P` (for a projective embedding of `X`,
  [DegreeStrata](DegreeStrata.lean)) is an open and closed set containing the unit point, and the
  rational point `picardPoint P R c` of a class `c` lies in it only if `deg c = 0`;
* `range_abelMorphism_eq_identityComponent_of_isAlgClosed`: for every rational point `o` of `X`,
  **the image of the Abel morphism `a_g : X^g ⟶ P`, `(p_i) ↦ Σ (p_i - o)`, is `J`**;
* `picardPoint_mem_identityComponent_iff_of_isAlgClosed`: **the rational points of `J` are the
  degree-zero classes of `Pic(X)`** (Stacks 0BA0(2); Milne p. 3); with
  `picardPointAddEquivOfIsSplitEpiOfIsProperOfFlatOfGeometricallyIntegral`, the rational points of
  `P` are `Pic(X)` as a group;
* `isProper_identityComponentOver_of_isAlgClosed`: **`J` is proper over `k`** (Stacks 0BA0, proof),
  since `X^g ⟶ J` is surjective and `X^g` is proper;
* `identityComponent_eq_opens_eulerCondition_degreeStratumPolynomial_zero_of_isAlgClosed`: for a
  closed embedding `X ⊆ P^N_k`, **`J` is the Hilbert-polynomial stratum of
  `m ↦ m · deg O(1) + 1 - g`**, the degree-zero stratum;
* `degreeZeroAddEquivOfIsAlgClosed`: the rational points of `J` are `ker(deg : Pic(X) → ℤ)` as
  groups;
* `exists_representableBy_fppfPicardSheaf_isProper_identityComponentOver_of_isAlgClosed`: these
  statements together, for the Picard scheme of `X`.

Only `Curve.Properties X` and the algebraic closedness of `k` are assumed; a rational point of
`X` exists (`Curve.Properties.exists_rationalPoint_of_isAlgClosed`) and is needed only to state
the Abel morphism. Smoothness of `J` and `dim J = g` are not treated.
-/

@[expose] public section

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory Opposite
open AlgebraicGeometry AlgebraicGeometry.Scheme AlgebraicGeometry.Scheme.Modules.Invertible
open AlgebraicGeometry.ProjectiveSpace
open AlgebraicGeometry.Scheme.RelativePicard AlgebraicGeometry.Scheme.RelativePicard.Strata
open AlgebraicGeometry.Scheme.Group AlgebraicGeometry.Scheme.OverField.Curve.Abel.BoundedFamily

namespace AlgebraicGeometry.Scheme.OverField.Curve

section Embedded

variable {k : Type u} [Field k] {ι : Type u} {Y : Scheme.{u}} (i : Y ⟶ ProjectiveSpace k ι)
  [IsClosedImmersion i] {N : ℕ} (e : ι ≃ Fin (N + 1)) [Flat (i ≫ toSpec k ι)]
  (hX : Properties (Over.mk (i ≫ toSpec k ι) : FScheme k))
  (P : LocallyNoetherianOver (Spec (.of k))) [LocallyOfFiniteType P.obj.hom]
  [IsSeparated P.obj.hom]
  (R : ((locallyNoetherianOverInclusion (Spec (.of k))).op ⋙
    (fppfPicardSheaf (i ≫ toSpec k ι)).obj ⋙
      CategoryTheory.forget AddCommGrpCat.{u + 1}).RepresentableBy P)

/-- **The identity component is the degree-zero stratum** (Stacks, Tag 0BA0, proof): for a curve
`X ⊆ P^N_k` over an algebraically closed field, `J = Pic⁰_{X/k}` is the stratum of the Hilbert
polynomial `m ↦ m · deg O(1) + 1 - g` of the universal section. -/
theorem identityComponent_eq_opens_eulerCondition_degreeStratumPolynomial_zero_of_isAlgClosed
    [IsAlgClosed k] :
    letI := picardCommGrpObj (i ≫ toSpec k ι) P R
    (identityComponent P.obj : Set P.obj.left) =
      (eulerCondition i N e (degreeStratumPolynomial i hX 0)).opens (T := P.obj)
        (R.homEquiv (𝟙 P)) :=
  identityComponent_eq_of_isClopen_of_isAlgClosed (X := Over.mk (i ≫ toSpec k ι)) hX P R _
    (isClopen_opens_eulerCondition_degreeStratumPolynomial i e P R hX 0)
    (unitPoint_mem_opens_eulerCondition_degreeStratumPolynomial_zero i e P R hX)
    fun c hc => (picardPoint_mem_opens_eulerCondition_degreeStratumPolynomial_iff i e P R hX c
      0).mp hc

end Embedded

variable {k : Type u} [Field k] {X : FScheme k} (hX : Properties X)
  (P : LocallyNoetherianOver (Spec (.of k))) [LocallyOfFiniteType P.obj.hom]
  (R : ((locallyNoetherianOverInclusion (Spec (.of k))).op ⋙ (fppfPicardSheaf X.hom).obj ⋙
    CategoryTheory.forget AddCommGrpCat.{u + 1}).RepresentableBy P)

/-- **The degree-zero locus of the Picard scheme of a curve**, over any field: there is an open
and closed set of points of `P`, containing the unit point, such that the rational point
`picardPoint P R c` of a class `c` lies in it only if `deg c = 0`: the degree-zero stratum of a
projective embedding of `X` (`Curve.Properties.exists_closedImmersion_projectiveSpace`,
[DegreeStrata](DegreeStrata.lean)). -/
theorem exists_isClopen_degreeZero :
    ∃ Z : Set P.obj.left, IsClopen Z ∧
      (letI := picardCommGrpObj X.hom P R; Group.unitPoint P.obj) ∈ Z ∧
      ∀ c : PicardGroup X.left, (picardPoint P R c).left (IsLocalRing.closedPoint k) ∈ Z →
        curveDegree smoothFieldNormality normalComponentsOpen smoothFieldRegularity
          smoothClosedPointDimension smoothFieldDimension Picard.Degree.properCurveProductFormula
          X hX c = 0 := by
  obtain ⟨N, i, hi, hiX⟩ := hX.exists_closedImmersion_projectiveSpace
  have hflat := hX.flat
  obtain ⟨Xl, ⟨⟨⟩⟩, Xh⟩ := X
  change Xl ⟶ ProjectiveSpace k (ULift.{u} (Fin (N + 1))) at i
  change i ≫ ProjectiveSpace.toSpec k (ULift.{u} (Fin (N + 1))) = Xh at hiX
  subst hiX
  have e : ULift.{u} (Fin (N + 1)) ≃ Fin (N + 1) := Equiv.ulift
  have : Flat (i ≫ ProjectiveSpace.toSpec k (ULift.{u} (Fin (N + 1)))) := hflat
  exact ⟨_, isClopen_opens_eulerCondition_degreeStratumPolynomial i e P R hX 0,
    unitPoint_mem_opens_eulerCondition_degreeStratumPolynomial_zero i e P R hX,
    fun c hc => (picardPoint_mem_opens_eulerCondition_degreeStratumPolynomial_iff i e P R hX c
      0).mp hc⟩

variable [IsSeparated P.obj.hom]

/-- **The image of the Abel morphism is the identity component** (Stacks, Tag 0BA0, proof;
Milne, *Jacobian Varieties*, §1, p. 3): for a rational point `o` of a curve `X` over an
algebraically closed field, `a_g(X^g) = J = Pic⁰_{X/k}`. -/
theorem range_abelMorphism_eq_identityComponent_of_isAlgClosed [IsAlgClosed k]
    (o : Spec (.of k) ⟶ X.left)
    (ho : o ≫ X.hom = 𝟙 _) :
    letI := hX.smooth
    letI := hX.proper
    letI := picardCommGrpObj X.hom P R
    Set.range (abelMorphism o ho P R (coherentGenus k X)).hom.left = identityComponent P.obj := by
  obtain ⟨Z, hZ, hZ₁, hZdeg⟩ := exists_isClopen_degreeZero hX P R
  obtain ⟨hC, hJ⟩ :=
    range_abelMorphism_eq_and_identityComponent_eq_of_isClopen_of_isAlgClosed hX P R o ho Z hZ hZ₁
      hZdeg
  exact hC.trans hJ.symm

/-- **The rational points of `J = Pic⁰_{X/k}` are the degree-zero classes** (Stacks, Tag 0BA0(2);
Milne, *Jacobian Varieties*, p. 3): for a curve `X` over an algebraically closed field and a class
`L ∈ Pic(X)`, the rational point `picardPoint P R L` of `P` lies in `J` if and only if
`deg L = 0`. -/
theorem picardPoint_mem_identityComponent_iff_of_isAlgClosed [IsAlgClosed k]
    (L : PicardGroup X.left) :
    letI := picardCommGrpObj X.hom P R
    (picardPoint P R L).left (IsLocalRing.closedPoint k) ∈ identityComponent P.obj ↔
      curveDegree smoothFieldNormality normalComponentsOpen smoothFieldRegularity
        smoothClosedPointDimension smoothFieldDimension Picard.Degree.properCurveProductFormula
        X hX L = 0 := by
  obtain ⟨Z, hZ, hZ₁, hZdeg⟩ := exists_isClopen_degreeZero hX P R
  exact picardPoint_mem_identityComponent_iff_of_isClopen_of_isAlgClosed hX P R Z hZ hZ₁ hZdeg L

include hX in
/-- **The Jacobian `J = Pic⁰_{X/k}` is proper over `k`** (Stacks, Picard Schemes of Curves,
Lemma 6.7, Tag 0BA0, proof): for a curve `X` over an algebraically closed field, the identity
component of `P` is proper, as the image of the proper `X^g` under the Abel morphism. -/
theorem isProper_identityComponentOver_of_isAlgClosed [IsAlgClosed k] :
    letI := picardCommGrpObj X.hom P R
    IsProper (identityComponentOver P.obj).hom := by
  obtain ⟨Z, hZ, hZ₁, hZdeg⟩ := exists_isClopen_degreeZero hX P R
  exact isProper_identityComponentOver_of_isClopen_of_isAlgClosed hX P R Z hZ hZ₁ hZdeg

open scoped CategoryTheory.MonObj in
/-- **The rational points of `J = Pic⁰_{X/k}` are the degree-zero classes, as groups** (Stacks,
Tag 0BA0(2); Milne, *Jacobian Varieties*, p. 3): over an algebraically closed field, the rational
point of a degree-zero class factors through `J`, and this is an isomorphism from the kernel of
the degree onto the group of rational points of `J`, for the group law of
`grpObjIdentityComponentOver`. -/
def degreeZeroAddEquivOfIsAlgClosed [IsAlgClosed k] :
    letI := picardCommGrpObj X.hom P R
    (curveDegree smoothFieldNormality normalComponentsOpen smoothFieldRegularity
        smoothClosedPointDimension smoothFieldDimension Picard.Degree.properCurveProductFormula
        X hX).ker ≃+ Additive (𝟙_ (Over (Spec (.of k))) ⟶ identityComponentOver P.obj) :=
  letI := picardCommGrpObj X.hom P R
  haveI := hX.proper
  haveI := hX.flat
  haveI := hX.isGeometricallyIntegral
  have ho := hX.exists_rationalPoint_of_isAlgClosed
  haveI : IsSplitEpi X.hom := IsSplitEpi.mk' ⟨ho.choose, ho.choose_spec⟩
  have hsub (L : (curveDegree smoothFieldNormality normalComponentsOpen smoothFieldRegularity
      smoothClosedPointDimension smoothFieldDimension Picard.Degree.properCurveProductFormula
      X hX).ker) : Set.range (picardPoint P R L.1).left ⊆ identityComponent P.obj := by
    rintro _ ⟨x, rfl⟩
    have hx : x = IsLocalRing.closedPoint k := Subsingleton.elim (α := Spec (.of k)) _ _
    rw [hx]
    exact (picardPoint_mem_identityComponent_iff_of_isAlgClosed hX P R L.1).mpr L.2
  have hpt (L : PicardGroup X.left) :
      picardPoint P R L = Additive.toMul
        (picardPointAddEquivOfIsSplitEpiOfIsProperOfFlatOfGeometricallyIntegral P R L) :=
    (picardPointAddEquivOfIsSplitEpiOfIsProperOfFlatOfGeometricallyIntegral_apply P R L).symm
  let φ (L : (curveDegree smoothFieldNormality normalComponentsOpen smoothFieldRegularity
      smoothClosedPointDimension smoothFieldDimension Picard.Degree.properCurveProductFormula
      X hX).ker) : 𝟙_ (Over (Spec (.of k))) ⟶ identityComponentOver P.obj :=
    liftIdentityComponent P.obj (picardPoint P R L.1) (hsub L)
  have hφ (L : (curveDegree smoothFieldNormality normalComponentsOpen smoothFieldRegularity
      smoothClosedPointDimension smoothFieldDimension Picard.Degree.properCurveProductFormula
      X hX).ker) : φ L ≫ identityComponentι P.obj = picardPoint P R L.1 :=
    liftIdentityComponent_ι _ _ _
  let f : (curveDegree smoothFieldNormality normalComponentsOpen smoothFieldRegularity
      smoothClosedPointDimension smoothFieldDimension Picard.Degree.properCurveProductFormula
      X hX).ker →+ Additive (𝟙_ (Over (Spec (.of k))) ⟶ identityComponentOver P.obj) :=
    { toFun := fun L => Additive.ofMul (φ L)
      map_zero' := by
        change Additive.ofMul (φ 0) = Additive.ofMul 1
        congr 1
        rw [← cancel_mono (identityComponentι P.obj), hφ, MonObj.one_comp, hpt]
        simp
      map_add' := fun L₁ L₂ => by
        change Additive.ofMul (φ (L₁ + L₂)) = Additive.ofMul (φ L₁ * φ L₂)
        congr 1
        rw [← cancel_mono (identityComponentι P.obj), hφ, MonObj.mul_comp, hφ, hφ, hpt, hpt, hpt]
        simp }
  AddEquiv.ofBijective f
    ⟨fun L₁ L₂ h => Subtype.ext
      ((picardPoint_bijective_of_isSplitEpi_of_isProper_of_flat_of_geometricallyIntegral P R).1 (by
      rw [← hφ L₁, ← hφ L₂]
      exact congrArg (fun b => Additive.toMul b ≫ identityComponentι P.obj) h)),
    fun b => by
      obtain ⟨L, hL⟩ :=
        (picardPoint_bijective_of_isSplitEpi_of_isProper_of_flat_of_geometricallyIntegral P R).2
        (Additive.toMul b ≫ identityComponentι P.obj)
      have hdeg : L ∈ (curveDegree smoothFieldNormality normalComponentsOpen smoothFieldRegularity
          smoothClosedPointDimension smoothFieldDimension Picard.Degree.properCurveProductFormula
          X hX).ker := by
        refine (picardPoint_mem_identityComponent_iff_of_isAlgClosed hX P R L).mp ?_
        rw [hL]
        change (identityComponent P.obj).ι ((Additive.toMul b).left (IsLocalRing.closedPoint k)) ∈
          (identityComponent P.obj : Set P.obj.left)
        rw [← Scheme.Opens.range_ι]
        exact ⟨_, rfl⟩
      refine ⟨⟨L, hdeg⟩, ?_⟩
      apply Additive.toMul.injective
      change φ ⟨L, hdeg⟩ = Additive.toMul b
      rw [← cancel_mono (identityComponentι P.obj), hφ]
      exact hL⟩

/-- **The Jacobian of a smooth proper curve over an algebraically closed field** (Stacks, Picard
Schemes of Curves, Lemma 6.7, Tag 0BA0; Milne, *Jacobian Varieties*, §1, p. 3; Kleiman,
*The Picard scheme*, arXiv:math/0504020v1, Thm 4.8): there are a scheme `P` over `k`, locally of
finite type and separated, and a representation `R` of `Pic_{X/k,(fppf)}` on locally Noetherian
test schemes, such that for the group law `picardCommGrpObj X.hom P R` and its identity component
`J = Pic⁰_{X/k}`:

1. `J` is proper over `k`;
2. the rational point of a class `L ∈ Pic(X)` lies in `J` if and only if `deg L = 0`;
3. for every rational point `o` of `X`, `J` is the image of the Abel morphism `X^g ⟶ P`,
   `(p_i) ↦ Σ (p_i - o)`.

The further properties of `P` (group law, tangent space `H^1(X, 𝒪_X)`, `J` open and closed,
quasi-compact and geometrically irreducible, field extension) are not repeated here: they hold
for every representing `P` locally of finite type, by the theorems collected in
`exists_representableBy_fppfPicardSheaf_properties`; the rational points of `P` are `Pic(X)` as
a group (`picardPointAddEquivOfIsSplitEpiOfIsProperOfFlatOfGeometricallyIntegral`). -/
theorem exists_representableBy_fppfPicardSheaf_isProper_identityComponentOver_of_isAlgClosed
    [IsAlgClosed k] :
    ∃ (P : LocallyNoetherianOver (Spec (.of k)))
      (R : ((locallyNoetherianOverInclusion (Spec (.of k))).op ⋙
        (fppfPicardSheaf X.hom).obj ⋙
          CategoryTheory.forget AddCommGrpCat.{u + 1}).RepresentableBy P)
      (_ : LocallyOfFiniteType P.obj.hom) (_ : IsSeparated P.obj.hom),
      (letI := picardCommGrpObj X.hom P R;
        IsProper (identityComponentOver P.obj).hom ∧
        (∀ L : PicardGroup X.left,
          (picardPoint P R L).left (IsLocalRing.closedPoint k) ∈ identityComponent P.obj ↔
            curveDegree smoothFieldNormality normalComponentsOpen smoothFieldRegularity
              smoothClosedPointDimension smoothFieldDimension
              Picard.Degree.properCurveProductFormula X hX L = 0) ∧
        ∀ (o : Spec (.of k) ⟶ X.left) (ho : o ≫ X.hom = 𝟙 _),
          (letI := hX.smooth; letI := hX.proper;
            Set.range (abelMorphism o ho P R (coherentGenus k X)).hom.left =
              identityComponent P.obj)) := by
  obtain ⟨P, R, hP, hsep, -⟩ := exists_representableBy_fppfPicardSheaf_properties hX
  exact ⟨P, R, hP, hsep, isProper_identityComponentOver_of_isAlgClosed hX P R,
    picardPoint_mem_identityComponent_iff_of_isAlgClosed hX P R,
    fun o ho => range_abelMorphism_eq_identityComponent_of_isAlgClosed hX P R o ho⟩

end AlgebraicGeometry.Scheme.OverField.Curve
