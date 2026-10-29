/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Curves.Jacobian.AbelMorphism
public import Aglib.AlgebraicGeometry.Picard.Comparison.Isomorphism
public import Aglib.AlgebraicGeometry.Picard.Tangent.Comparison

/-!
# Rational points of the Picard scheme of a curve with a rational point

Let `k` be a field and `X` a scheme over `k`, proper and flat with geometrically integral fibres,
with a rational point `o`, and let `P` represent `Pic_{X/k,(fppf)}` on locally Noetherian test
schemes through `R`.

* `picardPointClass X : Pic(X) →+ Pic_{X/k,(fppf)}(k)`, the class of the pullback to
  `X ×_k k`, is bijective when `X ⟶ Spec k` has a section
  (`picardPointClass_bijective_of_isSplitEpi_of_isProper_of_flat_of_geometricallyIntegral`):
  pullback along the isomorphism
  `X ×_k k ⟶ X` is bijective, `Pic(X ×_k k) → P_{X/k}(k)` is bijective since `Pic(Spec k) = 0`,
  and `P_{X/k} ⟶ Pic_{X/k,(fppf)}` is an isomorphism when `X ⟶ Spec k` has a section (Kleiman,
  *The Picard scheme*, arXiv:math/0504020v1, Thm 2.5(2), p. 18;
  `isIso_toFppfPicardSheaf_of_isSplitEpi_of_isProper_of_flat_of_geometricallyIntegral`).
* `picardPointAddEquivOfIsSplitEpiOfIsProperOfFlatOfGeometricallyIntegral P R :
  Pic(X) ≃+ Additive (Spec k ⟶ P)`: **the rational points of `P` are the line-bundle classes on
  `X`**, as groups for the group law `picardCommGrpObj X.hom P R`.
  Its value at `L` is `picardPoint P R L`, the rational point attached to the class of `L` by `R`.
* `parameterPoint_comp_abelMorphism_eq_picardPoint`: on a rational point `a` of `X^n`, the Abel
  morphism takes the value `picardPoint P R L` for any class `L` on `X` whose pullback to `X ×_k k`
  is the specialization of the graph-sum family at `a`.
-/

@[expose] public section

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory Opposite
open AlgebraicGeometry AlgebraicGeometry.Scheme AlgebraicGeometry.Scheme.Modules.Invertible
open AlgebraicGeometry.Scheme.RelativePicard
open scoped CategoryTheory.MonObj

namespace AlgebraicGeometry.Scheme.OverField.Curve

variable {k : Type u} [Field k]

/-- The rational point `Spec k` over itself, as a locally Noetherian test scheme over `k`. -/
abbrev locallyNoetherianRationalPoint (k : Type u) [Field k] :
    LocallyNoetherianOver (Spec (.of k)) :=
  ⟨𝟙_ (Over (Spec (.of k))), inferInstanceAs (IsLocallyNoetherian (Spec (.of k)))⟩

variable (X : FScheme k)

/-- **The class of a line bundle as a rational section of the Picard sheaf**:
`Pic(X) → Pic(X ×_k k) → Pic_{X/k,(fppf)}(k)`. -/
def picardPointClass :
    PicardGroup X.left →+ (fppfPicardSheaf X.hom).obj.obj (op (𝟙_ (Over (Spec (.of k))))) :=
  ((quotientProjection X.hom ≫ toFppfPicardSheaf X.hom).app
    (op (𝟙_ (Over (Spec (.of k)))))).hom.comp
      (PullbackTensor.Local.pullbackHom (pullback.fst X.hom (𝟙 (Spec (.of k)))))

theorem picardPointClass_apply (L : PicardGroup X.left) :
    picardPointClass X L = (quotientProjection X.hom ≫ toFppfPicardSheaf X.hom).app
      (op (𝟙_ (Over (Spec (.of k))))) (pullbackClass (pullback.fst X.hom (𝟙 (Spec (.of k)))) L) :=
  rfl

variable {X}

/-- **`Pic(X) = Pic_{X/k,(fppf)}(k)` with a rational point** (Kleiman, *The Picard scheme*,
arXiv:math/0504020v1, Thm 2.5(2), p. 18, with `Pic(Spec k) = 0`): `X ⟶ Spec k` has a section
and is proper and flat with geometrically integral fibres. -/
theorem picardPointClass_bijective_of_isSplitEpi_of_isProper_of_flat_of_geometricallyIntegral
    [IsSplitEpi X.hom] [IsProper X.hom] [Flat X.hom] [GeometricallyIntegral X.hom] :
    Function.Bijective (picardPointClass X) := by
  have := isIso_toFppfPicardSheaf_of_isSplitEpi_of_isProper_of_flat_of_geometricallyIntegral X.hom
  have h₁ := ConcreteCategory.bijective_of_isIso
    ((toFppfPicardSheaf X.hom).app (op (𝟙_ (Over (Spec (.of k))))))
  have h₂ := quotientProjection_app_bijective_of_subsingleton X.hom (op (𝟙_ (Over (Spec (.of k)))))
    (inferInstanceAs (Subsingleton (PicardGroup (Spec (.of k)))))
  have h₃ : Function.Bijective (pullbackClass (pullback.fst X.hom (𝟙 (Spec (.of k))))) := by
    refine Function.bijective_iff_has_inverse.mpr
      ⟨pullbackClass (inv (pullback.fst X.hom (𝟙 (Spec (.of k))))), fun a => ?_, fun b => ?_⟩
    · rw [← pullbackClass_comp, IsIso.inv_hom_id, pullbackClass_id]
    · rw [← pullbackClass_comp, IsIso.hom_inv_id, pullbackClass_id]
  exact (h₁.comp h₂).comp h₃

/-- `Pic(X) ≃+ Pic_{X/k,(fppf)}(k)` when `X ⟶ Spec k` has a section and is proper and flat with
geometrically integral fibres. -/
def picardPointClassAddEquivOfIsSplitEpiOfIsProperOfFlatOfGeometricallyIntegral
    [IsSplitEpi X.hom] [IsProper X.hom] [Flat X.hom] [GeometricallyIntegral X.hom] :
    PicardGroup X.left ≃+ (fppfPicardSheaf X.hom).obj.obj (op (𝟙_ (Over (Spec (.of k))))) :=
  AddEquiv.ofBijective (picardPointClass X)
    (picardPointClass_bijective_of_isSplitEpi_of_isProper_of_flat_of_geometricallyIntegral (X := X))

variable (P : LocallyNoetherianOver (Spec (.of k)))
  (R : ((locallyNoetherianOverInclusion (Spec (.of k))).op ⋙ (fppfPicardSheaf X.hom).obj ⋙
    CategoryTheory.forget AddCommGrpCat.{u + 1}).RepresentableBy P)

/-- **The rational point of `P` of a line-bundle class** `L` on `X`: the point attached by `R` to
`picardPointClass X L`. -/
def picardPoint (L : PicardGroup X.left) : 𝟙_ (Over (Spec (.of k))) ⟶ P.obj :=
  ((R.homEquiv (X := locallyNoetherianRationalPoint k)).symm (picardPointClass X L)).hom

theorem homEquiv_picardPoint (L : PicardGroup X.left) :
    R.homEquiv (ObjectProperty.homMk (picardPoint P R L) : locallyNoetherianRationalPoint k ⟶ P) =
      picardPointClass X L :=
  R.homEquiv.apply_symm_apply _

/-- A rational point of `P` is the point of the class it corresponds to. -/
theorem picardPoint_eq_iff (L : PicardGroup X.left) (b : 𝟙_ (Over (Spec (.of k))) ⟶ P.obj) :
    picardPoint P R L = b ↔
      R.homEquiv (ObjectProperty.homMk b : locallyNoetherianRationalPoint k ⟶ P) =
        picardPointClass X L := by
  constructor
  · rintro rfl
    exact homEquiv_picardPoint P R L
  · intro h
    have h' : (ObjectProperty.homMk b : locallyNoetherianRationalPoint k ⟶ P) =
        (R.homEquiv (X := locallyNoetherianRationalPoint k)).symm (picardPointClass X L) :=
      R.homEquiv.eq_symm_apply.mpr h
    exact (congrArg InducedCategory.Hom.hom h').symm

/-- **Every rational point of `P` is the point of a unique class on `X`**, when `X ⟶ Spec k` has
a section and is proper and flat with geometrically integral fibres. -/
theorem picardPoint_bijective_of_isSplitEpi_of_isProper_of_flat_of_geometricallyIntegral
    [IsSplitEpi X.hom] [IsProper X.hom] [Flat X.hom] [GeometricallyIntegral X.hom] :
    Function.Bijective (picardPoint (X := X) P R) := by
  let e : (locallyNoetherianRationalPoint k ⟶ P) ≃ (𝟙_ (Over (Spec (.of k))) ⟶ P.obj) :=
    Equiv.mk (fun f => f.hom) (fun f => ObjectProperty.homMk f) (fun _ => rfl) (fun _ => rfl)
  exact (e.bijective.comp R.homEquiv.symm.bijective).comp
    (picardPointClass_bijective_of_isSplitEpi_of_isProper_of_flat_of_geometricallyIntegral (X := X))

variable [LocallyOfFiniteType P.obj.hom]

/-- **The rational point of the zero class is the unit section** of the group law
`picardCommGrpObj X.hom P R` (`picard_homEquiv_one`). -/
theorem picardPoint_zero :
    letI := picardCommGrpObj X.hom P R
    picardPoint P R 0 = η[P.obj] := by
  let := picardCommGrpObj X.hom P R
  rw [picardPoint_eq_iff, map_zero]
  have h0 := picard_homEquiv_one X.hom P R (locallyNoetherianRationalPoint k)
  have hone : (1 : (locallyNoetherianRationalPoint k).obj ⟶ P.obj) = η[P.obj] := by
    change CartesianMonoidalCategory.toUnit _ ≫ η[P.obj] = η[P.obj]
    rw [CartesianMonoidalCategory.toUnit_unit, Category.id_comp]
  rw [hone] at h0
  exact h0

/-- **The rational points of the Picard scheme are the line-bundle classes**, as groups:
`Pic(X) ≃+ Additive (Spec k ⟶ P)` for the group law `picardCommGrpObj X.hom P R`, when
`X ⟶ Spec k` has a section and is proper and flat with geometrically integral fibres. Its value at
`L` is `picardPoint P R L`. -/
def picardPointAddEquivOfIsSplitEpiOfIsProperOfFlatOfGeometricallyIntegral
    [IsSplitEpi X.hom] [IsProper X.hom] [Flat X.hom] [GeometricallyIntegral X.hom] :
    letI := picardCommGrpObj X.hom P R
    PicardGroup X.left ≃+ Additive (𝟙_ (Over (Spec (.of k))) ⟶ P.obj) :=
  letI := picardCommGrpObj X.hom P R
  (picardPointClassAddEquivOfIsSplitEpiOfIsProperOfFlatOfGeometricallyIntegral (X := X)).trans
    (picardHomAddEquiv X.hom P R (locallyNoetherianRationalPoint k)).symm

theorem picardPointAddEquivOfIsSplitEpiOfIsProperOfFlatOfGeometricallyIntegral_apply
    [IsSplitEpi X.hom] [IsProper X.hom] [Flat X.hom] [GeometricallyIntegral X.hom]
    (L : PicardGroup X.left) :
    letI := picardCommGrpObj X.hom P R
    Additive.toMul (picardPointAddEquivOfIsSplitEpiOfIsProperOfFlatOfGeometricallyIntegral P R L) =
      picardPoint P R L := by
  let := picardCommGrpObj X.hom P R
  symm
  rw [picardPoint_eq_iff]
  exact (picardHomAddEquiv X.hom P R (locallyNoetherianRationalPoint k)).apply_symm_apply _

end AlgebraicGeometry.Scheme.OverField.Curve

namespace AlgebraicGeometry.Scheme.OverField.Curve.Abel.BoundedFamily

open AlgebraicGeometry.Scheme.OverField.Curve

variable {k : Type u} [Field k] {X : FScheme k} [SmoothOfRelativeDimension 1 X.hom]
  [IsProper X.hom] (o : Spec (.of k) ⟶ X.left) (ho : o ≫ X.hom = 𝟙 _)
  (P : LocallyNoetherianOver (Spec (.of k)))
  (R : ((locallyNoetherianOverInclusion (Spec (.of k))).op ⋙ (fppfPicardSheaf X.hom).obj ⋙
    CategoryTheory.forget AddCommGrpCat.{u + 1}).RepresentableBy P)

/-- **The Abel morphism on rational points**: if the specialization of the graph-sum family at a
rational point `a` of `X^n` is the pullback of a class `L` on `X` to `X ×_k k`, then `a_n(a)` is
the rational point `picardPoint P R L`. -/
theorem parameterPoint_comp_abelMorphism_eq_picardPoint {n : ℕ}
    (a : Spec (.of k) ⟶ (parameter X.hom n).left) (ha : a ≫ (parameter X.hom n).hom = 𝟙 _)
    (L : PicardGroup X.left)
    (hL : pullbackClass (pullback.fst X.hom (𝟙 (Spec (.of k)))) L =
      pullbackClass (Hom.familyMap X.hom (parameter X.hom n).hom (𝟙 _) a ha)
        (classOf _ (lineBundle X.hom o ho n))) :
    (Over.homMk a ha : 𝟙_ (Over (Spec (.of k))) ⟶ parameter X.hom n) ≫
        (abelMorphism o ho P R n).hom = picardPoint P R L := by
  symm
  rw [picardPoint_eq_iff]
  have h := homEquiv_comp_abelMorphism o ho P R
    (ObjectProperty.homMk (Over.homMk a ha : 𝟙_ (Over (Spec (.of k))) ⟶ parameter X.hom n) :
      locallyNoetherianRationalPoint k ⟶ locallyNoetherianParameter X n)
  refine h.trans ?_
  rw [picardPointClass_apply]
  have h' : pullbackClass ((familyScheme X.hom).map (Over.homMk a ha :
      𝟙_ (Over (Spec (.of k))) ⟶ parameter X.hom n)) (classOf _ (lineBundle X.hom o ho n)) =
        pullbackClass (pullback.fst X.hom (𝟙 (Spec (.of k)))) L := by
    rw [familyScheme_map_eq_familyMap]
    exact hL.symm
  exact congrArg (fun x => ((quotientProjection X.hom ≫ toFppfPicardSheaf X.hom).app
    (op (𝟙_ (Over (Spec (.of k)))))) x) h'

end AlgebraicGeometry.Scheme.OverField.Curve.Abel.BoundedFamily
