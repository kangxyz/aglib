/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Group.MultiplicationCotangent
public import Aglib.AlgebraicGeometry.RationalPoint.Unramified

/-!
# Invertible multiplication and etaleness over arbitrary fields

The proved actual cotangent formula makes the identity stalk map unramified.
Its original fraction-field square passes this to the finite function-field
extension, which is then formally etale. No finite presentation or finiteness
of the localized identity stalk is assumed.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace
open MonoidalCategory CartesianMonoidalCategory MonObj
open scoped CategoryTheory.MonObj
open AlgebraicGeometry.Scheme.OverField

universe u


namespace AlgebraicGeometry.Scheme

/-- The original point-stalk pullback and original generic-field pullback
commute with the actual stalk-to-function-field localization maps. -/
theorem stalkMapAt_functionField_square {X Y : Scheme.{u}} [IsIntegral X] [IsIntegral Y]
    (f : X ⟶ Y) [IsDominant f] (x : X) (y : Y) (h : f x = y) :
    (algebraMap (X.presheaf.stalk x) X.functionField).comp (stalkMapAt f x y h).hom =
      (functionFieldMap f).comp (algebraMap (Y.presheaf.stalk y) Y.functionField) := by
  subst y
  rw [stalkMapAt_self]
  change (f.stalkMap x ≫ X.presheaf.stalkSpecializes (genericPoint_specializes x)).hom =
    (Y.presheaf.stalkSpecializes (genericPoint_specializes (f x)) ≫
      (Y.presheaf.stalkSpecializes (specializes_of_eq (map_genericPoint_of_isDominant X f)) ≫
        f.stalkMap (genericPoint X))).hom
  rw [← Category.assoc, TopCat.Presheaf.stalkSpecializes_comp]
  exact congrArg CommRingCat.Hom.hom
    (f.stalkSpecializes_stalkMap (genericPoint X) x (genericPoint_specializes x)).symm

/-- A finite dominant map with an unramified actual point-stalk map has a
formally etale actual generic-field map, in arbitrary characteristic. -/
theorem functionFieldMap_formallyEtale_of_unramified_stalk
    {X Y : Scheme.{u}} [IsIntegral X] [IsIntegral Y]
    (f : X ⟶ Y) [IsDominant f] [IsFinite f] (x : X) (y : Y) (h : f x = y)
    (hu : (stalkMapAt f x y h).hom.FormallyUnramified) :
    (functionFieldMap f).FormallyEtale :=
  RingHom.FormallyEtale.of_formallyUnramified_fraction_square
    (stalkMapAt f x y h).hom (algebraMap (Y.presheaf.stalk y) Y.functionField)
    (functionFieldMap f) (stalkMapAt_functionField_square f x y h) hu (functionFieldMap_finite f)

/-- Formal etaleness of the original generic-field map gives formal etaleness
of the literal generic-point stalk map, via its native point transport. -/
theorem stalkMap_genericPoint_formallyEtale_of_functionFieldMap
    {X Y : Scheme.{u}} [IsIntegral X] [IsIntegral Y] (f : X ⟶ Y) [IsDominant f]
    (hf : (functionFieldMap f).FormallyEtale) :
    (f.stalkMap (genericPoint X)).hom.FormallyEtale := by
  let : IsIso (Y.presheaf.stalkSpecializes
      (specializes_of_eq (map_genericPoint_of_isDominant X f))) :=
    (Y.presheaf.stalkCongr
      (.of_eq (map_genericPoint_of_isDominant X f).symm)).isIso_hom
  exact (RingHom.FormallyEtale.respectsIso.cancel_left_isIso
    (Y.presheaf.stalkSpecializes
      (specializes_of_eq (map_genericPoint_of_isDominant X f)))
    (f.stalkMap (genericPoint X))).mp hf

end AlgebraicGeometry.Scheme

namespace AlgebraicGeometry.Scheme.Group.Multiplication

attribute [local instance] Over.cartesianMonoidalCategory

variable {k : Type u} [Field k]

/-- The actual identity-stalk map of invertible multiplication is formally
unramified over every field, by the proved scalar cotangent formula. -/
theorem multiplicationLocalMap_formallyUnramified (G : Grp (FScheme k))
    (hG : Curve.Properties G.X) (n : ℕ) (hn : IsUnit (n : k)) :
    (multiplicationLocalMap G n).FormallyUnramified := by
  let : SmoothOfRelativeDimension 1 G.X.hom := hG.smooth
  let : Smooth G.X.hom := SmoothOfRelativeDimension.smooth 1 G.X.hom
  let : IsFinite ((𝟙 G.X) ^ n).left := (multiplication_finite_surjective_of_isUnit G hG n hn).1
  apply Cotangent.localMap_formallyUnramified_of_surjective η[G.X]
    ((𝟙 G.X) ^ n) (multiplication_pointed G n)
  change Function.Surjective (multiplicationCotangent G n)
  rw [multiplicationCotangent_eq_scalar G 1 n]
  intro a
  refine ⟨(n : k)⁻¹ • a, ?_⟩
  rw [LinearMap.smul_apply, LinearMap.id_apply, smul_smul, mul_inv_cancel₀ hn.ne_zero, one_smul]

/-- Invertible multiplication has a formally etale original generic-field
map. The argument uses no characteristic-zero or stalk finite-presentation premise. -/
theorem multiplication_functionFieldMap_formallyEtale (G : Grp (FScheme k))
    (hG : Curve.Properties G.X) (n : ℕ) (hn : IsUnit (n : k)) :
    letI := hG.isIntegral
    letI := (multiplication_finite_surjective_of_isUnit G hG n hn).2
    (functionFieldMap ((𝟙 G.X) ^ n).left).FormallyEtale := by
  let := hG.isIntegral
  let := (multiplication_finite_surjective_of_isUnit G hG n hn).1
  let := (multiplication_finite_surjective_of_isUnit G hG n hn).2
  exact functionFieldMap_formallyEtale_of_unramified_stalk ((𝟙 G.X) ^ n).left
    (Cotangent.pointData η[G.X]).point (Cotangent.pointData η[G.X]).point
    (Cotangent.point_eq _ _ _ (multiplication_pointed G n))
    (multiplicationLocalMap_formallyUnramified G hG n hn)

/-- Over an algebraically closed field of any characteristic, the actual
generic etale neighborhood spreads by translations to all of multiplication. -/
theorem multiplication_etale_of_isAlgClosed [IsAlgClosed k] (G : Grp (FScheme k))
    (hG : Curve.Properties G.X) (n : ℕ) (hn : IsUnit (n : k)) :
    Etale ((𝟙 G.X) ^ n).left := by
  let := hG.isIntegral
  let : SmoothOfRelativeDimension 1 G.X.hom := hG.smooth
  let : Smooth G.X.hom := SmoothOfRelativeDimension.smooth 1 G.X.hom
  let : IsLocallyNoetherian G.X.left := LocallyOfFiniteType.isLocallyNoetherian G.X.hom
  obtain ⟨hfinite, hsurj⟩ := multiplication_finite_surjective_of_isUnit G hG n hn
  let := hfinite
  let := hsurj
  let : IsMonHom ((𝟙 G.X) ^ n) :=
    Curve.pointedMorphism_of_curveProperties G G hG hG _ (multiplication_pointed G n)
  have hg := stalkMap_genericPoint_formallyEtale_of_functionFieldMap ((𝟙 G.X) ^ n).left
    (multiplication_functionFieldMap_formallyEtale G hG n hn)
  obtain ⟨W, hW, he⟩ :=
    LocalRing.Etale.exists_etale_neighborhood_of_stalkMap_formallyEtale
      ((𝟙 G.X) ^ n).left (genericPoint G.X.left) hg
  let : Etale (W.ι ≫ (Grp.ofHom ((𝟙 G.X) ^ n)).hom.hom.left) := he
  exact Curve.etale_of_nonempty_etale_open G G (Grp.ofHom ((𝟙 G.X) ^ n)) W
    ⟨⟨genericPoint G.X.left, hW⟩⟩

/-- Multiplication by an invertible natural scalar is etale over the original
arbitrary field. The literal algebraic-closure pullback is identified with the
same power map, then faithfully flat descent returns to the original map. -/
theorem multiplication_etale_of_isUnit (G : Grp (FScheme k))
    (hG : Curve.Properties G.X) (n : ℕ) (hn : IsUnit (n : k)) :
    Etale ((𝟙 G.X) ^ n).left := by
  let : IsMonHom ((𝟙 G.X) ^ n) :=
    Curve.pointedMorphism_of_curveProperties G G hG hG _ (multiplication_pointed G n)
  let f : G ⟶ G := Grp.ofHom ((𝟙 G.X) ^ n)
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
  have hpow : f'.hom.hom = (𝟙 G'.X) ^ n := by
    change P.map ((𝟙 G.X) ^ n) = (𝟙 (P.obj G.X)) ^ n
    calc
      _ = (P.map (𝟙 G.X)) ^ n :=
        (P.homMonoidHom (X := G.X) (M := G.X)).map_pow _ _
      _ = _ := by rw [CategoryTheory.Functor.map_id]
  have hn' : IsUnit (n : K) := by
    simpa only [map_natCast] using hn.map (algebraMap k K)
  have he : Etale f'.hom.hom.left := by
    rw [hpow]
    exact multiplication_etale_of_isAlgClosed G' hG' n hn'
  let : Surjective s := ⟨Function.surjective_to_subsingleton s⟩
  exact MorphismProperty.of_isPullback_of_descendsAlong
    (P := @Etale) (Q := @Surjective ⊓ @Flat ⊓ @QuasiCompact) hSquare.flip
    ⟨⟨inferInstance, inferInstance⟩, inferInstance⟩ he

/-- The original multiplication morphism is finite, etale and surjective for
every invertible natural level, over an arbitrary field. -/
theorem multiplication_finite_etale_of_invertible (G : Grp (FScheme k))
    (hG : Curve.Properties G.X) (n : ℕ) (hn : IsUnit (n : k)) :
    IsFinite ((𝟙 G.X) ^ n).left ∧ Etale ((𝟙 G.X) ^ n).left ∧
      Surjective ((𝟙 G.X) ^ n).left :=
  ⟨(multiplication_finite_surjective_of_isUnit G hG n hn).1,
    multiplication_etale_of_isUnit G hG n hn,
    (multiplication_finite_surjective_of_isUnit G hG n hn).2⟩

/-- The all-characteristic finite-etale conclusion retains the exact original
group law and literal multiplication specified by `PointedGroupLaw C c`. -/
theorem pointedGroupLaw_multiplication_finite_etale_of_invertible
    {C : FScheme k} {c : 𝟙_ (FScheme k) ⟶ C} (L : PointedGroupLaw C c)
    (hC : Curve.Properties C) (n : ℕ) (hn : IsUnit (n : k)) :
    letI : GrpObj C := L.law
    IsFinite ((𝟙 C) ^ n).left ∧ Etale ((𝟙 C) ^ n).left ∧
      Surjective ((𝟙 C) ^ n).left := by
  let : GrpObj C := L.law
  exact multiplication_finite_etale_of_invertible { X := C, grp := L.law } hC n hn

end AlgebraicGeometry.Scheme.Group.Multiplication
