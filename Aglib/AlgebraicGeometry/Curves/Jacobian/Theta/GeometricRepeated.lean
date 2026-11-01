/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Curves.Jacobian.Theta.UniversalFamily
public import Aglib.AlgebraicGeometry.Curves.Jacobian.Theta.RepeatedImage
public import Aglib.AlgebraicGeometry.Curves.Abel.RepeatedDivisor
public import Aglib.AlgebraicGeometry.Curves.Abel.BoundedFamily.PositiveParameters

/-!
# Repeated geometric divisors factor the original repeated Abel morphism

First prove composition of the original ordered parameter maps on every
test scheme. On an algebraically closed field test, decompose a repeated
effective divisor using its actual coefficients and recover its points as
the original graph sections. The whole positive-family classification into
the same supplied P/R then gives the actual repeated Abel factorization.

The field may be any extension of the ground field. No replacement Picard
representative over that field and no point-only classifying map is used.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits MonoidalCategory Opposite AlgebraicGeometry
open Scheme Scheme.Modules.Invertible Scheme.RelativePicard Scheme.Group
open scoped CategoryTheory.MonObj

universe u

namespace AlgebraicGeometry.Scheme.OverField.Curve.Abel.BoundedFamily

variable {k : Type u} [Field k] (X : FScheme k)

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- Duplicating the first coordinate commutes with every original tuple
lift, including those over nonreduced test schemes. -/
theorem parameterPoint_comp_repeatedParameter (n : ℕ) {T : Over (Spec (.of k))}
    (s : Fin (n + 1) → (T.left ⟶ X.left)) (hs : ∀ i, s i ≫ X.hom = T.hom) :
    (Over.homMk (parameterPoint X.hom T.hom s hs)
      (parameterPoint_over X.hom T.hom s hs) : T ⟶ parameter X.hom (n + 1)) ≫
        repeatedParameter X n =
      Over.homMk (parameterPoint X.hom T.hom (Fin.cases (s 0) s) (Fin.cases (hs 0) hs))
        (parameterPoint_over X.hom T.hom _ _) := by
  have hc (i : Fin (n + 2)) :
      (repeatedParameter X n).left ≫ coordinate X.hom (n + 2) i =
        Fin.cases (coordinate X.hom (n + 1) 0) (coordinate X.hom (n + 1)) i :=
    parameterPoint_coordinate X.hom (parameter X.hom (n + 1)).hom _ _ i
  apply finiteProductOver_hom_ext
  intro i
  apply Over.OverMorphism.ext
  change (parameterPoint X.hom T.hom s hs ≫ (repeatedParameter X n).left) ≫
      coordinate X.hom (n + 2) i =
    parameterPoint X.hom T.hom (Fin.cases (s 0) s) (Fin.cases (hs 0) hs) ≫
      coordinate X.hom (n + 2) i
  rw [Category.assoc, hc, parameterPoint_coordinate]
  refine Fin.cases ?_ (fun j => ?_) i
  · exact parameterPoint_coordinate X.hom T.hom s hs 0
  · exact parameterPoint_coordinate X.hom T.hom s hs j

end AlgebraicGeometry.Scheme.OverField.Curve.Abel.BoundedFamily

namespace AlgebraicGeometry.Scheme.OverField.Curve

open Abel.BoundedFamily Divisors Picard Picard.DivisorClass Picard.Degree

variable {k : Type u} [Field k] {X : FScheme k} (hX : Properties X)
  (o : Spec (.of k) ⟶ X.left) (ho : o ≫ X.hom = 𝟙 _)
  (P : LocallyNoetherianOver (Spec (.of k)))
  (R : ((locallyNoetherianOverInclusion (Spec (.of k))).op ⋙
    (fppfPicardSheaf X.hom).obj ⋙
      CategoryTheory.forget AddCommGrpCat.{u + 1}).RepresentableBy P)
  [LocallyOfFiniteType P.obj.hom]

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- If a geometric fibre class of the actual degree-(n+2) universal family
has a repeated effective representative, its ORIGINAL parameter map factors
through the ORIGINAL repeated Abel map in the same Jacobian. -/
theorem exists_comp_repeatedAbelMorphism_of_effective_divisor
    {K : Type u} [Field K] [IsAlgClosed K] (b : Spec (.of K) ⟶ Spec (.of k))
    (n : ℕ) (D : Divisor (pullback X.hom b)) (heff : ∀ x, 0 ≤ D x)
    (hdeg : degDiv (pullback X.hom b) (pullback.snd X.hom b) D = ((n + 2 : ℕ) : ℤ))
    (hrep : ∃ x, 2 ≤ D x) :
    letI := picardCommGrpObj X.hom P R
    let Y : FScheme K := Over.mk (pullback.snd X.hom b)
    let hY := curveProperties_baseChange hX K b
    letI := PointDivisor.isIntegral_of_properties Y hY
    letI := curveProperties_isNoetherian hY
    letI (x : ClosedPoint Y.left) := PointDivisor.isDiscreteValuationRing_stalk Y hY x
    ∀ (a : Over.mk b ⟶ identityComponentOver P.obj),
      classOf _ (RigidifiedPair.map a (degreeUniversalPair hX o ho P R (n + 2))).bundle =
        divisorToPicard Y.left hY.topologicalKrullDim_eq_one.le D →
      ∃ q : Over.mk b ⟶ parameter X.hom (n + 1),
        q ≫ repeatedAbelMorphism o ho hX P R n = a := by
  classical
  let := picardCommGrpObj X.hom P R
  let := hX.smooth
  let := hX.proper
  let Y : FScheme K := Over.mk (pullback.snd X.hom b)
  let hY := curveProperties_baseChange hX K b
  let := hY.proper
  let := PointDivisor.isIntegral_of_properties Y hY
  let := curveProperties_isNoetherian hY
  let (x : ClosedPoint Y.left) := PointDivisor.isDiscreteValuationRing_stalk Y hY x
  let hd := hY.topologicalKrullDim_eq_one.le
  change ∀ (a : Over.mk b ⟶ identityComponentOver P.obj),
    classOf (pullback X.hom b)
      (RigidifiedPair.map a (degreeUniversalPair hX o ho P R (n + 2))).bundle =
        divisorToPicard Y.left hd D →
      ∃ q : Over.mk b ⟶ parameter X.hom (n + 1),
        q ≫ repeatedAbelMorphism o ho hX P R n = a
  intro a hclass
  let T : LocallyNoetherianOver (Spec (.of k)) :=
    ⟨Over.mk b, inferInstanceAs (IsLocallyNoetherian (Spec (.of K)))⟩
  obtain ⟨s, hs⟩ := effective_divisor_eq_repeated_tuple Y.left Y.hom n D heff hdeg hrep
  let v : Fin (n + 1) → {q : Spec (.of K) ⟶ Y.left // q ≫ Y.hom = 𝟙 _} := fun i =>
    ⟨pointOfClosedPoint Y.hom (s i).val (s i).property,
      pointOfClosedPoint_comp Y.hom (s i).val (s i).property⟩
  let r : Fin (n + 1) → (Spec (.of K) ⟶ X.left) := fun i => (v i).val ≫ pullback.fst X.hom b
  have hr (i : Fin (n + 1)) : r i ≫ X.hom = b := by
    have hvi : (v i).val ≫ pullback.snd X.hom b = 𝟙 _ := (v i).property
    dsimp only [r]
    rw [Category.assoc, pullback.condition, ← Category.assoc, hvi, Category.id_comp]
  have hgraph (i : Fin (n + 1)) : Hom.graph X.hom b (r i) (hr i) = (v i).val := by
    apply pullback.hom_ext
    · exact Hom.graph_fst X.hom b (r i) (hr i)
    · exact (Hom.graph_snd X.hom b (r i) (hr i)).trans (v i).property.symm
  have hclosed (i : Fin (n + 1)) : PointDivisor.closedPoint Y
      (Hom.graph X.hom b (r i) (hr i)) (Hom.graph_snd X.hom b (r i) (hr i)) = s i := by
    apply Subtype.ext
    change Hom.graph X.hom b (r i) (hr i) (IsLocalRing.closedPoint K) = (s i).val
    rw [hgraph]
    exact pointOfClosedPoint_apply Y.hom (s i).val (s i).property _
  have hpoints (i : Fin (n + 1)) :
      divisorToPicard Y.left hd (PointDivisor.pointDivisor Y
        (Hom.graph X.hom b (r i) (hr i)) (Hom.graph_snd X.hom b (r i) (hr i)) 1) =
      divisorToPicard Y.left hd (Finsupp.single (s i) 1) :=
    congrArg (divisorToPicard Y.left hd)
      (congrArg (fun x : ClosedPoint Y.left => Finsupp.single x (1 : ℤ)) (hclosed i))
  let q : T.obj ⟶ parameter X.hom (n + 1) :=
    Over.homMk (parameterPoint X.hom b r hr) (parameterPoint_over X.hom b r hr)
  let q' := q ≫ repeatedParameter X n
  have hq' : q' = (Over.homMk
      (parameterPoint X.hom b (Fin.cases (r 0) r) (Fin.cases (hr 0) hr))
      (parameterPoint_over X.hom b _ _) : T.obj ⟶ parameter X.hom (n + 2)) :=
    parameterPoint_comp_repeatedParameter X n (T := T.obj) r hr
  let m : pullback X.hom b ⟶ pullback X.hom (parameter X.hom (n + 2)).hom :=
    (familyScheme X.hom).map q'
  let C : PicardGroup (pullback X.hom (parameter X.hom (n + 2)).hom) :=
    classOf _ (positiveFamilyLineBundle X.hom (n + 2))
  have hpositive : pullbackClass m C = divisorToPicard Y.left hd D := by
    let u : T.obj ⟶ parameter X.hom (n + 2) := Over.homMk
      (parameterPoint X.hom b (Fin.cases (r 0) r) (Fin.cases (hr 0) hr))
      (parameterPoint_over X.hom b _ _)
    have hm : m =
        Hom.familyMap X.hom (parameter X.hom (n + 2)).hom b u.left u.w :=
      (congrArg (fun a : T.obj ⟶ parameter X.hom (n + 2) => (familyScheme X.hom).map a)
        hq').trans (familyScheme_map_eq_familyMap X.hom u)
    refine (congrArg (fun m : pullback X.hom b ⟶
        pullback X.hom (parameter X.hom (n + 2)).hom =>
      pullbackClass m C) hm).trans ?_
    have hfield := positiveFamilyLineBundle_class_at_field_tuple
      (S := Spec (.of k)) (X := X.left) X.hom (K := K) b (n := n + 2)
      (Fin.cases (r 0) r) (Fin.cases (hr 0) hr) hY hd
    refine hfield.trans ?_
    rw [Fin.sum_univ_succ, hs, map_add, map_sum]
    simp only [Fin.cases_zero, Fin.cases_succ]
    exact congrArg₂ (fun c d : PicardGroup Y.left => c + d) (hpoints 0)
      (Finset.sum_congr rfl (fun i _ => hpoints i))
  have hpos := (homEquiv_comp_positiveAbelMorphism X P R
      (ObjectProperty.homMk q' : T ⟶ locallyNoetherianParameter X (n + 2))).trans
    (congrArg (fun c : PicardGroup Y.left =>
      (quotientProjection X.hom ≫ toFppfPicardSheaf X.hom).app (op T.obj) c) hpositive)
  have hQ := (degreeUniversalPair_classifies hX o ho P R (n + 2) (T := T) a).symm.trans
    (congrArg (fun c : PicardGroup Y.left =>
      (quotientProjection X.hom ≫ toFppfPicardSheaf X.hom).app (op T.obj) c) hclass)
  have hm : q' ≫ (positiveAbelMorphism X P R (n + 2)).hom =
      a ≫ identityComponentι P.obj ≫ (GrpObj.mulRight (picardPoint P R
        ((n + 2) • classOf X.left (PointDivisor.positiveLineBundle X hX o ho)))).hom :=
    congrArg InducedCategory.Hom.hom (R.homEquiv.injective (hpos.trans hQ.symm))
  have hnormal : q' ≫ (abelMorphism o ho P R (n + 2)).hom = a ≫ identityComponentι P.obj := by
    apply (cancel_mono (GrpObj.mulRight (picardPoint P R
      ((n + 2) • classOf X.left (PointDivisor.positiveLineBundle X hX o ho)))).hom).mp
    rw [positiveAbelMorphism_eq_based_comp_translation hX o ho P R (n + 2)] at hm
    simpa only [Category.assoc] using hm
  refine ⟨q, ?_⟩
  apply (cancel_mono (identityComponentι P.obj)).mp
  change (q ≫ (repeatedParameter X n ≫ jacobianAbelMorphism hX o ho P R (n + 2))) ≫
    identityComponentι P.obj = a ≫ identityComponentι P.obj
  rw [Category.assoc, Category.assoc, jacobianAbelMorphism_comp_inclusion]
  exact hnormal

end AlgebraicGeometry.Scheme.OverField.Curve
