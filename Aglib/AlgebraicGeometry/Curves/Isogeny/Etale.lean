/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Group.CurveIsogeny
public import Aglib.AlgebraicGeometry.FunctionField.GenericFiber
public import Aglib.AlgebraicGeometry.Group.ScalarExtension
public import Aglib.AlgebraicGeometry.Group.Translation
public import Aglib.AlgebraicGeometry.Morphisms.Etale.Locus
public import Mathlib.AlgebraicGeometry.AlgClosed.Basic
public import Mathlib.AlgebraicGeometry.Morphisms.LocalFlatDescent
public import Mathlib.FieldTheory.Perfect
public import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
public import Mathlib.RingTheory.Etale.Field

/-!
# Etale loci and translations of curve group homomorphisms

The function-field constructions and translations use the actual native scheme
maps. In characteristic zero the finite generic extension is separable. Its
etale neighborhood spreads by translations over an algebraic closure, and
faithfully flat descent proves etaleness of the original morphism. The final
adapter discharges the etaleness family of the existing pointed-isogeny consumer.

Target provenance: `R5Lab.AlgebraicGeometry.Curves.Isogenies.FieldFinite`,
revision `f8a3314ddecffcada2ec721d26d56a937bed9690`, declaration
`CharZeroFiniteCurveGroupHomEtale`. The original theorem family is a target,
not an assumed producer.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace
open MonoidalCategory CartesianMonoidalCategory MonObj
open scoped CategoryTheory.MonObj

universe u

namespace AlgebraicGeometry.Scheme

variable {X Y : Scheme.{u}} [IsIntegral X] [IsIntegral Y]

/-- The actual generic-field map of a finite dominant morphism is finite. -/
theorem functionFieldMap_finite (f : X ⟶ Y) [IsDominant f] [IsFinite f] :
    (functionFieldMap f).Finite := by
  let : IsIso (genericFibreMap f) := genericFibreMap_isIso f
  have h : IsFinite (Spec.map (CommRingCat.ofHom (functionFieldMap f))) := by
    rw [← show genericFibreMap f ≫ pullback.snd f (Y.fromSpecStalk (genericPoint Y)) =
      Spec.map (CommRingCat.ofHom (functionFieldMap f)) from pullback.lift_snd _ _ _]
    infer_instance
  exact (IsFinite.SpecMap_iff _).mp h

/-- Characteristic zero makes the finite extension on the actual generic fields
formally etale; no separability premise is supplied. -/
theorem functionFieldMap_formallyEtale_of_charZero
    (f : X ⟶ Y) [IsDominant f] [IsFinite f] [CharZero Y.functionField] :
    (functionFieldMap f).FormallyEtale := by
  let := (functionFieldMap f).toAlgebra
  let : Module.Finite Y.functionField X.functionField := functionFieldMap_finite f
  let : Algebra.IsSeparable Y.functionField X.functionField := inferInstance
  exact Algebra.FormallyEtale.of_isSeparable Y.functionField X.functionField

/-- The characteristic-zero generic-field argument applies to the actual
generic-point stalk map, with its literal source and target. -/
theorem stalkMap_genericPoint_formallyEtale_of_charZero
    (f : X ⟶ Y) [IsDominant f] [IsFinite f] [CharZero Y.functionField] :
    (f.stalkMap (genericPoint X)).hom.FormallyEtale := by
  let : IsIso (Y.presheaf.stalkSpecializes
      (specializes_of_eq (map_genericPoint_of_isDominant X f))) :=
    (Y.presheaf.stalkCongr
      (.of_eq (map_genericPoint_of_isDominant X f).symm)).isIso_hom
  exact (RingHom.FormallyEtale.respectsIso.cancel_left_isIso
    (Y.presheaf.stalkSpecializes
      (specializes_of_eq (map_genericPoint_of_isDominant X f)))
    (f.stalkMap (genericPoint X))).mp (functionFieldMap_formallyEtale_of_charZero f)

/-- A finite dominant morphism in characteristic zero is etale on a source
neighborhood of the actual generic point. -/
theorem exists_genericPoint_etale_neighborhood_of_charZero
    (f : X ⟶ Y) [IsDominant f] [IsFinite f] [LocallyOfFinitePresentation f]
    [CharZero Y.functionField] :
    ∃ W : X.Opens, genericPoint X ∈ W ∧ Etale (W.ι ≫ f) :=
  LocalRing.Etale.exists_etale_neighborhood_of_stalkMap_formallyEtale f (genericPoint X)
    (stalkMap_genericPoint_formallyEtale_of_charZero f)

end AlgebraicGeometry.Scheme

namespace AlgebraicGeometry.Scheme.Group.Translation

attribute [local instance] Over.cartesianMonoidalCategory

variable {S : Scheme.{u}} {G H : Grp (Over S)}

/-- Translation by the inverse point is the inverse of the actual translation. -/
def translationIso (a : 𝟙_ (Over S) ⟶ G.X) : G.X ≅ G.X where
  hom := translation a
  inv := translation a⁻¹
  hom_inv_id := by
    change translationHom (G := G) a⁻¹ * translationHom (G := G) a = 1
    rw [← map_mul, inv_mul_cancel, map_one]
  inv_hom_id := by
    change translationHom (G := G) a * translationHom (G := G) a⁻¹ = 1
    rw [← map_mul, mul_inv_cancel, map_one]

/-- A native group homomorphism commutes with the literal translations. -/
@[reassoc] theorem translation_comp_hom (f : G ⟶ H)
    (a : 𝟙_ (Over S) ⟶ G.X) :
    translation a ≫ f.hom.hom = f.hom.hom ≫ translation (a ≫ f.hom.hom) := by
  simp [translation, MonObj.mul_comp, MonObj.comp_mul]

end AlgebraicGeometry.Scheme.Group.Translation

namespace AlgebraicGeometry.Scheme.OverField.Curve

attribute [local instance] Over.cartesianMonoidalCategory

open AlgebraicGeometry.Scheme.OverField
open AlgebraicGeometry.Scheme.Group.Translation

/-- Over an algebraically closed field, translates of any nonempty etale
source open prove etaleness of the original group homomorphism. -/
theorem etale_of_nonempty_etale_open
    {k : Type u} [Field k] [IsAlgClosed k] (G H : Grp (FScheme k))
    [LocallyOfFiniteType G.X.hom] (f : G ⟶ H)
    (W : G.X.left.Opens) (hW : Nonempty W) [Etale (W.ι ≫ f.hom.hom.left)] :
    Etale f.hom.hom.left := by
  let : JacobsonSpace G.X.left := LocallyOfFiniteType.jacobsonSpace G.X.hom
  obtain ⟨p, hpW, hp⟩ := nonempty_inter_closedPoints
    (show (W : Set G.X.left).Nonempty from
      ⟨(Classical.choice hW).val, (Classical.choice hW).property⟩) W.isOpen.isLocallyClosed
  let c : 𝟙_ (FScheme k) ⟶ G.X :=
    Over.homMk (pointOfClosedPoint G.X.hom p hp) (pointOfClosedPoint_comp G.X.hom p hp)
  have hc : c.left (IsLocalRing.closedPoint k) = p := by
    exact pointOfClosedPoint_apply G.X.hom p hp _
  let t (a : 𝟙_ (FScheme k) ⟶ G.X) : W.toScheme ⟶ G.X.left :=
    W.ι ≫ (translation a).left
  have htIso (a : 𝟙_ (FScheme k) ⟶ G.X) : IsIso (translation a).left := by
    let : IsIso (translation a) := (translationIso a).isIso_hom
    exact (Over.forget (Base k)).map_isIso (translation a)
  have htOpen (a : 𝟙_ (FScheme k) ⟶ G.X) : IsOpenImmersion (t a) := by
    let := htIso a
    dsimp [t]
    infer_instance
  let U (a : 𝟙_ (FScheme k) ⟶ G.X) : G.X.left.Opens := (t a).opensRange
  have hEtale (a : 𝟙_ (FScheme k) ⟶ G.X) : Etale (t a ≫ f.hom.hom.left) := by
    have heq : t a ≫ f.hom.hom.left =
        (W.ι ≫ f.hom.hom.left) ≫ (translation (a ≫ f.hom.hom)).left := by
      dsimp [t]
      rw [Category.assoc, ← Over.comp_left, translation_comp_hom]
      rfl
    rw [heq]
    let : IsIso (translation (a ≫ f.hom.hom)).left := by
      let : IsIso (translation (a ≫ f.hom.hom)) :=
        (translationIso (a ≫ f.hom.hom)).isIso_hom
      exact (Over.forget (Base k)).map_isIso (translation (a ≫ f.hom.hom))
    infer_instance
  have hCover : iSup U = ⊤ := by
    apply top_le_iff.mp
    intro x _
    by_contra hx
    obtain ⟨q, hqU, hq⟩ := nonempty_inter_closedPoints
      (show ((iSup U : G.X.left.Opens) : Set G.X.left)ᶜ.Nonempty from ⟨x, hx⟩)
      (iSup U).isOpen.isClosed_compl.isLocallyClosed
    let b : 𝟙_ (FScheme k) ⟶ G.X :=
      Over.homMk (pointOfClosedPoint G.X.hom q hq) (pointOfClosedPoint_comp G.X.hom q hq)
    have hb : b.left (IsLocalRing.closedPoint k) = q :=
      pointOfClosedPoint_apply G.X.hom q hq _
    have htrans : c ≫ translation (b * c⁻¹) = b := by
      simp [comp_translation]
    have hq : q ∈ U (b * c⁻¹) := by
      refine ⟨⟨p, hpW⟩, ?_⟩
      have hpoint := congrArg
        (fun z : 𝟙_ (FScheme k) ⟶ G.X => z.left (IsLocalRing.closedPoint k)) htrans
      change (translation (b * c⁻¹)).left p = q
      simpa only [Over.comp_left, Scheme.Hom.comp_apply, hc, hb] using hpoint
    exact hqU (Opens.mem_iSup.mpr ⟨b * c⁻¹, hq⟩)
  apply IsZariskiLocalAtSource.of_iSup_eq_top (P := @Etale) U hCover
  intro a
  let := htOpen a
  let := hEtale a
  let e := IsOpenImmersion.isoOfRangeEq (t a) (U a).ι (by simp [U])
  apply (MorphismProperty.cancel_left_of_respectsIso @Etale e.hom
    ((U a).ι ≫ f.hom.hom.left)).mp
  rw [← Category.assoc, IsOpenImmersion.isoOfRangeEq_hom_fac]
  infer_instance

/-- A finite surjective homomorphism of actual smooth proper geometrically
connected curve groups over an algebraically closed characteristic-zero field
is etale. Generic separability and translations supply the conclusion. -/
theorem finite_hom_etale_of_isAlgClosed
    {k : Type u} [Field k] [CharZero k] [IsAlgClosed k] (G H : Grp (FScheme k))
    (hG : Properties G.X) (hH : Properties H.X) (f : G ⟶ H)
    [IsFinite f.hom.hom.left] [Surjective f.hom.hom.left] :
    Etale f.hom.hom.left := by
  let := hG.smooth
  let := hH.smooth
  let : Smooth G.X.hom := SmoothOfRelativeDimension.smooth 1 G.X.hom
  let : Smooth H.X.hom := SmoothOfRelativeDimension.smooth 1 H.X.hom
  let := hG.isIntegral
  let := hH.isIntegral
  let : IsLocallyNoetherian H.X.left := LocallyOfFiniteType.isLocallyNoetherian H.X.hom
  let : Algebra k H.X.left.functionField :=
    AlgebraicGeometry.Scheme.functionFieldConstantsAlgebra H.X.left H.X.hom
  let : CharZero H.X.left.functionField :=
    charZero_of_injective_algebraMap (algebraMap k H.X.left.functionField).injective
  obtain ⟨W, hW, he⟩ :=
    AlgebraicGeometry.Scheme.exists_genericPoint_etale_neighborhood_of_charZero f.hom.hom.left
  let := he
  exact etale_of_nonempty_etale_open G H f W ⟨⟨genericPoint G.X.left, hW⟩⟩

/-- Every finite surjective homomorphism between actual smooth proper
geometrically connected curve groups over a characteristic-zero field is etale.
The algebraic-closure argument descends to the original morphism by fpqc descent. -/
theorem finite_hom_etale_of_charZero
    {k : Type u} [Field k] [CharZero k] (G H : Grp (FScheme k))
    (hG : Properties G.X) (hH : Properties H.X) (f : G ⟶ H)
    [IsFinite f.hom.hom.left] [Surjective f.hom.hom.left] :
    Etale f.hom.hom.left := by
  let K := AlgebraicClosure k
  let s : Spec (.of K) ⟶ Base k := Spec.algebraMap k K
  let B := AlgebraicGeometry.Scheme.Group.BaseChange.groupSchemeBaseChange s
  let G' := B.functor.obj G
  let H' := B.functor.obj H
  let f' := B.functor.map f
  have hSquare : IsPullback (pullback.fst G.X.hom s) f'.hom.hom.left
      f.hom.hom.left (pullback.fst H.X.hom s) := by
    apply IsPullback.flip
    apply IsPullback.of_right (h₁₂ := pullback.snd H.X.hom s)
      (h₂₂ := H.X.hom) (v₁₃ := s)
      _ (AlgebraicGeometry.Scheme.Group.BaseChange.groupSchemeBaseChange_map_left_fst s f)
      (IsPullback.of_hasPullback H.X.hom s).flip
    simpa only [AlgebraicGeometry.Scheme.Group.BaseChange.groupSchemeBaseChange_map_left_snd,
      Over.w] using (IsPullback.of_hasPullback G.X.hom s).flip
  have hG' : Properties G'.X := by
    exact
      { smooth := MorphismProperty.pullback_snd G.X.hom s hG.smooth
        proper := MorphismProperty.pullback_snd G.X.hom s hG.proper
        connected := MorphismProperty.pullback_snd G.X.hom s hG.connected }
  have hH' : Properties H'.X := by
    exact
      { smooth := MorphismProperty.pullback_snd H.X.hom s hH.smooth
        proper := MorphismProperty.pullback_snd H.X.hom s hH.proper
        connected := MorphismProperty.pullback_snd H.X.hom s hH.connected }
  let : IsFinite f'.hom.hom.left :=
    MorphismProperty.of_isPullback hSquare (inferInstance : IsFinite f.hom.hom.left)
  let : Surjective f'.hom.hom.left :=
    MorphismProperty.of_isPullback hSquare (inferInstance : Surjective f.hom.hom.left)
  have he : Etale f'.hom.hom.left := finite_hom_etale_of_isAlgClosed G' H' hG' hH' f'
  let : Surjective s := ⟨Function.surjective_to_subsingleton s⟩
  exact MorphismProperty.of_isPullback_of_descendsAlong
    (P := @Etale) (Q := @Surjective ⊓ @Flat ⊓ @QuasiCompact) hSquare.flip
    ⟨⟨inferInstance, inferInstance⟩, inferInstance⟩ he

/-- The exact arbitrary-field theorem family required by the native conditional
pointed-isogeny consumer, proved for its original literal homomorphism. -/
theorem charZeroFiniteCurveGroupHomEtale :
    ∀ (k : Type u) [Field k] [CharZero k] (G H : Grp (FScheme k)),
      Properties G.X → Properties H.X →
      ∀ f : G ⟶ H, IsFinite f.hom.hom.left → Surjective f.hom.hom.left →
        Etale f.hom.hom.left := by
  intro k _ _ G H hG hH f hf hs
  let := hf
  let := hs
  exact finite_hom_etale_of_charZero G H hG hH f

/-- Native pointed rigidity and proper-curve finiteness now yield finite etale
surjectivity of the original dominant origin-preserving map in characteristic
zero, without a supplied etaleness theorem family. -/
theorem pointed_dominant_finite_etale_of_charZero
    {k : Type u} [Field k] [CharZero k] {C D : FScheme k}
    {c : 𝟙_ (FScheme k) ⟶ C} {d : 𝟙_ (FScheme k) ⟶ D}
    (LC : PointedGroupLaw C c) (LD : PointedGroupLaw D d)
    (hC : Properties C) (hD : Properties D)
    (m : C ⟶ D) [IsDominant m.left] (ho : c ≫ m = d) :
    letI : GrpObj C := LC.law
    letI : GrpObj D := LD.law
    IsMonHom m ∧ IsFinite m.left ∧ Etale m.left ∧ Surjective m.left :=
  pointed_dominant_finite_etale charZeroFiniteCurveGroupHomEtale LC LD hC hD m ho

end AlgebraicGeometry.Scheme.OverField.Curve
