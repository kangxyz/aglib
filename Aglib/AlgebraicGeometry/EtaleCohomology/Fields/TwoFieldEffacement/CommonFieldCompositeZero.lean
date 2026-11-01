/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.Fields.TwoFieldEffacement.CompositeZero
public import Aglib.FieldTheory.IntermediateField.MappedFiniteCompositum

/-! # Original composite zero over one common finite coefficient field

The unchanged finite source field maps into the native mapped compositum with
the original coefficient field. The actual scalar pullback of the original
source scheme has its canonical map to the original target pullback. An actual
closure reconstruction and its original zero descend to one further finite
field. This is a zero-descent bridge; the curve producer supplies its zero.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.Scheme.EtaleCohomology.TwoFieldEffacement

universe u

attribute [local instance] hasSheafifyLarge HasExt.standard

/-- The actual map from a source scalar pullback to the original target scalar
pullback, constructed from the original scheme and field-square equations. -/
def scalarClassMap {U S P F C K : Scheme.{u}}
    (p : U ⟶ S) (q : P ⟶ F) (a : P ⟶ U) (b : F ⟶ S)
    (ha : a ≫ p = q ≫ b) (c : C ⟶ F) (d : C ⟶ K) (k : K ⟶ S)
    (hcd : c ≫ b = d ≫ k) : pullback q c ⟶ pullback p k :=
  pullback.lift (pullback.fst q c ≫ a) (pullback.snd q c ≫ d) (by
    rw [Category.assoc, ha, ← Category.assoc, pullback.condition,
      Category.assoc, hcd, ← Category.assoc])

@[reassoc] theorem scalarClassMap_fst {U S P F C K : Scheme.{u}}
    (p : U ⟶ S) (q : P ⟶ F) (a : P ⟶ U) (b : F ⟶ S)
    (ha : a ≫ p = q ≫ b) (c : C ⟶ F) (d : C ⟶ K) (k : K ⟶ S)
    (hcd : c ≫ b = d ≫ k) :
    scalarClassMap p q a b ha c d k hcd ≫ pullback.fst p k =
      pullback.fst q c ≫ a := pullback.lift_fst _ _ _

@[reassoc] theorem scalarClassMap_snd {U S P F C K : Scheme.{u}}
    (p : U ⟶ S) (q : P ⟶ F) (a : P ⟶ U) (b : F ⟶ S)
    (ha : a ≫ p = q ≫ b) (c : C ⟶ F) (d : C ⟶ K) (k : K ⟶ S)
    (hcd : c ≫ b = d ≫ k) :
    scalarClassMap p q a b ha c d k hcd ≫ pullback.snd p k =
      pullback.snd q c ≫ d := pullback.lift_snd _ _ _

section Fields

variable (k K Ω₀ Ω : Type u) [Field k] [Field K] [Field Ω₀] [Field Ω]
  [Algebra k K] [Algebra k Ω₀] [Algebra k Ω] [Algebra K Ω] [IsScalarTower k K Ω]
  (F : IntermediateField k Ω₀) (e : Ω₀ →ₐ[k] Ω)

/-- The native common field; the source field itself is not replaced by its image. -/
abbrev commonField := IntermediateField.adjoin K ((F.map e : IntermediateField k Ω) : Set Ω)

/-- The original source-field inclusion into that same native compositum. -/
abbrev sourceCommonMap : F →ₐ[k] commonField k K Ω₀ Ω F e :=
  IntermediateField.mappedFiniteCompositumInclusion K F e

/-- The actual source and coefficient maps to the base field agree. -/
theorem commonField_spec_square :
    Spec.map (CommRingCat.ofHom (sourceCommonMap k K Ω₀ Ω F e).toRingHom) ≫ Spec.algebraMap k F =
      Spec.algebraMap K (commonField k K Ω₀ Ω F e) ≫ Spec.algebraMap k K := by
  rw [← Spec.map_comp, ← Spec.map_comp]
  congr 1
  apply CommRingCat.hom_ext
  apply RingHom.ext
  intro x
  exact ((sourceCommonMap k K Ω₀ Ω F e).commutes x).trans
    (IsScalarTower.algebraMap_apply k K (commonField k K Ω₀ Ω F e) x)

/-- The full original source-to-ambient triangle through the common field. -/
theorem commonField_ambient_square :
    Spec.algebraMap (commonField k K Ω₀ Ω F e) Ω ≫
        Spec.map (CommRingCat.ofHom (sourceCommonMap k K Ω₀ Ω F e).toRingHom) =
      Spec.map (CommRingCat.ofHom (e.comp F.val).toRingHom) := by
  rw [← Spec.map_comp]
  congr 1

/-- The literal coefficient map over the actual common scalar pullback. -/
def commonFieldClassMap {U P : Scheme.{u}}
    (p : U ⟶ Spec (.of k)) (q : P ⟶ Spec (.of F)) (a : P ⟶ U)
    (ha : a ≫ p = q ≫ Spec.algebraMap k F) :
    pullback q (Spec.map (CommRingCat.ofHom (sourceCommonMap k K Ω₀ Ω F e).toRingHom)) ⟶
      pullback p (Spec.algebraMap k K) :=
  scalarClassMap p q a (Spec.algebraMap k F) ha
    (Spec.map (CommRingCat.ofHom (sourceCommonMap k K Ω₀ Ω F e).toRingHom))
    (Spec.algebraMap K (commonField k K Ω₀ Ω F e)) (Spec.algebraMap k K)
    (commonField_spec_square k K Ω₀ Ω F e)

/-- A supplied original closure zero descends on the unchanged source scheme
through the actual common field to one finite coefficient field. Both the
original source inclusion and its ambient-field equation are retained. -/
theorem exists_common_finiteField_composite_zero
    [Module.Finite k F] [Algebra.IsAlgebraic K Ω]
    {U P W : Scheme.{u}} [CompactSpace P] [QuasiSeparatedSpace P]
    (p : U ⟶ Spec (.of k)) (q : P ⟶ Spec (.of F)) (a : P ⟶ U)
    (ha : a ≫ p = q ≫ Spec.algebraMap k F)
    (r : W ⟶ P) (s : W ⟶ Spec (.of Ω))
    (H : IsPullback r s q (Spec.map (CommRingCat.ofHom (e.comp F.val).toRingHom)))
    (h : W ⟶ pullback p (Spec.algebraMap k K))
    (hfst : h ≫ pullback.fst p (Spec.algebraMap k K) = r ≫ a)
    (hsnd : h ≫ pullback.snd p (Spec.algebraMap k K) = s ≫ Spec.algebraMap K Ω)
    (A : Type u) [AddCommGroup A] (degree : ℕ)
    (c : Sheaf.H.{u + 2} (ConstantFinite.coefficient A
      (pullback p (Spec.algebraMap k K))) degree)
    (hc : Curves.constantRestriction A h degree c = 0) :
    let C := commonField k K Ω₀ Ω F e
    let b := Spec.map (CommRingCat.ofHom (sourceCommonMap k K Ω₀ Ω F e).toRingHom)
    let pC := pullback.snd q b
    ∃ t : Finset Ω,
      Module.Finite K (FiniteEtale.FieldLimit.finiteField C Ω t) ∧
      ∃ i : F →+* FiniteEtale.FieldLimit.finiteField C Ω t,
        (FiniteEtale.FieldLimit.finiteField C Ω t).val.toRingHom.comp i =
          (e.comp F.val).toRingHom ∧
        i.comp (algebraMap k F) =
          (algebraMap K (FiniteEtale.FieldLimit.finiteField C Ω t)).comp (algebraMap k K) ∧
        Curves.constantRestriction A
          (((FiniteEtale.FieldLimit.schemeDiagram C Ω pC).obj (op t)).hom ≫
            commonFieldClassMap k K Ω₀ Ω F e p q a ha) degree c = 0 := by
  let C := commonField k K Ω₀ Ω F e
  let b := Spec.map (CommRingCat.ofHom (sourceCommonMap k K Ω₀ Ω F e).toRingHom)
  let PC := pullback q b
  let pC : PC ⟶ Spec (.of C) := pullback.snd q b
  let hC := commonFieldClassMap k K Ω₀ Ω F e p q a ha
  have hb : Spec.algebraMap C Ω ≫ b = Spec.map (CommRingCat.ofHom (e.comp F.val).toRingHom) :=
    commonField_ambient_square k K Ω₀ Ω F e
  let rC : W ⟶ PC := pullback.lift r (s ≫ Spec.algebraMap C Ω) (by
    rw [Category.assoc, hb]
    exact H.w)
  have HC : IsPullback rC s pC (Spec.algebraMap C Ω) := by
    apply IsPullback.of_right (h₁₂ := pullback.fst q b) (h₂₂ := b)
    · rw [show rC ≫ pullback.fst q b = r from pullback.lift_fst _ _ _, hb]
      exact H
    · exact pullback.lift_snd _ _ _
    · exact IsPullback.of_hasPullback _ _
  have hCf : hC ≫ pullback.fst p (Spec.algebraMap k K) = pullback.fst q b ≫ a :=
    pullback.lift_fst _ _ _
  have hCs : hC ≫ pullback.snd p (Spec.algebraMap k K) =
      pullback.snd q b ≫ Spec.algebraMap K C := pullback.lift_snd _ _ _
  have hrC : rC ≫ hC = h := by
    apply pullback.hom_ext
    · rw [Category.assoc, hCf, ← Category.assoc,
        show rC ≫ pullback.fst q b = r from pullback.lift_fst _ _ _, hfst]
    · rw [Category.assoc, hCs, ← Category.assoc,
        show rC ≫ pullback.snd q b = s ≫ Spec.algebraMap C Ω from pullback.lift_snd _ _ _,
        Category.assoc, hsnd]
      congr 1
      rw [← Spec.map_comp]
      congr 1
  have hzero : Curves.constantRestriction A
      (pullback.fst pC (Spec.algebraMap C Ω) ≫ hC) degree c = 0 := by
    rw [← HC.isoPullback_inv_fst, Category.assoc, hrC,
      Curves.constantRestriction_comp, hc, map_zero]
  let : Module.Finite K C := IntermediateField.finite_mapped_adjoin K F e
  let : QuasiSeparatedSpace PC := quasiSeparatedSpace_of_quasiSeparated (pullback.fst q b)
  obtain ⟨t, ht⟩ := exists_finiteField_composite_zero C Ω pC hC A degree c hzero
  let L := FiniteEtale.FieldLimit.finiteField C Ω t
  let i : F →+* L :=
    (algebraMap C L).comp (sourceCommonMap k K Ω₀ Ω F e).toRingHom
  refine ⟨t, Module.Finite.trans C L, i, ?_, ?_, ht⟩
  · exact congrArg AlgHom.toRingHom
      (IntermediateField.val_comp_mappedFiniteCompositumInclusion K F e)
  · apply RingHom.ext
    intro x
    change algebraMap C L ((sourceCommonMap k K Ω₀ Ω F e) (algebraMap k F x)) = _
    rw [(sourceCommonMap k K Ω₀ Ω F e).commutes,
      IsScalarTower.algebraMap_apply k K C]
    exact (IsScalarTower.algebraMap_apply K C L (algebraMap k K x)).symm

end Fields

end AlgebraicGeometry.Scheme.EtaleCohomology.TwoFieldEffacement
