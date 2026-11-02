/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.Fields.TwoFieldEffacement.AffineFiniteH1
public import
  Aglib.AlgebraicGeometry.EtaleCohomology.Fields.TwoFieldEffacement.GenericCoefficientPresentation
public import
  Aglib.AlgebraicGeometry.EtaleCohomology.Fields.TwoFieldEffacement.CommonFieldRingSeparableCover
public import
  Aglib.AlgebraicGeometry.EtaleCohomology.Fields.TwoFieldEffacement.CoefficientCompositeZero

/-! # Original generic H1 classes and the two-field pointed cover

The coefficient presentation and the affine constant-class effacement are
produced internally. The original source cover is descended through its actual
cartesian source, without replacing that cover by a second base-change model.
The conclusion is generic literal zero, not a target neighbourhood or property B.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits CategoryTheory.PreGaloisCategory Opposite
namespace AlgebraicGeometry.Scheme.EtaleCohomology.TwoFieldEffacement
universe u eX
attribute [local instance] hasSheafifyLarge HasExt.standard
open FiniteEtale

section Constant
variable (k K : Type u) [Field k] [Field K] [Algebra k K]
  {U : Scheme.{u}} [IsAffine U] (p : U ⟶ Spec (.of k))
  [SmoothOfRelativeDimension 1 p] [GeometricallyConnected p]

/-- The affine producer supplies the cover and its original zero; both finite
extensions are then refined to their actual separable subfields. -/
theorem exists_affine_separable_pointed_H1_effacement
    (x : Spec (.of k) ⟶ U) (hx : x ≫ p = 𝟙 _)
    (A : Type u) [AddCommGroup A] [Finite A]
    (n : ℕ) (hn : 0 < n) (hkill : ∀ z : A, n • z = 0) (hunit : IsUnit (n : k))
    (c : Sheaf.H.{u + 2} (ConstantFinite.coefficient A
      (pullback p (Spec.algebraMap k K))) 1) :
    ∃ (F : IntermediateField k (AlgebraicClosure k))
      (E : Type u) (_ : Field E) (_ : Algebra K E),
      letI : Algebra k E := ((algebraMap K E).comp (algebraMap k K)).toAlgebra
      letI : IsScalarTower k K E := IsScalarTower.of_algebraMap_eq' rfl
      letI : ConnectedSpace
          (pullback p (Spec.algebraMap k (separableClosure k F)) : Scheme.{u}) :=
        GeometricallyConnected.connectedSpace_of_subsingleton
          (pullback.snd p (Spec.algebraMap k (separableClosure k F)))
      Module.Finite k F ∧ Module.Finite K E ∧
      ∃ (jE : E →ₐ[K] AlgebraicClosure K) (a : F →ₐ[k] E),
        jE.toRingHom.comp a.toRingHom =
          ((Geometrically.commonClosureEmbedding k K).comp F.val).toRingHom ∧
        ∃ (Z : FiniteEtale (pullback p (Spec.algebraMap k (separableClosure k F)))),
          IsGalois Z ∧ Nat.card (Aut Z) ∣ n ^ Group.rank (Multiplicative A) ∧
          ∃ z : Spec (.of (separableClosure k F)) ⟶ Z.obj.left,
            z ≫ Z.obj.hom = separableSourcePoint k F p x hx ∧
            Curves.constantRestriction A
              (((FiniteEtale.baseChange (pullback.fst
                (pullback.snd p (Spec.algebraMap k (separableClosure k F)))
                (Spec.map (CommRingCat.ofHom
                  (separableSourceMap k F K E a).toRingHom)))).obj Z).obj.hom ≫
                  separableFieldClassMap k K p F E a) 1 c = 0 := by
  have hsource :=
    exists_affine_finite_pointed_H1_effacement k K U p x hx A n hn hkill hunit c
  obtain ⟨F, V, qV, aV, H, hsource⟩ := hsource
  let : QuasiSeparatedSpace (pullback p (Spec.algebraMap k F) : Scheme.{u}) :=
    quasiSeparatedSpace_of_quasiSeparated (pullback.fst p (Spec.algebraMap k F))
  let : ConnectedSpace (pullback p (Spec.algebraMap k F) : Scheme.{u}) :=
    GeometricallyConnected.connectedSpace_of_subsingleton (pullback.snd p (Spec.algebraMap k F))
  let : CompactSpace V := H.isoPullback.inv.homeomorph.compactSpace
  let : QuasiSeparatedSpace V :=
    (quasiSeparatedSpace_congr H.isoPullback.hom.homeomorph).mpr inferInstance
  let : ConnectedSpace V := H.isoPullback.hom.homeomorph.connectedSpace_iff.mpr inferInstance
  obtain ⟨Y, xF, zF, hF, hxFq, hxFa, hzF, hY, hcard, hfinite⟩ := hsource
  let : Module.Finite k F := hF
  let : IsGalois Y := hY
  obtain ⟨t, hE, i, hi₁, hi₂, hc⟩ := hfinite
  let emb := Geometrically.commonClosureEmbedding k K
  let C := commonField k K (AlgebraicClosure k) (AlgebraicClosure K) F emb
  let E := FieldLimit.finiteField C (AlgebraicClosure K) t
  let : Module.Finite K E := hE
  let : Algebra k E := ((algebraMap K E).comp (algebraMap k K)).toAlgebra
  let : IsScalarTower k K E := IsScalarTower.of_algebraMap_eq' rfl
  let aC := sourceCommonMap k K (AlgebraicClosure k) (AlgebraicClosure K) F emb
  have hz₁ : zF ≫ Y.obj.hom ≫ aV = Spec.algebraMap k F ≫ x :=
    (Category.assoc zF Y.obj.hom aV).symm.trans
      ((congrArg (fun z => z ≫ aV) hzF).trans hxFa)
  have hz₂ : zF ≫ Y.obj.hom ≫ qV = 𝟙 _ :=
    (Category.assoc zF Y.obj.hom qV).symm.trans
      ((congrArg (fun z => z ≫ qV) hzF).trans hxFq)
  have refineFields := exists_commonScalar_ring_separable_cover_and_zero
    k K p F C E aC (AlgebraicClosure K) E.val i hi₁ hi₂
  have refinePointed := refineFields x hx aV qV H Y zF hz₁ hz₂
  have refineClass := refinePointed A 1 (n ^ Group.rank (Multiplicative A)) hcard c
  have refined := refineClass hc
  obtain ⟨a, ha, hcover⟩ := refined
  have hambient : (E.val.restrictScalars K).toRingHom.comp a.toRingHom =
      ((Geometrically.commonClosureEmbedding k K).comp F.val).toRingHom :=
    (congrArg (fun m => (E.val.restrictScalars K).toRingHom.comp m) ha).trans hi₁
  exact ⟨F, E, inferInstance, inferInstance, hF, hE, E.val.restrictScalars K,
    a, hambient, hcover⟩

end Constant

section Generic
variable (B k K : Type u) [CommRing B] [Field k] [Field K]
  [Algebra B K] [Algebra k K]
  {Y U : Scheme.{u}} (e : Y ⟶ Spec (.of B)) [QuasiCompact e] [QuasiSeparated e]
  (p : U ⟶ Spec (.of k))

/-- The unique canonical comparison for the actual generic square and the
actual finite coefficient stage. No second coefficient sheaf is selected. -/
def genericCoefficientStageIso
    (aη : pullback e (Spec.algebraMap B K) ⟶ U)
    (Hη : IsPullback aη (pullback.snd e (Spec.algebraMap B K))
      p (Spec.algebraMap k K))
    (L : Type u) [Field L] [Algebra K L] [Algebra k L] [IsScalarTower k K L] :
    pullback (pullback.snd e (Spec.algebraMap B K)) (Spec.algebraMap K L) ≅
      pullback p (Spec.algebraMap k L) := by
  have ht : Spec.algebraMap K L ≫ Spec.algebraMap k K = Spec.algebraMap k L := by
    rw [← Spec.map_comp]
    exact congrArg Spec.map (CommRingCat.hom_ext
      (IsScalarTower.algebraMap_eq k K L).symm)
  have H := (IsPullback.of_hasPullback
    (pullback.snd e (Spec.algebraMap B K)) (Spec.algebraMap K L)).paste_horiz Hη
  rw [ht] at H
  exact H.isoPullback

/-- The single original generic H1 conclusion, shared by the actual family instance.
It asserts the produced cover and literal original class zero; it is not an input certificate. -/
def GenericPointedH1Effacement
    [GeometricallyConnected p]
    [HasExt.{eX} (AbelianSheaf.{u, u + 1} Y)]
    (x : Spec (.of k) ⟶ U) (hx : x ≫ p = 𝟙 _)
    (aη : pullback e (Spec.algebraMap B K) ⟶ U)
    (Hη : IsPullback aη (pullback.snd e (Spec.algebraMap B K)) p (Spec.algebraMap k K))
    (M : AbelianSheaf.{u, u + 1} (Spec (.of B))) (n : ℕ)
    (c : Sheaf.H.{eX} ((inverseImage e).obj M) 1) : Prop :=
    ∃ (L : FiniteGaloisIntermediateField K (SeparableClosure K))
      (C : Type u) (_ : AddCommGroup C) (_ : Finite C),
      letI : Algebra k L := ((algebraMap K L).comp (algebraMap k K)).toAlgebra
      letI : IsScalarTower k K L := IsScalarTower.of_algebraMap_eq' rfl
      (∀ z : C, n • z = 0) ∧
      ∃ (F : IntermediateField k (AlgebraicClosure k))
        (E : Type u) (_ : Field E) (_ : Algebra L E),
        letI : Algebra k E := ((algebraMap L E).comp (algebraMap k L)).toAlgebra
        letI : IsScalarTower k L E := IsScalarTower.of_algebraMap_eq' rfl
        letI : ConnectedSpace
            (pullback p (Spec.algebraMap k (separableClosure k F)) : Scheme.{u}) :=
          GeometricallyConnected.connectedSpace_of_subsingleton
            (pullback.snd p (Spec.algebraMap k (separableClosure k F)))
        Module.Finite k F ∧ Module.Finite L E ∧
        ∃ (jE : E →ₐ[L] AlgebraicClosure L) (a : F →ₐ[k] E),
          jE.toRingHom.comp a.toRingHom =
            ((Geometrically.commonClosureEmbedding k L).comp F.val).toRingHom ∧
          ∃ Z : FiniteEtale (pullback p (Spec.algebraMap k (separableClosure k F))),
            IsGalois Z ∧ Nat.card (Aut Z) ∣ n ^ Group.rank (Multiplicative C) ∧
            ∃ z : Spec (.of (separableClosure k F)) ⟶ Z.obj.left,
              z ≫ Z.obj.hom = separableSourcePoint k F p x hx ∧
              cohomologyPullback.{u, eX, u + 2}
                ((((FiniteEtale.baseChange (pullback.fst
                  (pullback.snd p (Spec.algebraMap k (separableClosure k F)))
                  (Spec.map (CommRingCat.ofHom
                    (separableSourceMap k F L E a).toRingHom)))).obj Z).obj.hom ≫
                    separableFieldClassMap k L p F E a ≫
                      (genericCoefficientStageIso B k K e p aη Hη L).inv) ≫
                        (pullback.fst (pullback.snd e (Spec.algebraMap B K))
                          (Spec.algebraMap K L) ≫ pullback.fst e (Spec.algebraMap B K)))
                ((inverseImage e).obj M) 1 c = 0

/-- A generic original class with coefficients from Spec B is killed by the
produced pointed source cover and the produced separable coefficient stage.
The original Ext world is independent; no generic zero or presentation is an
input. This does not assert zero on a neighbourhood of a nongeneric point. -/
theorem exists_generic_pointed_H1_effacement
    [IsAffine U] [SmoothOfRelativeDimension 1 p] [GeometricallyConnected p]
    [HasExt.{eX} (AbelianSheaf.{u, u + 1} Y)]
    (x : Spec (.of k) ⟶ U) (hx : x ≫ p = 𝟙 _)
    (aη : pullback e (Spec.algebraMap B K) ⟶ U)
    (Hη : IsPullback aη (pullback.snd e (Spec.algebraMap B K))
      p (Spec.algebraMap k K))
    (M : AbelianSheaf.{u, u + 1} (Spec (.of B)))
    (n : ℕ) (hn : 0 < n) (hM : n • 𝟙 M = 0) (hunit : IsUnit (n : k))
    (c : Sheaf.H.{eX} ((inverseImage e).obj M) 1) :
    GenericPointedH1Effacement B k K e p x hx aη Hη M n c := by
  obtain ⟨L, C, hC, hfin, hCn, d, β, hd⟩ :=
    exists_generic_finiteGalois_coefficient_presentation.{u, eX, u + 2, u + 2}
      B K e M n hn hM 1 c
  let := hC
  let := hfin
  let : Algebra k L := ((algebraMap K L).comp (algebraMap k K)).toAlgebra
  let : IsScalarTower k K L := IsScalarTower.of_algebraMap_eq' rfl
  let eStage := genericCoefficientStageIso B k K e p aη Hη L
  let dStage := Curves.constantRestriction C eStage.inv 1 d
  obtain ⟨F, E, hEF, hEA, hseparable⟩ :=
    exists_affine_separable_pointed_H1_effacement k L p x hx C n hn hCn hunit dStage
  let : Field E := hEF
  let : Algebra L E := hEA
  let : Algebra k E := ((algebraMap L E).comp (algebraMap k L)).toAlgebra
  let : IsScalarTower k L E := IsScalarTower.of_algebraMap_eq' rfl
  obtain ⟨hF, hE, jE, a, ha, Z, hZ, hcard, z, hz, hzero⟩ := hseparable
  let g₀ := pullback.fst (pullback.snd p (Spec.algebraMap k (separableClosure k F)))
    (Spec.map (CommRingCat.ofHom (separableSourceMap k F L E a).toRingHom))
  let r := ((FiniteEtale.baseChange g₀).obj Z).obj.hom ≫
    separableFieldClassMap k L p F E a
  let f := pullback.fst (pullback.snd e (Spec.algebraMap B K)) (Spec.algebraMap K L) ≫
    pullback.fst e (Spec.algebraMap B K)
  have hclass := cohomologyPullback_zero_of_constant_coefficient_stage
    r eStage.inv f ((inverseImage e).obj M) C 1 c d β hd hzero
  refine ⟨L, C, hC, hfin, hCn, F, E, hEF, hEA, hF, hE, jE, a, ha,
    Z, hZ, hcard, z, hz, ?_⟩
  exact Eq.mp (congrArg
    (fun m => cohomologyPullback.{u, eX, u + 2} m ((inverseImage e).obj M) 1 c = 0)
    (congrArg (fun m => m ≫ f)
      (Category.assoc ((FiniteEtale.baseChange g₀).obj Z).obj.hom
        (separableFieldClassMap k L p F E a) eStage.inv))) hclass

end Generic

section Family
variable (A B k K : Type u) [CommRing A] [CommRing B] [Field k] [Field K]
  [Algebra A B] [Algebra A k] [Algebra A K] [Algebra B K] [Algebra k K]
  [IsScalarTower A B K] [IsScalarTower A k K]
  {X : Scheme.{u}} (pX : X ⟶ Spec (.of A))
local notation "U" => pullback pX (Spec.algebraMap A k)
local notation "Y" => pullback pX (Spec.algebraMap A B)
local notation "p" => pullback.snd pX (Spec.algebraMap A k)
local notation "e" => pullback.snd pX (Spec.algebraMap A B)

/-- The actual two generic base changes of the original A-family commute. -/
def familyGenericMap : pullback e (Spec.algebraMap B K) ⟶ U :=
  pullback.lift
    (pullback.fst e (Spec.algebraMap B K) ≫ pullback.fst pX (Spec.algebraMap A B))
    (pullback.snd e (Spec.algebraMap B K) ≫ Spec.algebraMap k K) (by
      rw [Category.assoc, pullback.condition, ← Category.assoc, pullback.condition,
        Category.assoc, Category.assoc]
      congr 1
      rw [← Spec.map_comp, ← Spec.map_comp]
      exact congrArg Spec.map (CommRingCat.hom_ext
        ((IsScalarTower.algebraMap_eq A B K).symm.trans
          (IsScalarTower.algebraMap_eq A k K))))

/-- The family supplies the whole generic cartesian square; it is not a
class-zero or coefficient-presentation certificate. -/
theorem familyGenericSquare :
    IsPullback (familyGenericMap A B k K pX)
      (pullback.snd e (Spec.algebraMap B K)) p (Spec.algebraMap k K) := by
  have ht : Spec.algebraMap k K ≫ Spec.algebraMap A k =
      Spec.algebraMap B K ≫ Spec.algebraMap A B := by
    rw [← Spec.map_comp, ← Spec.map_comp]
    exact congrArg Spec.map (CommRingCat.hom_ext
      ((IsScalarTower.algebraMap_eq A k K).symm.trans
        (IsScalarTower.algebraMap_eq A B K)))
  apply IsPullback.of_right (h₁₂ := pullback.fst pX (Spec.algebraMap A k))
    (h₂₂ := Spec.algebraMap A k)
  · rw [show familyGenericMap A B k K pX ≫ pullback.fst pX (Spec.algebraMap A k) =
      pullback.fst e (Spec.algebraMap B K) ≫ pullback.fst pX (Spec.algebraMap A B) from
        pullback.lift_fst _ _ _, ht]
    exact (IsPullback.of_hasPullback e (Spec.algebraMap B K)).paste_horiz
      (IsPullback.of_hasPullback pX (Spec.algebraMap A B))
  · exact pullback.lift_snd _ _ _
  · exact IsPullback.of_hasPullback pX (Spec.algebraMap A k)

/-- The original A-family instance constructs its generic square internally.
Only the whole generic fibre is assumed affine, not the original family. -/
theorem exists_family_generic_pointed_H1_effacement
    [QuasiCompact pX] [QuasiSeparated pX] [SmoothOfRelativeDimension 1 pX]
    [GeometricallyConnected pX] [IsAffine U]
    [HasExt.{eX} (AbelianSheaf.{u, u + 1} Y)]
    (x : Spec (.of k) ⟶ U) (hx : x ≫ p = 𝟙 _)
    (M : AbelianSheaf.{u, u + 1} (Spec (.of B)))
    (n : ℕ) (hn : 0 < n) (hM : n • 𝟙 M = 0) (hunit : IsUnit (n : k))
    (c : Sheaf.H.{eX} ((inverseImage e).obj M) 1) :
    GenericPointedH1Effacement B k K e p x hx
      (familyGenericMap A B k K pX) (familyGenericSquare A B k K pX) M n c := by
  let : SmoothOfRelativeDimension 1 p :=
    (@MorphismProperty.IsStableUnderBaseChange.of_isPullback
      Scheme.{u} _ (@SmoothOfRelativeDimension 1)
      (smoothOfRelativeDimension_isStableUnderBaseChange 1))
      (IsPullback.of_hasPullback pX (Spec.algebraMap A k)) inferInstance
  exact exists_generic_pointed_H1_effacement B k K e p x hx
    (familyGenericMap A B k K pX) (familyGenericSquare A B k K pX)
    M n hn hM hunit c

end Family
end AlgebraicGeometry.Scheme.EtaleCohomology.TwoFieldEffacement
