/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.Fields.TwoFieldEffacement.FiniteSourceH1
public import Aglib.AlgebraicGeometry.EtaleCohomology.Fields.TwoFieldEffacement.FiniteSourceCommonField

/-! # Original finite-constant H1 effacement over two finite fields

The actual pointed source-closure producer supplies the zero. Its selected
finite source field, two-level point base and Galois cover are unchanged.
The original closure square then feeds mapped-compositum zero descent, giving
one finite extension of the coefficient field with both source-field triangles.
The proper smooth curve/open hypotheses are retained; this is not yet an
arbitrary smooth-affine curve or arbitrary-coefficient effacement theorem.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.PreGaloisCategory Opposite
open AlgebraicGeometry.Scheme.OverField

namespace AlgebraicGeometry.Scheme.EtaleCohomology.TwoFieldEffacement

universe u

attribute [local instance] hasSheafifyLarge HasExt.standard

open FiniteEtale FiniteEtale.FieldCoverDescent

section ClosureMaps

variable (k K : Type u) [Field k] [Field K] [Algebra k K]
  (X : FScheme k) {U : Scheme.{u}} (j : U ⟶ X.left)

/-- The actual closure comparison preserves the projection to the original open. -/
@[reassoc] theorem closureClassMap_original :
    closureClassMap k K X j ≫ pullback.fst (j ≫ X.hom) (Spec.algebraMap k K) =
      pullback.fst
        (Hom.fibreInclusion X.hom j (Spec.algebraMap k (AlgebraicClosure k)) ≫
          pullback.snd X.hom (Spec.algebraMap k (AlgebraicClosure k)))
        (Spec.map (CommRingCat.ofHom (Geometrically.commonClosureEmbedding k K).toRingHom)) ≫
      pullback.fst (j ≫ X.hom) (Spec.algebraMap k (AlgebraicClosure k)) := by
  simp only [closureClassMap, closureOpenIso, compatibleClosurePullbackIso,
    Iso.trans_hom, Category.assoc, doublePullbackIso_hom_original,
    pullback.congrHom_hom, pullback.map, pullback.lift_fst_assoc, Category.comp_id]

/-- The same comparison preserves the original coefficient-field structural map. -/
@[reassoc] theorem closureClassMap_field :
    closureClassMap k K X j ≫ pullback.snd (j ≫ X.hom) (Spec.algebraMap k K) =
      pullback.snd
        (Hom.fibreInclusion X.hom j (Spec.algebraMap k (AlgebraicClosure k)) ≫
          pullback.snd X.hom (Spec.algebraMap k (AlgebraicClosure k)))
        (Spec.map (CommRingCat.ofHom (Geometrically.commonClosureEmbedding k K).toRingHom)) ≫
      Spec.algebraMap K (AlgebraicClosure K) := by
  rw [closureClassMap, Category.assoc, pullback.condition]
  simp only [closureOpenIso, compatibleClosurePullbackIso, Iso.trans_hom,
    Category.assoc, doublePullbackIso_hom_field_assoc, pullback.congrHom_hom,
    pullback.map, pullback.lift_snd_assoc, Category.comp_id]

end ClosureMaps

/-- A genuine pointed source cover and a common finite coefficient field kill
the original H1 class. The returned base and cover are the unchanged selected
two-level point base and cover, not replacement models. -/
theorem exists_finite_pointed_H1_effacement
    (k K : Type u) [Field k] [Field K] [Algebra k K]
    (X : FScheme k) (hX : Curve.Properties X)
    {U : Scheme.{u}} (j : U ⟶ X.left) [IsOpenImmersion j]
    [CompactSpace U] [QuasiSeparatedSpace U] [GeometricallyConnected (j ≫ X.hom)]
    (x : Spec (.of k) ⟶ U) (hx : x ≫ (j ≫ X.hom) = 𝟙 _)
    (A : Type u) [AddCommGroup A] [Finite A]
    (n : ℕ) (hn : 0 < n) (hkill : ∀ a : A, n • a = 0) (hunit : IsUnit (n : k))
    (c : H1Etale (pullback (j ≫ X.hom) (Spec.algebraMap k K))
      (ConstantFinite.coefficient A _)) :
    ∃ (F : IntermediateField k (AlgebraicClosure k))
      (V : Scheme.{u}) (qV : V ⟶ Spec (.of F)) (aV : V ⟶ U)
      (H : IsPullback aV qV (j ≫ X.hom) (Spec.algebraMap k F)),
      letI : QuasiSeparatedSpace (pullback (j ≫ X.hom) (Spec.algebraMap k F) : Scheme.{u}) :=
        quasiSeparatedSpace_of_quasiSeparated (pullback.fst (j ≫ X.hom) (Spec.algebraMap k F))
      letI : ConnectedSpace (pullback (j ≫ X.hom) (Spec.algebraMap k F) : Scheme.{u}) :=
        GeometricallyConnected.connectedSpace_of_subsingleton
          (pullback.snd (j ≫ X.hom) (Spec.algebraMap k F))
      letI : CompactSpace V := H.isoPullback.inv.homeomorph.compactSpace
      letI : QuasiSeparatedSpace V :=
        (quasiSeparatedSpace_congr H.isoPullback.hom.homeomorph).mpr inferInstance
      letI : ConnectedSpace V :=
        H.isoPullback.hom.homeomorph.connectedSpace_iff.mpr inferInstance
      ∃ (Z : FiniteEtale V) (xF : Spec (.of F) ⟶ V) (zF : Spec (.of F) ⟶ Z.obj.left),
      Module.Finite k F ∧ xF ≫ qV = 𝟙 _ ∧
      xF ≫ aV = Spec.algebraMap k F ≫ x ∧ zF ≫ Z.obj.hom = xF ∧
      IsGalois Z ∧ Nat.card (Aut Z) ∣ n ^ Group.rank (Multiplicative A) ∧
      let e := Geometrically.commonClosureEmbedding k K
      let C := commonField k K (AlgebraicClosure k) (AlgebraicClosure K) F e
      let b := Spec.map (CommRingCat.ofHom
        (sourceCommonMap k K (AlgebraicClosure k) (AlgebraicClosure K) F e).toRingHom)
      let q := Z.obj.hom ≫ qV
      let a := Z.obj.hom ≫ aV
      let ha : a ≫ (j ≫ X.hom) = q ≫ Spec.algebraMap k F := by
        rw [Category.assoc, H.w, ← Category.assoc]
      ∃ t : Finset (AlgebraicClosure K),
        Module.Finite K (FieldLimit.finiteField C (AlgebraicClosure K) t) ∧
        ∃ i : F →+* FieldLimit.finiteField C (AlgebraicClosure K) t,
          (FieldLimit.finiteField C (AlgebraicClosure K) t).val.toRingHom.comp i =
            (e.comp F.val).toRingHom ∧
          i.comp (algebraMap k F) =
            (algebraMap K (FieldLimit.finiteField C (AlgebraicClosure K) t)).comp
              (algebraMap k K) ∧
          Curves.constantRestriction A
            (((FieldLimit.schemeDiagram C (AlgebraicClosure K) (pullback.snd q b)).obj
              (op t)).hom ≫ commonFieldClassMap k K (AlgebraicClosure k)
                (AlgebraicClosure K) F e (j ≫ X.hom) q a ha) 1 c = 0 := by
  have hsource := exists_finite_source_pointed_H1_effacement
    k K X hX j x hx A n hn hkill hunit c
  exact exists_common_finite_pointed_H1_effacement_of_source k K (j ≫ X.hom)
    (Hom.fibreInclusion X.hom j (Spec.algebraMap k (AlgebraicClosure k)) ≫
      pullback.snd X.hom (Spec.algebraMap k (AlgebraicClosure k)))
    (Hom.fibreInclusion_snd X.hom j (Spec.algebraMap k (AlgebraicClosure k)))
    (closureClassMap k K X j) (closureClassMap_original k K X j)
    (closureClassMap_field k K X j) x A n c hsource

end AlgebraicGeometry.Scheme.EtaleCohomology.TwoFieldEffacement
