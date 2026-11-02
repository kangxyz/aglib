/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.Fields.TwoFieldEffacement.AffineFiniteSourceH1
public import Aglib.AlgebraicGeometry.EtaleCohomology.Fields.TwoFieldEffacement.FiniteSourceCommonField

/-! # Finite two-field H1 effacement on the whole affine source

The actual affine source producer supplies the marked cover and its zero.
The same common-field lower used by the original proper consumer supplies the
finite coefficient extension. No external zero or effacement certificate is
an input to this public theorem.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits CategoryTheory.PreGaloisCategory Opposite
namespace AlgebraicGeometry.Scheme.EtaleCohomology.TwoFieldEffacement
universe u
attribute [local instance] hasSheafifyLarge HasExt.standard
open FiniteEtale FiniteEtale.FieldCoverDescent

section ClosureMaps
variable (k K : Type u) [Field k] [Field K] [Algebra k K]
  {U : Scheme.{u}} (p : U ⟶ Spec (.of k))

@[reassoc] theorem affineClosureClassMap_original :
    affineClosureClassMap k K p ≫ pullback.fst p (Spec.algebraMap k K) =
      pullback.fst (pullback.snd p (Spec.algebraMap k (AlgebraicClosure k)))
        (Spec.map (CommRingCat.ofHom (Geometrically.commonClosureEmbedding k K).toRingHom)) ≫
      pullback.fst p (Spec.algebraMap k (AlgebraicClosure k)) := by
  simp only [affineClosureClassMap, compatibleClosurePullbackIso, Category.assoc,
    doublePullbackIso_hom_original]

@[reassoc] theorem affineClosureClassMap_field :
    affineClosureClassMap k K p ≫ pullback.snd p (Spec.algebraMap k K) =
      pullback.snd (pullback.snd p (Spec.algebraMap k (AlgebraicClosure k)))
        (Spec.map (CommRingCat.ofHom (Geometrically.commonClosureEmbedding k K).toRingHom)) ≫
      Spec.algebraMap K (AlgebraicClosure K) := by
  rw [affineClosureClassMap, Category.assoc, pullback.condition]
  simp only [compatibleClosurePullbackIso, doublePullbackIso_hom_field_assoc]
end ClosureMaps

/-- The original affine H1 class is killed by produced finite source and common
coefficient extensions, with the original whole cover, point and order bound. -/
theorem exists_affine_finite_pointed_H1_effacement
    (k K : Type u) [Field k] [Field K] [Algebra k K]
    (U : Scheme.{u}) [IsAffine U]
    (p : U ⟶ Spec (.of k)) [SmoothOfRelativeDimension 1 p] [GeometricallyConnected p]
    (x : Spec (.of k) ⟶ U) (hx : x ≫ p = 𝟙 _)
    (A : Type u) [AddCommGroup A] [Finite A]
    (n : ℕ) (hn : 0 < n) (hkill : ∀ a : A, n • a = 0) (hunit : IsUnit (n : k))
    (c : H1Etale (pullback p (Spec.algebraMap k K))
      (ConstantFinite.coefficient A _)) :
    ∃ (F : IntermediateField k (AlgebraicClosure k))
      (V : Scheme.{u}) (qV : V ⟶ Spec (.of F)) (aV : V ⟶ U)
      (H : IsPullback aV qV p (Spec.algebraMap k F)),
      letI : QuasiSeparatedSpace (pullback p (Spec.algebraMap k F) : Scheme.{u}) :=
        quasiSeparatedSpace_of_quasiSeparated (pullback.fst p (Spec.algebraMap k F))
      letI : ConnectedSpace (pullback p (Spec.algebraMap k F) : Scheme.{u}) :=
        GeometricallyConnected.connectedSpace_of_subsingleton
          (pullback.snd p (Spec.algebraMap k F))
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
      let ha : a ≫ p = q ≫ Spec.algebraMap k F := by
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
                (AlgebraicClosure K) F e p q a ha) 1 c = 0 := by
  have hsource := exists_affine_finite_source_pointed_H1_effacement
    k K U p x hx A n hn hkill hunit c
  exact exists_common_finite_pointed_H1_effacement_of_source k K p
    (pullback.snd p (Spec.algebraMap k (AlgebraicClosure k))) rfl
    (affineClosureClassMap k K p) (affineClosureClassMap_original k K p)
    (affineClosureClassMap_field k K p) x A n c hsource

end AlgebraicGeometry.Scheme.EtaleCohomology.TwoFieldEffacement
