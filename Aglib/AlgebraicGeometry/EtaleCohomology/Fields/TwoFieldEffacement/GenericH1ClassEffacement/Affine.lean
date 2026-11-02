/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import
  Aglib.AlgebraicGeometry.EtaleCohomology.Fields.TwoFieldEffacement.AffineFiniteH1
public import Aglib.AlgebraicGeometry.EtaleCohomology.Fields.TwoFieldEffacement.GenericH1ClassEffacement.Separable

/-! # Affine separable pointed H1 effacement

The affine finite-source producer and its actual common-field stage supply the
original pointed Galois cover. Its separable refinement retains the original
point, order bound and literal class-zero map.
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
  let emb := Geometrically.commonClosureEmbedding k K
  let C := commonField k K (AlgebraicClosure k) (AlgebraicClosure K) F emb
  let aC := sourceCommonMap k K (AlgebraicClosure k) (AlgebraicClosure K) F emb
  have hambient : (algebraMap C (AlgebraicClosure K)).comp aC.toRingHom =
      (emb.comp F.val).toRingHom :=
    congrArg (fun m : F →ₐ[k] AlgebraicClosure K => m.toRingHom)
      (IntermediateField.val_comp_mappedFiniteCompositumInclusion K F emb)
  have hz₁ : zF ≫ Y.obj.hom ≫ aV = Spec.algebraMap k F ≫ x :=
    (Category.assoc zF Y.obj.hom aV).symm.trans
      ((congrArg (fun z => z ≫ aV) hzF).trans hxFa)
  have hz₂ : zF ≫ Y.obj.hom ≫ qV = 𝟙 _ :=
    (Category.assoc zF Y.obj.hom qV).symm.trans
      ((congrArg (fun z => z ≫ qV) hzF).trans hxFq)
  have refineFields := exists_finiteStage_separable_pointed_effacement
    k K p F C (AlgebraicClosure K) aC (emb.comp F.val).toRingHom hambient
  have refinePointed := refineFields x hx aV qV H Y zF hz₁ hz₂
  have refineClass := refinePointed A 1 (n ^ Group.rank (Multiplicative A)) hcard c
  have refined := refineClass hfinite
  exact ⟨F, refined⟩

end Constant

end AlgebraicGeometry.Scheme.EtaleCohomology.TwoFieldEffacement
