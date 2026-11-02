/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import
  Aglib.AlgebraicGeometry.EtaleCohomology.Fields.TwoFieldEffacement.GenericH1ClassEffacement.Affine
public import
  Aglib.AlgebraicGeometry.EtaleCohomology.Fields.TwoFieldEffacement.GenericCoefficientPresentation
public import Aglib.AlgebraicGeometry.EtaleCohomology.Fields.TwoFieldEffacement.GenericCoefficientPresentationConsumer
public import
  Aglib.AlgebraicGeometry.EtaleCohomology.Fields.TwoFieldEffacement.CoefficientCompositeZero

/-! # Original generic pointed H1 effacement

The actual generic square identifies the produced finite coefficient stage.
Affine separable effacement and the original coefficient transport then kill
the original class, retaining its independent Ext world.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits CategoryTheory.PreGaloisCategory Opposite
namespace AlgebraicGeometry.Scheme.EtaleCohomology.TwoFieldEffacement
universe u eX
attribute [local instance] hasSheafifyLarge HasExt.standard
open FiniteEtale

/-- The whole original affine pointed-cover construction and coefficient-class
transport over specified scheme maps, before their generic-square specialization. -/
theorem exists_affine_pointed_H1_effacement_of_presentation
    (k L : Type u) [Field k] [Field L] [Algebra k L]
    {U T Y : Scheme.{u}} [IsAffine U]
    (p : U ⟶ Spec (.of k))
    [SmoothOfRelativeDimension 1 p] [GeometricallyConnected p]
    [HasExt.{eX} (AbelianSheaf.{u, u + 1} Y)]
    (x : Spec (.of k) ⟶ U) (hx : x ≫ p = 𝟙 _)
    (h : pullback p (Spec.algebraMap k L) ⟶ T) (f : T ⟶ Y)
    (M₀ : AbelianSheaf.{u, u + 1} Y)
    (C : Type u) [AddCommGroup C] [Finite C]
    (n : ℕ) (hn : 0 < n) (hCn : ∀ z : C, n • z = 0) (hunit : IsUnit (n : k))
    (c : Sheaf.H.{eX} M₀ 1)
    (d : Sheaf.H.{u + 2} (ConstantFinite.coefficient C T) 1)
    (β : ConstantFinite.coefficient C T ⟶ (inverseImage f).obj M₀)
    (hd : Sheaf.H.map.{u + 2} β 1 d =
      cohomologyPullback.{u, eX, u + 2} f M₀ 1 c) :
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
                    separableFieldClassMap k L p F E a ≫ h) ≫ f) M₀ 1 c = 0 := by
  let dStage := Curves.constantRestriction C h 1 d
  have hsource := exists_affine_separable_pointed_H1_effacement
    k L p x hx C n hn hCn hunit dStage
  obtain ⟨F, E, hEF, hEA, hseparable⟩ := hsource
  let : Field E := hEF
  let : Algebra L E := hEA
  let : Algebra k E := ((algebraMap L E).comp (algebraMap k L)).toAlgebra
  let : IsScalarTower k L E := IsScalarTower.of_algebraMap_eq' rfl
  obtain ⟨hF, hE, jE, a, ha, Z, hZ, hcard, z, hz, hzero⟩ := hseparable
  let g₀ := pullback.fst (pullback.snd p (Spec.algebraMap k (separableClosure k F)))
    (Spec.map (CommRingCat.ofHom (separableSourceMap k F L E a).toRingHom))
  let q := ((FiniteEtale.baseChange g₀).obj Z).obj.hom
  let s := separableFieldClassMap k L p F E a
  have hclass := cohomologyPullback_zero_of_constant_coefficient_stage.{u, eX}
    (q ≫ s) h f M₀ C 1 c d β hd hzero
  refine ⟨F, E, hEF, hEA, hF, hE, jE, a, ha, Z, hZ, hcard, z, hz, ?_⟩
  exact Eq.mp (congrArg
    (fun m => cohomologyPullback.{u, eX, u + 2} m M₀ 1 c = 0)
    (congrArg (fun m => m ≫ f) (Category.assoc q s h))) hclass

end AlgebraicGeometry.Scheme.EtaleCohomology.TwoFieldEffacement
