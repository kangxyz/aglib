/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import
  Aglib.AlgebraicGeometry.EtaleCohomology.Fields.TwoFieldEffacement.CommonFieldRingSeparableCover

/-! # Complete separable refinement of the original finite field stage

The entire finite-stage existential is consumed over variable common and ambient
fields. Its original ring map, pointed cover and zero supply the complete
separable result before the common-field construction is specialized.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits CategoryTheory.PreGaloisCategory Opposite
namespace AlgebraicGeometry.Scheme.EtaleCohomology.TwoFieldEffacement
universe u
attribute [local instance] hasSheafifyLarge HasExt.standard
open FiniteEtale

variable (k K : Type u) [Field k] [Field K] [Algebra k K]
  {U : Scheme.{u}} (p : U ⟶ Spec (.of k))
  (F C Ω : Type u) [Field F] [Field C] [Field Ω]
  [Algebra k F] [Module.Finite k F]
  [Algebra k C] [Algebra K C] [IsScalarTower k K C]
  [Algebra C Ω] [Algebra K Ω] [IsScalarTower K C Ω]
  (aC : F →ₐ[k] C) (iF : F →+* Ω)
  [CompactSpace U] [QuasiSeparatedSpace U] [GeometricallyConnected p]

/-- Refine the same finite-stage ring map and package its full pointed-cover
conclusion before inserting the native common and algebraic-closure fields. -/
theorem exists_finiteStage_separable_pointed_effacement
    (hambient : (algebraMap C Ω).comp aC.toRingHom = iF)
    (x : Spec (.of k) ⟶ U) (hx : x ≫ p = 𝟙 _)
    {V : Scheme.{u}} [ConnectedSpace V]
    (aV : V ⟶ U) (qV : V ⟶ Spec (.of F))
    (H : IsPullback aV qV p (Spec.algebraMap k F))
    (Y : FiniteEtale V) [IsGalois Y]
    (zF : Spec (.of F) ⟶ Y.obj.left)
    (hz₁ : zF ≫ Y.obj.hom ≫ aV = Spec.algebraMap k F ≫ x)
    (hz₂ : zF ≫ Y.obj.hom ≫ qV = 𝟙 _)
    (A : Type u) [AddCommGroup A] [Finite A] (degree n : ℕ)
    (hcard : Nat.card (Aut Y) ∣ n)
    (ξ : Sheaf.H.{u + 2} (ConstantFinite.coefficient A
      (pullback p (Spec.algebraMap k K))) degree)
    (hfinite :
      let q := Y.obj.hom ≫ qV
      let a := Y.obj.hom ≫ aV
      let ha : a ≫ p = q ≫ Spec.algebraMap k F :=
        (Category.assoc Y.obj.hom aV p).trans
          ((congrArg (fun z => Y.obj.hom ≫ z) H.w).trans
            (Category.assoc Y.obj.hom qV (Spec.algebraMap k F)).symm)
      let bC := Spec.map (CommRingCat.ofHom aC.toRingHom)
      ∃ t : Finset Ω,
        Module.Finite K (FieldLimit.finiteField C Ω t) ∧
        ∃ i : F →+* FieldLimit.finiteField C Ω t,
          (FieldLimit.finiteField C Ω t).val.toRingHom.comp i = iF ∧
          i.comp (algebraMap k F) =
            (algebraMap K (FieldLimit.finiteField C Ω t)).comp (algebraMap k K) ∧
          Curves.constantRestriction A
            (((FieldLimit.schemeDiagram C Ω (pullback.snd q bC)).obj (op t)).hom ≫
              scalarClassMap p q a (Spec.algebraMap k F) ha bC
                (Spec.algebraMap K C) (Spec.algebraMap k K)
                (commonScalarSquare k K F C aC)) degree ξ = 0) :
    ∃ (E : Type u) (_ : Field E) (_ : Algebra K E),
      letI : Algebra k E := ((algebraMap K E).comp (algebraMap k K)).toAlgebra
      letI : IsScalarTower k K E := IsScalarTower.of_algebraMap_eq' rfl
      letI : ConnectedSpace
          (pullback p (Spec.algebraMap k (separableClosure k F)) : Scheme.{u}) :=
        GeometricallyConnected.connectedSpace_of_subsingleton
          (pullback.snd p (Spec.algebraMap k (separableClosure k F)))
      Module.Finite k F ∧ Module.Finite K E ∧
      ∃ (jE : E →ₐ[K] Ω) (a : F →ₐ[k] E),
        jE.toRingHom.comp a.toRingHom = iF ∧
        ∃ Z : FiniteEtale (pullback p (Spec.algebraMap k (separableClosure k F))),
          IsGalois Z ∧ Nat.card (Aut Z) ∣ n ∧
          ∃ z : Spec (.of (separableClosure k F)) ⟶ Z.obj.left,
            z ≫ Z.obj.hom = separableSourcePoint k F p x hx ∧
            Curves.constantRestriction A
              (((FiniteEtale.baseChange (pullback.fst
                (pullback.snd p (Spec.algebraMap k (separableClosure k F)))
                (Spec.map (CommRingCat.ofHom
                  (separableSourceMap k F K E a).toRingHom)))).obj Z).obj.hom ≫
                    separableFieldClassMap k K p F E a) degree ξ = 0 := by
  obtain ⟨t, hE, i, hi₁, hi₂, hc⟩ := hfinite
  let E := FieldLimit.finiteField C Ω t
  let : Module.Finite K E := hE
  let : Algebra k E := ((algebraMap K E).comp (algebraMap k K)).toAlgebra
  let : IsScalarTower k K E := IsScalarTower.of_algebraMap_eq' rfl
  have refineFields := exists_commonScalar_ring_separable_cover_and_zero
    k K p F C E aC Ω E.val i (hi₁.trans hambient.symm) hi₂
  have refinePointed := refineFields x hx aV qV H Y zF hz₁ hz₂
  have refineClass := refinePointed A degree n hcard ξ
  have refined := refineClass hc
  obtain ⟨a, ha, hcover⟩ := refined
  have hambientE : (E.val.restrictScalars K).toRingHom.comp a.toRingHom = iF :=
    (congrArg (fun m => (E.val.restrictScalars K).toRingHom.comp m) ha).trans hi₁
  exact ⟨E, inferInstance, inferInstance, inferInstance, hE,
    E.val.restrictScalars K, a, hambientE, hcover⟩

end AlgebraicGeometry.Scheme.EtaleCohomology.TwoFieldEffacement
