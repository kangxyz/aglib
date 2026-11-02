/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.Fields.TwoFieldEffacement.CommonFieldCompositeZero
public import Aglib.AlgebraicGeometry.EtaleCohomology.Fields.TwoFieldEffacement.SeparableRefinement

/-! # The original common-field square and separable pointed cover

The actual two pullback lifts and the original class-zero transport are
constructed before choosing common fields or finite stages. The pointed pure
refinement is supplied by the existing unique actual-source construction.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits CategoryTheory.PreGaloisCategory Opposite

namespace AlgebraicGeometry.Scheme.EtaleCohomology.TwoFieldEffacement
universe u
attribute [local instance] hasSheafifyLarge HasExt.standard
open FiniteEtale

/-- Transport zero through the two actual scalar pullback lifts. The original
class map is identified by its two projection equations, not replaced. -/
theorem constantRestriction_zero_of_scalarStage
    {U S P F C K E Q : Scheme.{u}}
    (p : U ⟶ S) (q : P ⟶ F) (a : P ⟶ U) (b : F ⟶ S)
    (ha : a ≫ p = q ≫ b) (c : C ⟶ F) (d : C ⟶ K) (k : K ⟶ S)
    (hcd : c ≫ b = d ≫ k) (j : E ⟶ C)
    (r : Q ⟶ P) (s : Q ⟶ E) (hrs : r ≫ q = s ≫ j ≫ c)
    (h : Q ⟶ pullback p k)
    (hfst : h ≫ pullback.fst p k = r ≫ a)
    (hsnd : h ≫ pullback.snd p k = s ≫ j ≫ d)
    (A : Type u) [AddCommGroup A] (n : ℕ)
    (ξ : Sheaf.H.{u + 2} (ConstantFinite.coefficient A (pullback p k)) n)
    (hzero : Curves.constantRestriction A
      (pullback.snd j (pullback.snd q c) ≫ scalarClassMap p q a b ha c d k hcd) n ξ = 0) :
    Curves.constantRestriction A h n ξ = 0 := by
  let rC : Q ⟶ pullback q c := pullback.lift r (s ≫ j)
    (hrs.trans (Category.assoc s j c).symm)
  let rE : Q ⟶ pullback j (pullback.snd q c) :=
    pullback.lift s rC (pullback.lift_snd _ _ _).symm
  have hr : rE ≫ pullback.snd j (pullback.snd q c) ≫
      scalarClassMap p q a b ha c d k hcd = h := by
    apply pullback.hom_ext
    · simp only [Category.assoc, scalarClassMap_fst]
      exact ((Category.assoc rE (pullback.snd j (pullback.snd q c))
        (pullback.fst q c ≫ a)).symm.trans
        ((congrArg (fun z => z ≫ pullback.fst q c ≫ a)
          (pullback.lift_snd s rC _)).trans
          ((Category.assoc rC (pullback.fst q c) a).symm.trans
            ((congrArg (fun z => z ≫ a) (pullback.lift_fst r (s ≫ j) _)).trans
              hfst.symm))))
    · simp only [Category.assoc, scalarClassMap_snd]
      exact ((Category.assoc rE (pullback.snd j (pullback.snd q c))
        (pullback.snd q c ≫ d)).symm.trans
        ((congrArg (fun z => z ≫ pullback.snd q c ≫ d)
          (pullback.lift_snd s rC _)).trans
          ((Category.assoc rC (pullback.snd q c) d).symm.trans
            ((congrArg (fun z => z ≫ d) (pullback.lift_snd r (s ≫ j) _)).trans
              ((Category.assoc s j d).trans hsnd.symm)))))
  exact (congrArg (fun z => Curves.constantRestriction A z n ξ) hr.symm).trans
    ((Curves.constantRestriction_comp A
      (pullback.snd j (pullback.snd q c) ≫ scalarClassMap p q a b ha c d k hcd)
      rE n ξ).trans (by rw [hzero, map_zero]))

section Fields
variable (k K : Type u) [Field k] [Field K] [Algebra k K]
  {U : Scheme.{u}} (p : U ⟶ Spec (.of k))

/-- The original common-field class map at the actual separable stages. -/
def separableFieldClassMap (F E : Type u) [Field F] [Field E]
    [Algebra k F] [Algebra k E] [Algebra K E] [IsScalarTower k K E]
    (a : F →ₐ[k] E) :
    pullback (pullback.snd p (Spec.algebraMap k (separableClosure k F)))
      (Spec.map (CommRingCat.ofHom (separableSourceMap k F K E a).toRingHom)) ⟶
      pullback p (Spec.algebraMap k K) :=
  scalarClassMap p (pullback.snd p (Spec.algebraMap k (separableClosure k F)))
    (pullback.fst p (Spec.algebraMap k (separableClosure k F)))
    (Spec.algebraMap k (separableClosure k F)) pullback.condition
    (Spec.map (CommRingCat.ofHom (separableSourceMap k F K E a).toRingHom))
    (Spec.algebraMap K (separableClosure K E)) (Spec.algebraMap k K)
    (separableSourceMap_spec_square k F K E a)

variable (F C E : Type u) [Field F] [Field C] [Field E]
  [Algebra k F] [Module.Finite k F]
  [Algebra k C] [Algebra K C] [IsScalarTower k K C]
  [Algebra C E] [Algebra K E] [IsScalarTower K C E]
  [Algebra k E] [IsScalarTower k K E] [Module.Finite K E]
  (aC : F →ₐ[k] C) (aE : F →ₐ[k] E)
  (haE : (algebraMap C E).comp aC.toRingHom = aE.toRingHom)
  [CompactSpace U] [QuasiSeparatedSpace U] [GeometricallyConnected p]

local instance : ConnectedSpace (pullback p (Spec.algebraMap k F) : Scheme.{u}) :=
  GeometricallyConnected.connectedSpace_of_subsingleton (pullback.snd p (Spec.algebraMap k F))
local instance : ConnectedSpace
    (pullback p (Spec.algebraMap k (separableClosure k F)) : Scheme.{u}) :=
  GeometricallyConnected.connectedSpace_of_subsingleton
    (pullback.snd p (Spec.algebraMap k (separableClosure k F)))

omit [Module.Finite k F] in
/-- The common scalar square is the original algebra-map compatibility. -/
theorem commonScalarSquare :
    Spec.map (CommRingCat.ofHom aC.toRingHom) ≫ Spec.algebraMap k F =
      Spec.algebraMap K C ≫ Spec.algebraMap k K := by
  rw [← Spec.map_comp, ← Spec.map_comp]
  apply congrArg Spec.map
  apply CommRingCat.hom_ext
  apply RingHom.ext
  intro z
  exact (aC.commutes z).trans (IsScalarTower.algebraMap_apply k K C z)

include haE in
/-- The original common-field zero supplies the original marked separable
cover. The complete scalar-square transport precedes native finite stages. -/
theorem exists_commonScalar_separable_cover_and_zero
    (x : Spec (.of k) ⟶ U) (hx : x ≫ p = 𝟙 _)
    {V : Scheme.{u}} [CompactSpace V] [QuasiSeparatedSpace V] [ConnectedSpace V]
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
    (hzero :
      let q := Y.obj.hom ≫ qV
      let a := Y.obj.hom ≫ aV
      let ha : a ≫ p = q ≫ Spec.algebraMap k F :=
        (Category.assoc Y.obj.hom aV p).trans
          ((congrArg (fun z => Y.obj.hom ≫ z) H.w).trans
            (Category.assoc Y.obj.hom qV (Spec.algebraMap k F)).symm)
      let bC := Spec.map (CommRingCat.ofHom aC.toRingHom)
      Curves.constantRestriction A
        (pullback.snd (Spec.algebraMap C E) (pullback.snd q bC) ≫
          scalarClassMap p q a (Spec.algebraMap k F) ha bC
            (Spec.algebraMap K C) (Spec.algebraMap k K)
            (commonScalarSquare k K F C aC)) degree ξ = 0) :
    ∃ Z : FiniteEtale (pullback p (Spec.algebraMap k (separableClosure k F))),
      IsGalois Z ∧ Nat.card (Aut Z) ∣ n ∧
      ∃ z : Spec (.of (separableClosure k F)) ⟶ Z.obj.left,
        z ≫ Z.obj.hom = separableSourcePoint k F p x hx ∧
        Curves.constantRestriction A
          (((baseChange (pullback.fst
            (pullback.snd p (Spec.algebraMap k (separableClosure k F)))
            (Spec.map (CommRingCat.ofHom
              (separableSourceMap k F K E aE).toRingHom)))).obj Z).obj.hom ≫
              separableFieldClassMap k K p F E aE) degree ξ = 0 := by
  let F₀ := separableClosure k F
  let E₀ := separableClosure K E
  let b₀ := Spec.algebraMap k F₀
  let p₀ := pullback.snd p b₀
  let a₀ := Spec.map (CommRingCat.ofHom (separableSourceMap k F K E aE).toRingHom)
  let W := pullback p₀ a₀
  let pW : W ⟶ Spec (.of E₀) := pullback.snd p₀ a₀
  let D := pullback pW (Spec.algebraMap E₀ E)
  let g : D ⟶ V := separableCommonProjection k F K E aE p₀ ≫
    (separableSourceTowerIso k F p).hom ≫ H.isoPullback.inv
  let Q := (baseChange g).obj Y
  let q := Y.obj.hom ≫ qV
  let aY := Y.obj.hom ≫ aV
  have haY : aY ≫ p = q ≫ Spec.algebraMap k F :=
    (Category.assoc Y.obj.hom aV p).trans
      ((congrArg (fun z => Y.obj.hom ≫ z) H.w).trans
        (Category.assoc Y.obj.hom qV (Spec.algebraMap k F)).symm)
  let bC := Spec.map (CommRingCat.ofHom aC.toRingHom)
  let qQ : Q.obj.left ⟶ Y.obj.left := pullback.fst Y.obj.hom g
  let dQ : Q.obj.left ⟶ D := Q.obj.hom
  let sQ := dQ ≫ pullback.snd pW (Spec.algebraMap E₀ E)
  have hgq : g ≫ qV = pullback.snd pW (Spec.algebraMap E₀ E) ≫
      Spec.map (CommRingCat.ofHom aE.toRingHom) := by
    dsimp only [g]
    rw [Category.assoc, Category.assoc, H.isoPullback_inv_snd,
      separableSourceTowerIso_hom_field, separableCommonProjection_snd]
  have hga : g ≫ aV = pullback.fst pW (Spec.algebraMap E₀ E) ≫
      pullback.fst p₀ a₀ ≫ pullback.fst p b₀ := by
    dsimp only [g]
    rw [Category.assoc, Category.assoc, H.isoPullback_inv_fst,
      separableSourceTowerIso_hom_original, ← Category.assoc,
      separableCommonProjection_fst, Category.assoc]
  have hQ : qQ ≫ Y.obj.hom = dQ ≫ g := pullback.condition
  have hqQ : qQ ≫ q = sQ ≫ Spec.map (CommRingCat.ofHom aE.toRingHom) :=
    (Category.assoc qQ Y.obj.hom qV).symm.trans
      ((congrArg (fun z => z ≫ qV) hQ).trans
        ((Category.assoc dQ g qV).trans
          ((congrArg (fun z => dQ ≫ z) hgq).trans
            (Category.assoc dQ (pullback.snd pW (Spec.algebraMap E₀ E))
              (Spec.map (CommRingCat.ofHom aE.toRingHom))).symm)))
  have hbc : Spec.algebraMap C E ≫ bC = Spec.map (CommRingCat.ofHom aE.toRingHom) := by
    rw [← Spec.map_comp]
    exact congrArg Spec.map (CommRingCat.hom_ext haE)
  let h := separableFieldClassMap k K p F E aE
  have hfst : (dQ ≫ pullback.fst pW (Spec.algebraMap E₀ E) ≫ h) ≫
      pullback.fst p (Spec.algebraMap k K) = qQ ≫ aY := by
    simp only [Category.assoc, h, separableFieldClassMap, scalarClassMap_fst]
    have hQa : qQ ≫ aY = dQ ≫ g ≫ aV :=
      (Category.assoc qQ Y.obj.hom aV).symm.trans
        ((congrArg (fun z => z ≫ aV) hQ).trans (Category.assoc dQ g aV))
    exact (hQa.trans (congrArg (fun z => dQ ≫ z) hga)).symm
  have hsnd : (dQ ≫ pullback.fst pW (Spec.algebraMap E₀ E) ≫ h) ≫
      pullback.snd p (Spec.algebraMap k K) = sQ ≫ Spec.algebraMap C E ≫ Spec.algebraMap K C := by
    have ht : Spec.algebraMap E₀ E ≫ Spec.algebraMap K E₀ =
        Spec.algebraMap C E ≫ Spec.algebraMap K C := by
      rw [← Spec.map_comp, ← Spec.map_comp]
      exact congrArg Spec.map (CommRingCat.hom_ext
        ((IsScalarTower.algebraMap_eq K E₀ E).symm.trans
          (IsScalarTower.algebraMap_eq K C E)))
    have hD := congrArg (fun z => z ≫ Spec.algebraMap K E₀)
      (pullback.condition (f := pW) (g := Spec.algebraMap E₀ E))
    have hD' := hD.trans
      ((Category.assoc (pullback.snd pW (Spec.algebraMap E₀ E))
        (Spec.algebraMap E₀ E) (Spec.algebraMap K E₀)).trans
        (congrArg (fun z => pullback.snd pW (Spec.algebraMap E₀ E) ≫ z) ht))
    simpa only [Category.assoc, h, separableFieldClassMap, scalarClassMap_snd,
      pW, p₀, a₀, b₀, sQ] using congrArg (fun z => dQ ≫ z) hD'
  have hcQ : Curves.constantRestriction A
      (dQ ≫ pullback.fst pW (Spec.algebraMap E₀ E) ≫ h) degree ξ = 0 :=
    constantRestriction_zero_of_scalarStage p q aY (Spec.algebraMap k F) haY bC
      (Spec.algebraMap K C) (Spec.algebraMap k K) (commonScalarSquare k K F C aC)
      (Spec.algebraMap C E) qQ sQ
      (hqQ.trans (congrArg (fun z => sQ ≫ z) hbc.symm))
      _ hfst hsnd A degree ξ hzero
  obtain ⟨Z, eZ, hZ, hcardZ, z, hz, _, hz0⟩ :=
    exists_cartesian_source_separable_cover_and_zero k F K E aE p x hx
      aV qV H Y zF hz₁ hz₂ h A degree ξ hcQ
  exact ⟨Z, hZ, hcardZ.symm ▸ hcard, z, hz, hz0⟩

end Fields
end AlgebraicGeometry.Scheme.EtaleCohomology.TwoFieldEffacement
