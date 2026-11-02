/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.Fields.TwoFieldEffacement.FiniteSource
public import Aglib.AlgebraicGeometry.Geometrically.Connected.CommonOverfield
public import Aglib.AlgebraicGeometry.EtaleCohomology.Fields.TwoFieldEffacement.CommonFieldCompositeZero

/-! # The original finite source cover over its common coefficient field

This is the single complete common-field construction formerly inside
`FiniteH1`. It consumes the actual produced finite source-stage data and the
two original projection equations of the closure comparison. The source
scheme, two-stage point base, whole cover and marking are never replaced.
The proper and affine public consumers produce all input data internally.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits CategoryTheory.PreGaloisCategory Opposite

namespace AlgebraicGeometry.Scheme.EtaleCohomology.TwoFieldEffacement
universe u
attribute [local instance] hasSheafifyLarge HasExt.standard
open FiniteEtale FiniteEtale.FieldCoverDescent

/-- Descend the original supplied source-stage zero through its actual mapped
compositum, retaining both common-field triangles and the whole marked cover. -/
theorem exists_common_finite_pointed_H1_effacement_of_source
    (k K : Type u) [Field k] [Field K] [Algebra k K]
    {U : Scheme.{u}} [CompactSpace U] [QuasiSeparatedSpace U]
    (p : U ⟶ Spec (.of k)) [GeometricallyConnected p]
    (pbar : pullback p (Spec.algebraMap k (AlgebraicClosure k)) ⟶
      Spec (.of (AlgebraicClosure k)))
    (hpbar : pbar = pullback.snd p (Spec.algebraMap k (AlgebraicClosure k)))
    (φ : pullback pbar
      (Spec.map (CommRingCat.ofHom (Geometrically.commonClosureEmbedding k K).toRingHom)) ⟶
      pullback p (Spec.algebraMap k K))
    (hφfst : φ ≫ pullback.fst p (Spec.algebraMap k K) =
      pullback.fst pbar
        (Spec.map (CommRingCat.ofHom (Geometrically.commonClosureEmbedding k K).toRingHom)) ≫
      pullback.fst p (Spec.algebraMap k (AlgebraicClosure k)))
    (hφsnd : φ ≫ pullback.snd p (Spec.algebraMap k K) =
      pullback.snd pbar
        (Spec.map (CommRingCat.ofHom (Geometrically.commonClosureEmbedding k K).toRingHom)) ≫
      Spec.algebraMap K (AlgebraicClosure K))
    (x : Spec (.of k) ⟶ U)
    (A : Type u) [AddCommGroup A] [Finite A] (n : ℕ)
    (c : H1Etale (pullback p (Spec.algebraMap k K)) (ConstantFinite.coefficient A _))
    (hsource :
      let Ω := AlgebraicClosure k
      let e := Geometrically.commonClosureEmbedding k K
      letI : Algebra Ω (AlgebraicClosure K) := e.toRingHom.toAlgebra
      let b := Spec.algebraMap k Ω
      let g := pullback.fst pbar
        (Spec.algebraMap Ω (AlgebraicClosure K))
      ∃ (s : Finset Ω)
        (Z : FiniteEtale (((FieldLimit.schemeDiagram k Ω p).obj (op s)).left))
        (t : Finset Ω),
        let k₀ := FieldLimit.finiteField k Ω s
        let q₀ := pullback.fst (Spec.algebraMap k k₀) p
        let F := pointField k₀ Ω t
        let a := pullback.fst q₀ (Spec.algebraMap k₀ F)
        let ZF := (baseChange a).obj Z
        letI : ConnectedSpace (pullback q₀ (Spec.algebraMap k₀ F) : Scheme.{u}) :=
          GeometricallyConnected.connectedSpace_of_subsingleton
            (pullback.snd q₀ (Spec.algebraMap k₀ F))
        let v := pointProjection k₀ Ω q₀
          (FieldLimit.fieldProjection k Ω p (op s)) (pullback.snd p b)
          (fieldProjection_isPullback k Ω p s) t
        ∃ (xF : Spec (.of F) ⟶ pointBase k₀ Ω q₀ t)
          (zF : Spec (.of F) ⟶ ZF.obj.left),
          Module.Finite k F ∧
          IsPullback (a ≫ pullback.snd (Spec.algebraMap k k₀) p)
            (pullback.snd q₀ (Spec.algebraMap k₀ F)) p (Spec.algebraMap k F) ∧
          xF ≫ pullback.snd q₀ (Spec.algebraMap k₀ F) = 𝟙 _ ∧
          xF ≫ a ≫ pullback.snd (Spec.algebraMap k k₀) p = Spec.algebraMap k F ≫ x ∧
          zF ≫ ZF.obj.hom = xF ∧ IsGalois ZF ∧
          Nat.card (Aut ZF) ∣ n ^ Group.rank (Multiplicative A) ∧
          Curves.constantRestriction A
            (((baseChange (g ≫ v)).obj ZF).obj.hom ≫ φ) 1 c = 0
    ) :
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
  let Ω := AlgebraicClosure k
  let ΩK := AlgebraicClosure K
  let e := Geometrically.commonClosureEmbedding k K
  let : Algebra Ω ΩK := e.toRingHom.toAlgebra
  let b := Spec.algebraMap k Ω
  let g := pullback.fst pbar (Spec.algebraMap Ω ΩK)
  let w := pullback.snd p b
  obtain ⟨s, Z, t, xF, zF, hfinite, H, hxF, hxFa, hzF, hG, hcard, hzero⟩ :=
    hsource
  let k₀ := FieldLimit.finiteField k Ω s
  let q₀ := pullback.fst (Spec.algebraMap k k₀) p
  let F : IntermediateField k Ω := (pointField k₀ Ω t).restrictScalars k
  let V := pointBase k₀ Ω q₀ t
  let a₀ := pullback.fst q₀ (Spec.algebraMap k₀ (pointField k₀ Ω t))
  let ZF := (baseChange a₀).obj Z
  let qV := pullback.snd q₀ (Spec.algebraMap k₀ (pointField k₀ Ω t))
  let aV := a₀ ≫ pullback.snd (Spec.algebraMap k k₀) p
  let v := pointProjection k₀ Ω q₀ (FieldLimit.fieldProjection k Ω p (op s)) w
    (fieldProjection_isPullback k Ω p s) t
  let q := ZF.obj.hom ≫ qV
  let a := ZF.obj.hom ≫ aV
  have ha : a ≫ p = q ≫ Spec.algebraMap k F :=
    (Category.assoc ZF.obj.hom aV p).trans
      ((congrArg (fun z => ZF.obj.hom ≫ z) H.w).trans
        (Category.assoc ZF.obj.hom qV (Spec.algebraMap k F)).symm)
  let : Module.Finite k F := hfinite
  let : CompactSpace (pullback (Spec.algebraMap k k₀) p : Scheme.{u}) :=
    QuasiCompact.compactSpace_of_compactSpace (pullback.snd (Spec.algebraMap k k₀) p)
  let : QuasiSeparatedSpace (pullback (Spec.algebraMap k k₀) p : Scheme.{u}) :=
    quasiSeparatedSpace_of_quasiSeparated (pullback.snd (Spec.algebraMap k k₀) p)
  let : IsAffineHom a₀ :=
    (@MorphismProperty.IsStableUnderBaseChange.of_isPullback
      Scheme.{u} _ (@IsAffineHom) isAffineHom_isStableUnderBaseChange)
      (IsPullback.of_hasPullback q₀ (Spec.algebraMap k₀ (pointField k₀ Ω t))).flip
      inferInstance
  let : CompactSpace V := QuasiCompact.compactSpace_of_compactSpace a₀
  let : QuasiSeparatedSpace V := quasiSeparatedSpace_of_quasiSeparated a₀
  let : CompactSpace ZF.obj.left := QuasiCompact.compactSpace_of_compactSpace ZF.obj.hom
  let : QuasiSeparatedSpace ZF.obj.left := quasiSeparatedSpace_of_quasiSeparated ZF.obj.hom
  let W := (baseChange (g ≫ v)).obj ZF
  let r : W.obj.left ⟶ ZF.obj.left := pullback.fst ZF.obj.hom (g ≫ v)
  let sΩ : W.obj.left ⟶ Spec (.of ΩK) :=
    W.obj.hom ≫ pullback.snd pbar (Spec.algebraMap Ω ΩK)
  have Hv : IsPullback v w qV (Spec.algebraMap F Ω) :=
    pointProjection_isPullback k₀ Ω q₀ (FieldLimit.fieldProjection k Ω p (op s)) w
      (fieldProjection_isPullback k Ω p s) t
  have Hg : IsPullback g (pullback.snd pbar (Spec.algebraMap Ω ΩK)) w
      (Spec.algebraMap Ω ΩK) := by
    have hp : pbar = w := hpbar
    rw [← hp]
    exact IsPullback.of_hasPullback _ _
  have heF : Spec.algebraMap Ω ΩK ≫ Spec.algebraMap F Ω =
      Spec.map (CommRingCat.ofHom (e.comp F.val).toRingHom) := by
    rw [← Spec.map_comp]
    congr 1
  have HW : IsPullback r sΩ q
      (Spec.map (CommRingCat.ofHom (e.comp F.val).toRingHom)) := by
    have h := (IsPullback.of_hasPullback ZF.obj.hom (g ≫ v)).paste_vert
      (Hg.paste_horiz Hv)
    exact (congrArg (fun z => IsPullback r sΩ q z) heF).mp h
  have hv : v ≫ aV = pullback.fst p b :=
    (Category.assoc v a₀ (pullback.snd (Spec.algebraMap k k₀) p)).symm.trans
      ((congrArg (fun z => z ≫ pullback.snd (Spec.algebraMap k k₀) p)
        (pointProjection_fst k₀ Ω q₀ (FieldLimit.fieldProjection k Ω p (op s)) w
          (fieldProjection_isPullback k Ω p s) t)).trans
        (FieldLimit.fieldProjection_base k Ω p (op s)))
  let h := W.obj.hom ≫ φ
  have hfst : h ≫ pullback.fst p (Spec.algebraMap k K) = r ≫ a := by
    rw [show h = W.obj.hom ≫ φ from rfl,
      Category.assoc, hφfst]
    change W.obj.hom ≫ g ≫ pullback.fst p b = r ≫ ZF.obj.hom ≫ aV
    have hW : r ≫ ZF.obj.hom = W.obj.hom ≫ (g ≫ v) := pullback.condition
    exact (congrArg (fun z => W.obj.hom ≫ g ≫ z) hv.symm).trans
      (by simpa only [Category.assoc] using congrArg (fun z => z ≫ aV) hW.symm)
  have hsnd : h ≫ pullback.snd p (Spec.algebraMap k K) = sΩ ≫ Spec.algebraMap K ΩK := by
    rw [show h = W.obj.hom ≫ φ from rfl,
      Category.assoc, hφsnd]
    exact (Category.assoc _ _ _).symm
  have hfiniteZero := exists_common_finiteField_composite_zero k K Ω ΩK F e
    p q a ha r sΩ HW h hfst hsnd A 1 c hzero
  exact ⟨F, V, qV, aV, H, ZF, xF, zF, hfinite, hxF, hxFa, hzF, hG, hcard, hfiniteZero⟩

end AlgebraicGeometry.Scheme.EtaleCohomology.TwoFieldEffacement
