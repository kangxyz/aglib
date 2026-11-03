/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.Fields.TwoFieldEffacement.CompatibleClosure
public import Aglib.AlgebraicGeometry.EtaleCohomology.Curves.PointedGaloisEffacement
public import Aglib.AlgebraicGeometry.IdealSheaf.BaseChange.Fibre

/-! # An original two-field H1 class killed by a pointed source-closure cover

The existing algebraically closed pointed curve theorem is applied after one
compatible-closure comparison. The returned zero is stated for the original
class on the original target field base change and its literal composite map.
The standard Ext universe of the existing H1 supplier is retained honestly.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry.Scheme.OverField

namespace AlgebraicGeometry.Scheme.EtaleCohomology.TwoFieldEffacement

universe u eX eS eT

attribute [local instance] hasSheafifyLarge HasExt.standard

/-- Convert the original H1 zero and compose the original constant restrictions
before any closure field or finite-etale cover is substituted. -/
private theorem constantRestriction_comp_eq_zero_of_h1Pullback_eq_zero
    {X S T : Scheme.{u}}
    [HasExt.{eX} (AbelianSheaf.{u, u + 1} X)]
    [HasExt.{eS} (AbelianSheaf.{u, u + 1} S)]
    [HasExt.{eT} (AbelianSheaf.{u, u + 1} T)]
    (A : Type u) [AddCommGroup A] (f : S ⟶ X) (g : T ⟶ S)
    (c : Sheaf.H.{eX} (ConstantFinite.coefficient A X) 1)
    (h : h1Pullback.{u, eS, eT} g (ConstantFinite.coefficient A S)
      (Curves.constantRestriction.{u, eX, eS} A f 1 c) = 0) :
    Curves.constantRestriction.{u, eX, eT} A (g ≫ f) 1 c = 0 := by
  have hz : Curves.constantRestriction.{u, eS, eT} A g 1
      (Curves.constantRestriction.{u, eX, eS} A f 1 c) = 0 := by
    rw [Curves.constantRestriction_apply, cohomologyPullback_one, h, map_zero]
  exact (Curves.constantRestriction_comp A f g 1 c).trans hz

variable (k K : Type u) [Field k] [Field K] [Algebra k K]
  (X : FScheme k) {U : Scheme.{u}} (j : U ⟶ X.left)

/-- The one original open-curve double-pullback comparison, including its
native structural equality before the compatible-closure comparison. -/
def closureOpenIso :
    pullback
      (Hom.fibreInclusion X.hom j (Spec.algebraMap k (AlgebraicClosure k)) ≫
        pullback.snd X.hom (Spec.algebraMap k (AlgebraicClosure k)))
      (Spec.map (CommRingCat.ofHom (Geometrically.commonClosureEmbedding k K).toRingHom)) ≅
      pullback (pullback.snd (j ≫ X.hom) (Spec.algebraMap k K))
        (Spec.algebraMap K (AlgebraicClosure K)) :=
  pullback.congrHom (Hom.fibreInclusion_snd X.hom j
    (Spec.algebraMap k (AlgebraicClosure k))) rfl ≪≫
      compatibleClosurePullbackIso k K (j ≫ X.hom)

/-- The actual comparison arrow back to the unchanged target-field open curve. -/
def closureClassMap :
    pullback
      (Hom.fibreInclusion X.hom j (Spec.algebraMap k (AlgebraicClosure k)) ≫
        pullback.snd X.hom (Spec.algebraMap k (AlgebraicClosure k)))
      (Spec.map (CommRingCat.ofHom (Geometrically.commonClosureEmbedding k K).toRingHom)) ⟶
      pullback (j ≫ X.hom) (Spec.algebraMap k K) :=
  (closureOpenIso k K X j).hom ≫
    pullback.fst (pullback.snd (j ≫ X.hom) (Spec.algebraMap k K))
      (Spec.algebraMap K (AlgebraicClosure K))

/-- The original target-field class is killed by an actual pointed Galois
cover over the source algebraic closure, with its unchanged annihilator bound. -/
theorem exists_sourceClosure_pointed_H1_effacement
    (hX : Curve.Properties X) [IsOpenImmersion j]
    (x : Spec (.of k) ⟶ U) (hx : x ≫ (j ≫ X.hom) = 𝟙 _)
    (A : Type u) [AddCommGroup A] [Finite A]
    (n : ℕ) (hn : 0 < n) (hkill : ∀ a : A, n • a = 0) (hunit : IsUnit (n : k))
    (c : H1Etale (pullback (j ≫ X.hom) (Spec.algebraMap k K))
      (ConstantFinite.coefficient A _)) :
    let e := Geometrically.commonClosureEmbedding k K
    letI : Algebra (AlgebraicClosure k) (AlgebraicClosure K) := e.toRingHom.toAlgebra
    let b := Spec.algebraMap k (AlgebraicClosure k)
    let jbar := Hom.fibreInclusion X.hom j b
    let pbar := jbar ≫ pullback.snd X.hom b
    let g := pullback.fst pbar (Spec.algebraMap (AlgebraicClosure k) (AlgebraicClosure K))
    let xbar : Spec (.of (AlgebraicClosure k)) ⟶ pullback (j ≫ X.hom) b :=
      pullback.lift (b ≫ x) (𝟙 _)
        (by rw [Category.assoc, hx, Category.comp_id, Category.id_comp])
    letI : Nonempty (pullback (j ≫ X.hom) b : Scheme.{u}) :=
      Nonempty.map xbar inferInstance
    letI : IsIntegral (pullback (j ≫ X.hom) b : Scheme.{u}) := by
      let : IsIntegral (pullback X.hom b : Scheme.{u}) := Curve.curveProperties_isIntegral
        Scheme.smoothFieldNormality Scheme.normalComponentsOpen
        (Curve.curveProperties_baseChange hX (AlgebraicClosure k) b)
      let : IsOpenImmersion jbar :=
        MorphismProperty.of_isPullback (Hom.fibreInclusion_isPullback X.hom j b) inferInstance
      exact isIntegral_of_isOpenImmersion jbar
    ∃ (Z : FiniteEtale (pullback (j ≫ X.hom) b)) (_z : FiniteEtale.Fiber xbar Z),
      CategoryTheory.PreGaloisCategory.IsGalois Z ∧ ConnectedSpace Z.obj.left ∧
      Surjective Z.obj.hom ∧ Nat.card (Aut Z) ∣ n ^ Group.rank (Multiplicative A) ∧
      Curves.constantRestriction.{u, u + 2, u + 2} A
        (((FiniteEtale.baseChange g).obj Z).obj.hom ≫ closureClassMap k K X j) 1 c = 0 := by
  let e := Geometrically.commonClosureEmbedding k K
  let : Algebra (AlgebraicClosure k) (AlgebraicClosure K) := e.toRingHom.toAlgebra
  let b := Spec.algebraMap k (AlgebraicClosure k)
  let Xbar : FScheme (AlgebraicClosure k) := Over.mk (pullback.snd X.hom b)
  have hXbar : Curve.Properties Xbar :=
    Curve.curveProperties_baseChange hX (AlgebraicClosure k) b
  let jbar : pullback (j ≫ X.hom) b ⟶ Xbar.left := Hom.fibreInclusion X.hom j b
  have H := Hom.fibreInclusion_isPullback X.hom j b
  let : IsOpenImmersion jbar := MorphismProperty.of_isPullback H inferInstance
  let xbar : Spec (.of (AlgebraicClosure k)) ⟶ pullback (j ≫ X.hom) b :=
    pullback.lift (b ≫ x) (𝟙 _)
      (by rw [Category.assoc, hx, Category.comp_id, Category.id_comp])
  let : Nonempty (pullback (j ≫ X.hom) b : Scheme.{u}) :=
    Nonempty.map xbar inferInstance
  let : IsIntegral Xbar.left := Curve.curveProperties_isIntegral
    Scheme.smoothFieldNormality Scheme.normalComponentsOpen hXbar
  let : IsIntegral (pullback (j ≫ X.hom) b : Scheme.{u}) :=
    isIntegral_of_isOpenImmersion jbar
  have hxbar : xbar ≫ (jbar ≫ Xbar.hom) = 𝟙 _ := by
    have hpbar : jbar ≫ Xbar.hom = pullback.snd (j ≫ X.hom) b :=
      Hom.fibreInclusion_snd X.hom j b
    exact (congrArg (fun a => xbar ≫ a) hpbar).trans (pullback.lift_snd _ _ _)
  have hk : IsUnit (n : Γ(Spec (.of (AlgebraicClosure k)), ⊤)) := by
    have hnk : IsUnit (n : AlgebraicClosure k) := by
      simpa only [map_natCast] using hunit.map (algebraMap k (AlgebraicClosure k))
    simpa only [map_natCast] using hnk.map (Scheme.ΓSpecIso (.of (AlgebraicClosure k))).inv.hom
  let f := closureClassMap k K X j
  let cΩ := Curves.constantRestriction.{u, u + 2, u + 2} A f 1 c
  obtain ⟨Z, z, zΩ, hG, hconn, hsurj, hcard, _hpoint, hzero⟩ :=
    Curves.PointedGaloisEffacement.exists_pointed_source_galois_effacement
      (AlgebraicClosure k) (AlgebraicClosure K) Xbar hXbar jbar xbar hxbar A n hn hkill hk cΩ
  let g := pullback.fst (jbar ≫ Xbar.hom)
    (Spec.algebraMap (AlgebraicClosure k) (AlgebraicClosure K))
  let ZΩ := (FiniteEtale.baseChange g).obj Z
  refine ⟨Z, z, hG, hconn, hsurj, hcard, ?_⟩
  exact constantRestriction_comp_eq_zero_of_h1Pullback_eq_zero A f ZΩ.obj.hom c hzero

end AlgebraicGeometry.Scheme.EtaleCohomology.TwoFieldEffacement
