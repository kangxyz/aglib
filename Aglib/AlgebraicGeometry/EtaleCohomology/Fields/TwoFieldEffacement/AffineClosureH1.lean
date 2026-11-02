/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Curves.FiniteNormalCompactification
public import Aglib.AlgebraicGeometry.EtaleCohomology.Fields.TwoFieldEffacement.CompatibleClosure
public import Aglib.AlgebraicGeometry.EtaleCohomology.Curves.PointedGaloisEffacement

/-! # Source-closure effacement for the whole original smooth affine curve

Only the source algebraic-closure curve is compactified. The original U, its
structure map, target-field class, specified point and finite cover remain the
objects used by compatible-closure comparison and subsequent finite descent.
No smooth compactification over the possibly imperfect original field occurs.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Scheme.EtaleCohomology.TwoFieldEffacement

universe u

attribute [local instance] hasSheafifyLarge HasExt.standard

/-- Whole-curve compactification supplies the existing pointed H1 theorem;
the statement retains the original affine structural morphism. -/
theorem exists_affine_pointed_source_galois_effacement
    (k K : Type u) [Field k] [IsAlgClosed k] [Field K] [IsAlgClosed K] [Algebra k K]
    (U : Scheme.{u}) [IsAffine U] [Nonempty U]
    (p : U ⟶ Spec (.of k)) [SmoothOfRelativeDimension 1 p] [GeometricallyConnected p]
    (x : Spec (.of k) ⟶ U) (hx : x ≫ p = 𝟙 _)
    (A : Type u) [AddCommGroup A] [Finite A]
    (n : ℕ) (hn : 0 < n) (hkill : ∀ a : A, n • a = 0)
    (hunit : IsUnit (n : Γ(Spec (.of k), ⊤)))
    (c : H1Etale (pullback p (Spec.algebraMap k K)) (ConstantFinite.coefficient A _)) :
    letI : ConnectedSpace U := GeometricallyConnected.connectedSpace_of_subsingleton p
    let q := Spec.algebraMap k K
    let g := pullback.fst p q
    let xK := pullback.lift (q ≫ x) (𝟙 _)
      (by rw [Category.assoc, hx, Category.comp_id, Category.id_comp])
    ∃ (Z : FiniteEtale U) (z : FiniteEtale.Fiber x Z)
      (zK : FiniteEtale.Fiber xK ((FiniteEtale.baseChange g).obj Z)),
      PreGaloisCategory.IsGalois Z ∧ ConnectedSpace Z.obj.left ∧ Surjective Z.obj.hom ∧
      Nat.card (Aut Z) ∣ n ^ Group.rank (Multiplicative A) ∧
      zK.left ≫ pullback.fst Z.obj.hom g = q ≫ z.left ∧
      h1Pullback.{u, u + 2, u + 2} ((FiniteEtale.baseChange g).obj Z).obj.hom
        (ConstantFinite.coefficient A _) c = 0 := by
  let : ConnectedSpace U := GeometricallyConnected.connectedSpace_of_subsingleton p
  obtain ⟨X, hX, j, hj, hfac⟩ := exists_whole_affine_curve_compactification k U p
  let : IsOpenImmersion j := hj
  subst p
  exact Curves.PointedGaloisEffacement.exists_pointed_source_galois_effacement
    k K X hX j x hx A n hn hkill hunit c

/-- The exact compatible-closure arrow for the original affine structure map. -/
def affineClosureClassMap
    (k K : Type u) [Field k] [Field K] [Algebra k K]
    {U : Scheme.{u}} (p : U ⟶ Spec (.of k)) :
    pullback (pullback.snd p (Spec.algebraMap k (AlgebraicClosure k)))
      (Spec.map (CommRingCat.ofHom (Geometrically.commonClosureEmbedding k K).toRingHom)) ⟶
      pullback p (Spec.algebraMap k K) :=
  (compatibleClosurePullbackIso k K p).hom ≫
    pullback.fst (pullback.snd p (Spec.algebraMap k K))
      (Spec.algebraMap K (AlgebraicClosure K))

/-- A pointed finite Galois cover of the whole source-closure affine curve
kills the original two-field H1 class along the literal composite arrow. -/
theorem exists_affine_sourceClosure_pointed_H1_effacement
    (k K : Type u) [Field k] [Field K] [Algebra k K]
    (U : Scheme.{u}) [IsAffine U]
    (p : U ⟶ Spec (.of k)) [SmoothOfRelativeDimension 1 p] [GeometricallyConnected p]
    (x : Spec (.of k) ⟶ U) (hx : x ≫ p = 𝟙 _)
    (A : Type u) [AddCommGroup A] [Finite A]
    (n : ℕ) (hn : 0 < n) (hkill : ∀ a : A, n • a = 0) (hunit : IsUnit (n : k))
    (c : H1Etale (pullback p (Spec.algebraMap k K)) (ConstantFinite.coefficient A _)) :
    let e := Geometrically.commonClosureEmbedding k K
    letI : Algebra (AlgebraicClosure k) (AlgebraicClosure K) := e.toRingHom.toAlgebra
    let b := Spec.algebraMap k (AlgebraicClosure k)
    let pbar := pullback.snd p b
    let g := pullback.fst pbar (Spec.algebraMap (AlgebraicClosure k) (AlgebraicClosure K))
    let xbar : Spec (.of (AlgebraicClosure k)) ⟶ pullback p b :=
      pullback.lift (b ≫ x) (𝟙 _)
        (by rw [Category.assoc, hx, Category.comp_id, Category.id_comp])
    ∃ (Z : FiniteEtale (pullback p b)) (_ : FiniteEtale.Fiber xbar Z),
      PreGaloisCategory.IsGalois Z ∧ ConnectedSpace Z.obj.left ∧
      Surjective Z.obj.hom ∧ Nat.card (Aut Z) ∣ n ^ Group.rank (Multiplicative A) ∧
      Curves.constantRestriction.{u, u + 2, u + 2} A
        (((FiniteEtale.baseChange g).obj Z).obj.hom ≫ affineClosureClassMap k K p) 1 c = 0 := by
  let e := Geometrically.commonClosureEmbedding k K
  let : Algebra (AlgebraicClosure k) (AlgebraicClosure K) := e.toRingHom.toAlgebra
  let b := Spec.algebraMap k (AlgebraicClosure k)
  let pbar := pullback.snd p b
  let : SmoothOfRelativeDimension 1 pbar :=
    (@MorphismProperty.IsStableUnderBaseChange.of_isPullback
      Scheme.{u} _ (@SmoothOfRelativeDimension 1)
      (smoothOfRelativeDimension_isStableUnderBaseChange 1))
      (IsPullback.of_hasPullback p b) inferInstance
  let xbar : Spec (.of (AlgebraicClosure k)) ⟶ pullback p b :=
    pullback.lift (b ≫ x) (𝟙 _)
      (by rw [Category.assoc, hx, Category.comp_id, Category.id_comp])
  let : Nonempty (pullback p b : Scheme.{u}) := Nonempty.map xbar inferInstance
  have hxbar : xbar ≫ pbar = 𝟙 _ := pullback.lift_snd _ _ _
  have hk : IsUnit (n : Γ(Spec (.of (AlgebraicClosure k)), ⊤)) := by
    have hnk : IsUnit (n : AlgebraicClosure k) := by
      simpa only [map_natCast] using hunit.map (algebraMap k (AlgebraicClosure k))
    simpa only [map_natCast] using
      hnk.map (Scheme.ΓSpecIso (.of (AlgebraicClosure k))).inv.hom
  let f := affineClosureClassMap k K p
  let cΩ := Curves.constantRestriction.{u, u + 2, u + 2} A f 1 c
  obtain ⟨Z, z, zΩ, hG, hconn, hsurj, hcard, _hpoint, hzero⟩ :=
    exists_affine_pointed_source_galois_effacement
      (AlgebraicClosure k) (AlgebraicClosure K) (pullback p b) pbar
      xbar hxbar A n hn hkill hk cΩ
  let g := pullback.fst pbar
    (Spec.algebraMap (AlgebraicClosure k) (AlgebraicClosure K))
  let ZΩ := (FiniteEtale.baseChange g).obj Z
  have hz : Curves.constantRestriction.{u, u + 2, u + 2} A ZΩ.obj.hom 1 cΩ = 0 := by
    rw [Curves.constantRestriction_apply, cohomologyPullback_one]
    change Sheaf.H.map _ 1 (h1Pullback ZΩ.obj.hom (ConstantFinite.coefficient A _) cΩ) = 0
    rw [hzero, map_zero]
  refine ⟨Z, z, hG, hconn, hsurj, hcard, ?_⟩
  exact (Curves.constantRestriction_comp A f ZΩ.obj.hom 1 c).trans hz

end AlgebraicGeometry.Scheme.EtaleCohomology.TwoFieldEffacement
