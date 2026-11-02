/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.Fields.TwoFieldEffacement.AffineClosureH1
public import Aglib.AlgebraicGeometry.EtaleCohomology.Fields.TwoFieldEffacement.FiniteSource

/-! # A finite source-field pointed cover killing the original closure H1 class

The genuine whole-affine curve H1 producer is followed by the existing
two-level pointed field descent. The selected point base and cover are not flattened. The
reconstruction isomorphism transports the original class-killing equation
through the actual coefficient-closure base change. Finite descent on the
coefficient field is a subsequent step, not asserted here.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.PreGaloisCategory Opposite

namespace AlgebraicGeometry.Scheme.EtaleCohomology.TwoFieldEffacement

universe u

attribute [local instance] hasSheafifyLarge HasExt.standard

open FiniteEtale FiniteEtale.FieldCoverDescent

/-- The actual finite source-field cover, prescribed split point and
annihilator-power bound are produced from the original target-field H1 class.
The class becomes zero after the coefficient algebraic-closure pullback of
that same cover. The whole original smooth affine curve and its specified
point are retained. -/
theorem exists_affine_finite_source_pointed_H1_effacement
    (k K : Type u) [Field k] [Field K] [Algebra k K]
    (U : Scheme.{u}) [IsAffine U]
    (p : U ⟶ Spec (.of k)) [SmoothOfRelativeDimension 1 p] [GeometricallyConnected p]
    (x : Spec (.of k) ⟶ U) (hx : x ≫ p = 𝟙 _)
    (A : Type u) [AddCommGroup A] [Finite A]
    (n : ℕ) (hn : 0 < n) (hkill : ∀ a : A, n • a = 0) (hunit : IsUnit (n : k))
    (c : H1Etale (pullback p (Spec.algebraMap k K))
      (ConstantFinite.coefficient A _)) :
    let Ω := AlgebraicClosure k
    let e := Geometrically.commonClosureEmbedding k K
    letI : Algebra Ω (AlgebraicClosure K) := e.toRingHom.toAlgebra
    let b := Spec.algebraMap k Ω
    let g := pullback.fst (pullback.snd p b)
      (Spec.algebraMap Ω (AlgebraicClosure K))
    ∃ (s : Finset Ω)
      (Z : FiniteEtale (((FieldLimit.schemeDiagram k Ω p).obj (op s)).left))
      (t : Finset Ω),
      let k₀ := FieldLimit.finiteField k Ω s
      let q₀ := pullback.fst (Spec.algebraMap k k₀) p
      let F := pointField k₀ Ω t
      let a := pullback.fst q₀ (Spec.algebraMap k₀ F)
      let ZF := (baseChange a).obj Z
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
          (((baseChange (g ≫ v)).obj ZF).obj.hom ≫ affineClosureClassMap k K p) 1 c = 0 := by
  let e := Geometrically.commonClosureEmbedding k K
  let : Algebra (AlgebraicClosure k) (AlgebraicClosure K) := e.toRingHom.toAlgebra
  obtain ⟨Y, z, hG, _hconn, _hsurj, hcard, hzero⟩ :=
    exists_affine_sourceClosure_pointed_H1_effacement k K U p x hx A n hn hkill hunit c
  let : IsGalois Y := hG
  exact exists_finite_source_pointed_effacement_of_cover k (AlgebraicClosure k)
    p x hx Y z A n hcard _ (affineClosureClassMap k K p) c hzero

end AlgebraicGeometry.Scheme.EtaleCohomology.TwoFieldEffacement
