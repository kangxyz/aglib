/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Geometrically.Connected.CommonOverfield
public import Aglib.AlgebraicGeometry.EtaleCohomology.Curves.ConstantRestriction
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.Pasting

/-! # Original two-field pullbacks through one compatible closure embedding

The complete projection equations are proved on the native double pullbacks
before specializing to the chosen compatible algebraic closures. Original
constant cohomology restriction uses these same arrows and coefficients.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Scheme.EtaleCohomology.TwoFieldEffacement

universe u e

attribute [local instance] hasSheafifyLarge

section Square
variable {X S S₀ S₁ T : Scheme.{u}} (p : X ⟶ S)
  (b₀ : S₀ ⟶ S) (b₁ : S₁ ⟶ S) (c : T ⟶ S₀) (d : T ⟶ S₁)
  (h : c ≫ b₀ = d ≫ b₁)

/-- The native comparison of the two actual double pullbacks. -/
def doublePullbackIso : pullback (pullback.snd p b₀) c ≅ pullback (pullback.snd p b₁) d :=
  pullbackLeftPullbackSndIso p b₀ c ≪≫ pullback.congrHom rfl h ≪≫
    (pullbackLeftPullbackSndIso p b₁ d).symm

/-- The comparison retains the actual projection to the original scheme. -/
@[reassoc] theorem doublePullbackIso_hom_original :
    (doublePullbackIso p b₀ b₁ c d h).hom ≫
      pullback.fst (pullback.snd p b₁) d ≫ pullback.fst p b₁ =
        pullback.fst (pullback.snd p b₀) c ≫ pullback.fst p b₀ := by
  simp only [doublePullbackIso, Iso.trans_hom, Iso.symm_hom, Category.assoc,
    pullbackLeftPullbackSndIso_inv_fst, pullback.congrHom_hom, pullback.map,
    pullback.lift_fst, Category.comp_id, pullbackLeftPullbackSndIso_hom_fst]

/-- The comparison retains the actual projection to the common coefficient scheme. -/
@[reassoc] theorem doublePullbackIso_hom_field :
    (doublePullbackIso p b₀ b₁ c d h).hom ≫ pullback.snd (pullback.snd p b₁) d =
      pullback.snd (pullback.snd p b₀) c := by
  simp only [doublePullbackIso, Iso.trans_hom, Iso.symm_hom, Category.assoc,
    pullbackLeftPullbackSndIso_inv_snd_snd, pullback.congrHom_hom, pullback.map,
    pullback.lift_snd, Category.comp_id, pullbackLeftPullbackSndIso_hom_snd]

/-- Original coefficient restriction to the first double pullback is exactly
restriction through the second followed by the native comparison. -/
theorem doublePullback_constantRestriction
    [HasExt.{e} (AbelianSheaf.{u, u + 1} (pullback p b₁))]
    [HasExt.{e} (AbelianSheaf.{u, u + 1} (pullback (pullback.snd p b₁) d))]
    [HasExt.{e} (AbelianSheaf.{u, u + 1} (pullback (pullback.snd p b₀) c))]
    (A : Type u) [AddCommGroup A] (q : ℕ)
    (a : Sheaf.H.{e} (ConstantFinite.coefficient A (pullback p b₁)) q) :
    Curves.constantRestriction A
      ((doublePullbackIso p b₀ b₁ c d h).hom ≫ pullback.fst (pullback.snd p b₁) d) q a =
      Curves.constantRestriction A (doublePullbackIso p b₀ b₁ c d h).hom q
        (Curves.constantRestriction A (pullback.fst (pullback.snd p b₁) d) q a) :=
  Curves.constantRestriction_comp A _ _ q a

end Square

/-- The exact original spectrum square for the single chosen compatible closure embedding. -/
theorem compatibleClosure_spec_square (k K : Type u) [Field k] [Field K] [Algebra k K] :
    Spec.map (CommRingCat.ofHom (Geometrically.commonClosureEmbedding k K).toRingHom) ≫
      Spec.algebraMap k (AlgebraicClosure k) =
        Spec.algebraMap K (AlgebraicClosure K) ≫ Spec.algebraMap k K := by
  rw [← Spec.map_comp, ← Spec.map_comp]
  congr 1
  exact CommRingCat.hom_ext (Geometrically.commonClosureEmbedding_compatible k K)

/-- The same original two-field comparison specialized to the actual compatible closures. -/
def compatibleClosurePullbackIso (k K : Type u) [Field k] [Field K] [Algebra k K]
    {X : Scheme.{u}} (p : X ⟶ Spec (.of k)) :
    pullback (pullback.snd p (Spec.algebraMap k (AlgebraicClosure k)))
        (Spec.map (CommRingCat.ofHom (Geometrically.commonClosureEmbedding k K).toRingHom)) ≅
      pullback (pullback.snd p (Spec.algebraMap k K))
        (Spec.algebraMap K (AlgebraicClosure K)) :=
  doublePullbackIso p (Spec.algebraMap k (AlgebraicClosure k)) (Spec.algebraMap k K)
    (Spec.map (CommRingCat.ofHom (Geometrically.commonClosureEmbedding k K).toRingHom))
    (Spec.algebraMap K (AlgebraicClosure K)) (compatibleClosure_spec_square k K)

end AlgebraicGeometry.Scheme.EtaleCohomology.TwoFieldEffacement
