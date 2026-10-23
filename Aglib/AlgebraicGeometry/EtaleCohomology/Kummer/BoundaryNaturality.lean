/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.Kummer.Boundary

/-!
# Geometric naturality of the original Kummer boundary

The square is built from the actual root and unit coefficient maps and the
original connecting homomorphisms. The source and target Ext universes are
independent; the Gm coefficient comparison is not required to be invertible.
-/

@[expose] public section
noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory AlgebraicGeometry
open AlgebraicGeometry.Scheme.Modules.Invertible
open AlgebraicGeometry.Scheme.EtaleCohomology.Picard
open GroupCohomology.Kummer.Coefficients GroupCohomology.Kummer.CoefficientBaseChange

namespace AlgebraicGeometry.Scheme.EtaleCohomology.Kummer

universe u w w'
variable {X S : Scheme.{u}}

/-- The unit and root section maps preserve the original root inclusion. -/
theorem inclusion_unit (f : S ⟶ X) (n : ℕ) :
    inclusion X n ≫ gmUnit f = rootsUnit f n ≫ (directImage f).map (inclusion S n) := by
  ext U a
  apply (unitsSections S ((siteBaseChange f).op.obj U)).injective
  apply Additive.toMul.injective
  change (unitsSections S ((siteBaseChange f).op.obj U)
    ((gmUnit f).hom.app U ((inclusion X n).hom.app U a))).toMul =
    (unitsSections S ((siteBaseChange f).op.obj U)
      ((inclusion S n).hom.app ((siteBaseChange f).op.obj U)
        ((rootsUnit f n).hom.app U a))).toMul
  exact (gmUnit_sections f U ((inclusion X n).hom.app U a)).trans
    ((congrArg
      (Units.map (Limits.pullback.fst U.unop.hom f).appTop.hom.toMonoidHom)
      (inclusion_apply X n U a)).trans
        ((rootsUnit_sections f n U a).symm.trans
          (inclusion_apply S n ((siteBaseChange f).op.obj U)
            ((rootsUnit f n).hom.app U a)).symm))

/-- Transposing a coefficient square through an adjunction. -/
theorem adjoint_square {C D : Type*} [Category C] [Category D]
    {F : C ⥤ D} {G : D ⥤ C} (adj : F ⊣ G)
    {A B : C} {A' B' : D} (a : A ⟶ B) (b : A' ⟶ B')
    (p : A ⟶ G.obj A') (q : B ⟶ G.obj B') (h : a ≫ q = p ≫ G.map b) :
    F.map a ≫ (adj.homEquiv _ _).symm q = (adj.homEquiv _ _).symm p ≫ b := by
  apply (adj.homEquiv _ _).injective
  rw [Adjunction.homEquiv_naturality_left, Adjunction.homEquiv_naturality_right,
    Equiv.apply_symm_apply, Equiv.apply_symm_apply]
  exact h

/-- An additive functor transports multiplication-by-n squares. -/
theorem nsmul_identity_square {C D : Type*} [Category C] [Category D]
    [Preadditive C] [Preadditive D] (F : C ⥤ D) [F.Additive]
    {A : C} {B : D} (c : F.obj A ⟶ B) (n : ℕ) :
    c ≫ (n • 𝟙 B) = F.map (n • 𝟙 A) ≫ c := by
  simp only [CategoryTheory.Functor.map_nsmul, CategoryTheory.Functor.map_id,
    Preadditive.nsmul_comp,
    Preadditive.comp_nsmul, Category.id_comp, Category.comp_id]

/-- A morphism of the original short complexes after actual inverse image. -/
def sequencePullbackHom (f : S ⟶ X) (n : ℕ) :
    (sequence X n).map (inverseImage f) ⟶ sequence S n where
  τ₁ := torsorAdjunctionCoefficient f (q := rootsUnit f n)
  τ₂ := torsorAdjunctionCoefficient f (q := gmUnit f)
  τ₃ := torsorAdjunctionCoefficient f (q := gmUnit f)
  comm₁₂ := (adjoint_square (inverseImageAdjunction f) (inclusion X n) (inclusion S n)
    (rootsUnit f n) (gmUnit f) (inclusion_unit f n)).symm
  comm₂₃ := by
    change torsorAdjunctionCoefficient f (q := gmUnit f) ≫ (n • 𝟙 (gm S)) =
      (inverseImage f).map (n • 𝟙 (gm X)) ≫
        torsorAdjunctionCoefficient f (q := gmUnit f)
    exact nsmul_identity_square (inverseImage f)
      (torsorAdjunctionCoefficient f (q := gmUnit f)) n

variable [HasExt.{w} (AbelianSheaf.{u, u + 1} X)]
  [HasExt.{w'} (AbelianSheaf.{u, u + 1} S)]

/-- Original cohomology pullback with the canonical roots coefficient isomorphism. -/
def rootsCohomologyPullback (f : S ⟶ X) (n : ℕ) (hn : 0 < n)
    (hinv : IsUnit (n : Γ(X, ⊤))) (q : ℕ) :
    Sheaf.H.{w} (mu X n) q →+ Sheaf.H.{w'} (mu S n) q :=
  (Sheaf.H.map (rootsPullbackIso f n hn hinv).hom q).comp
    (cohomologyPullback f (mu X n) q)

/-- The original all-degree connecting homomorphism commutes with geometric pullback. -/
theorem boundary_pullback (f : S ⟶ X) (n : ℕ) (hn : 0 < n)
    (hinv : IsUnit (n : Γ(X, ⊤))) (q : ℕ) (a : Sheaf.H.{w} (gm X) q) :
    rootsCohomologyPullback f n hn hinv (q + 1) (boundary X n hn hinv q a) =
      boundary S n hn (levelInvertible f n hinv) q (gmCohomologyPullback f q a) := by
  change Sheaf.H.map (rootsPullbackIso f n hn hinv).hom (q + 1)
      (cohomologyPullback f (mu X n) (q + 1)
        (Sheaf.H.δ (shortExact X n hn hinv) q (q + 1) rfl a)) = _
  have hc := connecting_cohomologyPullback f (sequence X n)
    (shortExact X n hn hinv) q (q + 1) rfl a
  refine (congrArg (Sheaf.H.map (rootsPullbackIso f n hn hinv).hom (q + 1)) hc).trans ?_
  rw [← rootsUnit_adjoint]
  exact (Sheaf.H.δ_naturality q (q + 1) rfl
    ((shortExact X n hn hinv).map_of_exact (inverseImage f))
    (shortExact S n hn (levelInvertible f n hinv)) (sequencePullbackHom f n)
    (cohomologyPullback f (gm X) q a)).symm

/-- The exact arbitrary-geometric-pullback square on original ordinary Picard classes. -/
theorem picardBoundary_pullback (f : S ⟶ X) (n : ℕ) (hn : 0 < n)
    (hinv : IsUnit (n : Γ(X, ⊤))) (c : PicardGroup X) :
    rootsCohomologyPullback f n hn hinv 2 (picardBoundary X n hn hinv c) =
      picardBoundary S n hn (levelInvertible f n hinv) (pullbackClass f c) := by
  change rootsCohomologyPullback f n hn hinv 2
      (boundary X n hn hinv 1 (picardCohomologyEquiv X c)) = _
  rw [boundary_pullback, picardCohomologyEquiv_pullback]
  rfl

end AlgebraicGeometry.Scheme.EtaleCohomology.Kummer
