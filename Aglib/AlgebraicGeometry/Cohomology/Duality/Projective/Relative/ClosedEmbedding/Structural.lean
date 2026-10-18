/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Cohomology.Duality.Projective.Relative.ClosedEmbedding

/-!
# Structural linearity of the original closed-embedding Serre comparison

The supplied-resolution adjunction and original structural scalar actions make
the literal chosen-embedding comparison linear in every nonnegative degree.
These constructions require no coherent duality or Noetherian hypothesis.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian Opposite
open AlgebraicGeometry AlgebraicGeometry.ProjectiveSpace AlgebraicGeometry.Scheme.Modules
open AlgebraicGeometry.Scheme.Modules.QuasiCoherent

universe u
attribute [local instance] AlgebraicGeometry.Scheme.Modules.standardHasDerivedCategory

private theorem pushforwardLinearOfHom {S : Type u} [CommRing S]
    {X Y : Scheme.{u}} (f : X ⟶ Y) (α : S →+* Γ(Y, ⊤)) :
    letI := moduleCategoryLinearOfHom X (f.appTop.hom.comp α)
    letI := moduleCategoryLinearOfHom Y α
    (Scheme.Modules.pushforward f).Linear S := by
  let := moduleCategoryLinearOfHom X (f.appTop.hom.comp α)
  let := moduleCategoryLinearOfHom Y α
  refine { map_smul := ?_ }
  intro M N φ r
  apply Scheme.Modules.hom_ext
  intro U
  ext x
  change (r • φ).val.app (op (f ⁻¹ᵁ U)) x =
    (r • (Scheme.Modules.pushforward f).map φ).val.app (op U) x
  rw [moduleCategoryLinearOfHom_smul_app X (f.appTop.hom.comp α),
    moduleCategoryLinearOfHom_smul_app Y α]
  change X.presheaf.map (homOfLE (show f ⁻¹ᵁ U ≤ ⊤ from le_top)).op
      (f.appTop (α r)) • φ.val.app (op (f ⁻¹ᵁ U)) x =
    f.app U (Y.presheaf.map (homOfLE (show U ≤ ⊤ from le_top)).op (α r)) •
      φ.val.app (op (f ⁻¹ᵁ U)) x
  have h := congrArg
    (fun q : Γ(Y, ⊤) ⟶ Γ(X, f ⁻¹ᵁ U) => q.hom (α r))
    (f.naturality (homOfLE (show U ≤ ⊤ from le_top)).op)
  change f.app U (Y.presheaf.map (homOfLE (show U ≤ ⊤ from le_top)).op (α r)) =
    X.presheaf.map (homOfLE (show f ⁻¹ᵁ U ≤ ⊤ from le_top)).op (f.appTop (α r)) at h
  rw [h]

namespace AlgebraicGeometry.Scheme.Cohomology

variable {Z X Y : Scheme.{u}} (i : Z ⟶ X) [IsClosedImmersion i] (p : X ⟶ Y)

/-- The actual input equivalence is linear for the original structural actions.
Only left-source naturality of the same supplied-resolution adjunction is used. -/
def relativeClosedEmbeddingInputLinearEquiv {S : Type u} [CommRing S]
    (α : S →+* Γ(X, ⊤)) (Ω : X.Modules) (M : Z.Modules) (q : ℕ) :
    letI := moduleCategoryLinearOfHom Z (i.appTop.hom.comp α)
    letI := moduleCategoryLinearOfHom X α
    ((DerivedCategory.singleFunctor Z.Modules 0).obj M ⟶
      (DerivedCategory.Plus.ι.obj ((Scheme.Modules.derivedClosedImmersionRightAdjointPlus i).obj
        ((DerivedCategory.Plus.singleFunctor X.Modules 0).obj Ω)))⟦(q : ℤ)⟧) ≃ₗ[S]
      Ext.{u + 1} ((Scheme.Modules.pushforward i).obj M) Ω q := by
  let := moduleCategoryLinearOfHom Z (i.appTop.hom.comp α)
  let := moduleCategoryLinearOfHom X α
  let : (Scheme.Modules.pushforward i).Linear S := by
    exact pushforwardLinearOfHom i α
  let I := injectiveResolution Ω
  let E :
      ((DerivedCategory.singleFunctor X.Modules 0).obj ((Scheme.Modules.pushforward i).obj M) ⟶
        ((DerivedCategory.singleFunctor X.Modules 0).obj Ω)⟦(q : ℤ)⟧) ≃ₗ[S]
      ((DerivedCategory.singleFunctor Z.Modules 0).obj M ⟶
        (DerivedCategory.Plus.ι.obj ((Scheme.Modules.derivedClosedImmersionRightAdjointPlus i).obj
          ((DerivedCategory.Plus.singleFunctor X.Modules 0).obj Ω)))⟦(q : ℤ)⟧) :=
    { Adjunction.singleDerivedHomEquivOfInjectiveResolution
        (Scheme.Modules.closedImmersionRightAdjunction i) M I (q : ℤ) with
      map_smul' := by
        intro r x
        have hx := Adjunction.singleDerivedHomEquivOfInjectiveResolution_naturality_left
          (Scheme.Modules.closedImmersionRightAdjunction i) M I (q : ℤ) (r • 𝟙 M) x
        erw [(Scheme.Modules.pushforward i).map_smul,
          (Scheme.Modules.pushforward i).map_id,
          (DerivedCategory.singleFunctor X.Modules 0).map_smul,
          (DerivedCategory.singleFunctor X.Modules 0).map_id,
          (DerivedCategory.singleFunctor Z.Modules 0).map_smul,
          (DerivedCategory.singleFunctor Z.Modules 0).map_id] at hx
        erw [Linear.smul_comp, Category.id_comp, Linear.smul_comp, Category.id_comp] at hx
        exact hx }
  exact E.symm.trans (Ext.homLinearEquiv (R := S)
    (X := (Scheme.Modules.pushforward i).obj M) (Y := Ω) (n := q)).symm

/-- The linear input equivalence retains exactly the original adjunction inverse and Ext map. -/
theorem relativeClosedEmbeddingInputLinearEquiv_apply {S : Type u} [CommRing S]
    (α : S →+* Γ(X, ⊤)) (Ω : X.Modules) (M : Z.Modules) (q : ℕ)
    (x : (DerivedCategory.singleFunctor Z.Modules 0).obj M ⟶
      (DerivedCategory.Plus.ι.obj ((Scheme.Modules.derivedClosedImmersionRightAdjointPlus i).obj
        ((DerivedCategory.Plus.singleFunctor X.Modules 0).obj Ω)))⟦(q : ℤ)⟧) :
    relativeClosedEmbeddingInputLinearEquiv i α Ω M q x =
      relativeClosedEmbeddingInputAddEquiv i Ω M q x := rfl

/-- Structural scalar compatibility of the literal additive input equivalence. -/
theorem relativeClosedEmbeddingInputAddEquiv_smul {S : Type u} [CommRing S]
    (α : S →+* Γ(X, ⊤)) (Ω : X.Modules) (M : Z.Modules) (q : ℕ) (r : S) :
    letI := moduleCategoryLinearOfHom Z (i.appTop.hom.comp α)
    letI := moduleCategoryLinearOfHom X α
    ∀ x : (DerivedCategory.singleFunctor Z.Modules 0).obj M ⟶
      (DerivedCategory.Plus.ι.obj ((Scheme.Modules.derivedClosedImmersionRightAdjointPlus i).obj
        ((DerivedCategory.Plus.singleFunctor X.Modules 0).obj Ω)))⟦(q : ℤ)⟧,
      relativeClosedEmbeddingInputAddEquiv i Ω M q (r • x) =
        r • relativeClosedEmbeddingInputAddEquiv i Ω M q x := by
  let := moduleCategoryLinearOfHom Z (i.appTop.hom.comp α)
  let := moduleCategoryLinearOfHom X α
  intro x
  exact (relativeClosedEmbeddingInputLinearEquiv i α Ω M q).map_smul r x

variable (R : Type u) [CommRing R] (ι : Type u)
  (a : X ⟶ ProjectiveSpace R ι) (f : Y ⟶ Spec (.of R))
  (h : IsPullback a p (toSpec R ι) f) [Y.IsSeparated]

/-- The original chosen-embedding Serre map, linear for the structural base action and
its pullback along the actual composite to the base. -/
def relativeClosedEmbeddingSerreLinearMap {S : Type u} [CommRing S]
    (α : S →+* Γ(Y, ⊤)) (n : ℕ) (e : ι ≃ Fin (n + 1))
    (N : Y.Modules) [N.IsQuasicoherent] (M : Z.Modules) (q : ℕ) :
    letI := moduleCategoryLinearOfHom Z (i.appTop.hom.comp (p.appTop.hom.comp α))
    letI := moduleCategoryLinearOfHom Y α
    ((DerivedCategory.singleFunctor Z.Modules 0).obj M ⟶
      (DerivedCategory.Plus.ι.obj ((Scheme.Modules.derivedClosedImmersionRightAdjointPlus i).obj
        ((DerivedCategory.Plus.singleFunctor X.Modules 0).obj
          ((relativeTopDifferentialCoefficientsFunctor p n).obj N))))⟦(q : ℤ)⟧) →ₗ[S]
      (DerivedCategory.Plus.ι.obj ((Scheme.Modules.derivedPushforwardPlus (i ≫ p)).obj
          ((DerivedCategory.Plus.singleFunctor Z.Modules 0).obj M)) ⟶
        ((DerivedCategory.singleFunctor Y.Modules (n : ℤ)).obj N)⟦(q : ℤ)⟧) := by
  let := moduleCategoryLinearOfHom Z (i.appTop.hom.comp (p.appTop.hom.comp α))
  let := moduleCategoryLinearOfHom X (p.appTop.hom.comp α)
  let := moduleCategoryLinearOfHom Y α
  let E := relativeClosedEmbeddingInputLinearEquiv i (p.appTop.hom.comp α)
    ((relativeTopDifferentialCoefficientsFunctor p n).obj N) M q
  let D := DerivedCategory.Plus.ι.mapIso (relativeClosedEmbeddingPushforwardSingleIso i p M)
  let Φ := relativeProjectiveSerreLinearMap R ι a p f h α n e N
    ((Scheme.Modules.pushforward i).obj M) q
  refine { relativeClosedEmbeddingSerreMap i p R ι a f h n e N M q with map_smul' := ?_ }
  intro r x
  change D.hom ≫ Φ (E (r • x)) = r • (D.hom ≫ Φ (E x))
  rw [E.map_smul, Φ.map_smul, Linear.comp_smul]

/-- The linear map has literally the original chosen-embedding comparison as forward map. -/
theorem relativeClosedEmbeddingSerreLinearMap_apply {S : Type u} [CommRing S]
    (α : S →+* Γ(Y, ⊤)) (n : ℕ) (e : ι ≃ Fin (n + 1))
    (N : Y.Modules) [N.IsQuasicoherent] (M : Z.Modules) (q : ℕ)
    (x : (DerivedCategory.singleFunctor Z.Modules 0).obj M ⟶
      (DerivedCategory.Plus.ι.obj ((Scheme.Modules.derivedClosedImmersionRightAdjointPlus i).obj
        ((DerivedCategory.Plus.singleFunctor X.Modules 0).obj
          ((relativeTopDifferentialCoefficientsFunctor p n).obj N))))⟦(q : ℤ)⟧) :
    relativeClosedEmbeddingSerreLinearMap i p R ι a f h α n e N M q x =
      relativeClosedEmbeddingSerreMap i p R ι a f h n e N M q x := rfl

/-- Scalar compatibility of the original chosen-embedding Serre comparison. -/
theorem relativeClosedEmbeddingSerreMap_smul {S : Type u} [CommRing S]
    (α : S →+* Γ(Y, ⊤)) (n : ℕ) (e : ι ≃ Fin (n + 1))
    (N : Y.Modules) [N.IsQuasicoherent] (M : Z.Modules) (q : ℕ) (r : S) :
    letI := moduleCategoryLinearOfHom Z (i.appTop.hom.comp (p.appTop.hom.comp α))
    letI := moduleCategoryLinearOfHom Y α
    ∀ x : (DerivedCategory.singleFunctor Z.Modules 0).obj M ⟶
      (DerivedCategory.Plus.ι.obj ((Scheme.Modules.derivedClosedImmersionRightAdjointPlus i).obj
        ((DerivedCategory.Plus.singleFunctor X.Modules 0).obj
          ((relativeTopDifferentialCoefficientsFunctor p n).obj N))))⟦(q : ℤ)⟧,
      relativeClosedEmbeddingSerreMap i p R ι a f h n e N M q (r • x) =
        r • relativeClosedEmbeddingSerreMap i p R ι a f h n e N M q x := by
  let := moduleCategoryLinearOfHom Z (i.appTop.hom.comp (p.appTop.hom.comp α))
  let := moduleCategoryLinearOfHom Y α
  intro x
  exact (relativeClosedEmbeddingSerreLinearMap i p R ι a f h α n e N M q).map_smul r x

end AlgebraicGeometry.Scheme.Cohomology
