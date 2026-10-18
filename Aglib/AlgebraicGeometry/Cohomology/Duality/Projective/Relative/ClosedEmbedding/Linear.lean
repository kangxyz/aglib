/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Cohomology.Duality.Projective.Relative.ClosedEmbedding.Structural
public import Aglib.AlgebraicGeometry.Cohomology.Duality.Projective.Relative.Coherent
public import Aglib.AlgebraicGeometry.Modules.QuasiCoherent.FiniteType.Pushforward

/-!
# Linear Serre duality through a closed embedding

Native finite-morphism pushforward finiteness and ambient coherent duality make
the original structural comparison a linear equivalence over a Noetherian
separated base.
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

namespace AlgebraicGeometry.Scheme.Cohomology

variable {Z X Y : Scheme.{u}} (i : Z ⟶ X) [IsClosedImmersion i] (p : X ⟶ Y)

variable (R : Type u) [CommRing R] (ι : Type u)
  (a : X ⟶ ProjectiveSpace R ι) (f : Y ⟶ Spec (.of R))
  (h : IsPullback a p (toSpec R ι) f) [Y.IsSeparated]

/-- The actual chosen-embedding comparison is bijective for coherent source modules over
a Noetherian base and arbitrary quasicoherent coefficients. -/
theorem relativeClosedEmbeddingSerreMap_bijective [IsNoetherian Y]
    (n : ℕ) (e : ι ≃ Fin (n + 1)) (N : Y.Modules) [N.IsQuasicoherent]
    (M : Z.Modules) (hM : affineLocallyFiniteType Z M) (q : ℕ) :
    Function.Bijective (relativeClosedEmbeddingSerreMap i p R ι a f h n e N M q) := by
  apply (relativeClosedEmbeddingSerreMap_bijective_iff i p R ι a f h n e N M q).2
  exact relativeProjectiveSerreMap_bijective R ι a p f h n e N
    ((Scheme.Modules.pushforward i).obj M)
    (Scheme.Modules.QuasiCoherent.FiniteMorphism.affineLocallyFiniteType_pushforward i hM) q

/-- Relative Serre duality through the chosen closed embedding for the specified base-ring
action, with the literal original comparison as forward map. -/
def relativeClosedEmbeddingSerreDuality [IsNoetherian Y] {S : Type u} [CommRing S]
    (α : S →+* Γ(Y, ⊤)) (n : ℕ) (e : ι ≃ Fin (n + 1))
    (N : Y.Modules) [N.IsQuasicoherent] (M : Z.Modules)
    (hM : affineLocallyFiniteType Z M) (q : ℕ) :
    letI := moduleCategoryLinearOfHom Z (i.appTop.hom.comp (p.appTop.hom.comp α))
    letI := moduleCategoryLinearOfHom Y α
    ((DerivedCategory.singleFunctor Z.Modules 0).obj M ⟶
      (DerivedCategory.Plus.ι.obj ((Scheme.Modules.derivedClosedImmersionRightAdjointPlus i).obj
        ((DerivedCategory.Plus.singleFunctor X.Modules 0).obj
          ((relativeTopDifferentialCoefficientsFunctor p n).obj N))))⟦(q : ℤ)⟧) ≃ₗ[S]
      (DerivedCategory.Plus.ι.obj ((Scheme.Modules.derivedPushforwardPlus (i ≫ p)).obj
          ((DerivedCategory.Plus.singleFunctor Z.Modules 0).obj M)) ⟶
        ((DerivedCategory.singleFunctor Y.Modules (n : ℤ)).obj N)⟦(q : ℤ)⟧) := by
  let := moduleCategoryLinearOfHom Z (i.appTop.hom.comp (p.appTop.hom.comp α))
  let := moduleCategoryLinearOfHom Y α
  exact LinearEquiv.ofBijective
    (relativeClosedEmbeddingSerreLinearMap i p R ι a f h α n e N M q)
    (relativeClosedEmbeddingSerreMap_bijective i p R ι a f h n e N M hM q)

/-- The equivalence retains exactly the original chosen-embedding forward map. -/
theorem relativeClosedEmbeddingSerreDuality_apply [IsNoetherian Y]
    {S : Type u} [CommRing S] (α : S →+* Γ(Y, ⊤))
    (n : ℕ) (e : ι ≃ Fin (n + 1)) (N : Y.Modules) [N.IsQuasicoherent]
    (M : Z.Modules) (hM : affineLocallyFiniteType Z M) (q : ℕ)
    (x : (DerivedCategory.singleFunctor Z.Modules 0).obj M ⟶
      (DerivedCategory.Plus.ι.obj ((Scheme.Modules.derivedClosedImmersionRightAdjointPlus i).obj
        ((DerivedCategory.Plus.singleFunctor X.Modules 0).obj
          ((relativeTopDifferentialCoefficientsFunctor p n).obj N))))⟦(q : ℤ)⟧) :
    relativeClosedEmbeddingSerreDuality i p R ι a f h α n e N M hM q x =
      relativeClosedEmbeddingSerreMap i p R ι a f h n e N M q x := rfl

end AlgebraicGeometry.Scheme.Cohomology
