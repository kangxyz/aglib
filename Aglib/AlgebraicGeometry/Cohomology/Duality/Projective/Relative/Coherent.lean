/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Cohomology.Duality.Projective.Relative.Comparison.Open
public import Aglib.AlgebraicGeometry.Cohomology.Duality.Projective.Relative.Coherent.AffineCover
public import Aglib.AlgebraicGeometry.Cohomology.Duality.Projective.Relative.Coherent.Biproduct
public import Aglib.AlgebraicGeometry.Cohomology.Duality.Projective.Relative.Coherent.Induction

/-!
# Relative projective Serre duality for arbitrary quasicoherent coefficients

The equivalence has the original derived-image and normalized-trace map as its
forward map in every nonnegative degree. The base is Noetherian and separated,
the source module is coherent in the native affine-local finite-type sense,
and the coefficient is arbitrary quasicoherent.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian
open AlgebraicGeometry AlgebraicGeometry.ProjectiveSpace AlgebraicGeometry.Scheme.Modules
open AlgebraicGeometry.Scheme.Modules.QuasiCoherent

universe u
attribute [local instance] AlgebraicGeometry.Scheme.Modules.standardHasDerivedCategory
attribute [local instance] CategoryTheory.Abelian.hasFiniteBiproducts

namespace AlgebraicGeometry.Scheme.Cohomology

variable (R : Type u) [CommRing R] (ι : Type u)
  {X Y : Scheme.{u}} (a : X ⟶ ProjectiveSpace R ι) (p : X ⟶ Y)
  (f : Y ⟶ Spec (.of R)) (h : IsPullback a p (toSpec R ι) f)
  [Y.IsSeparated] [IsNoetherian Y]

/-- The literal relative projective Serre comparison is bijective in every degree.
There is no flatness or perfection condition on the coefficient or base. -/
theorem relativeProjectiveSerreMap_bijective
    (n : ℕ) (e : ι ≃ Fin (n + 1)) (N : Y.Modules) [N.IsQuasicoherent]
    (M : X.Modules) (hM : affineLocallyFiniteType X M) (q : ℕ) :
    Function.Bijective (relativeProjectiveSerreMap R ι a p f h n e N M q) := by
  let : M.IsQuasicoherent := quasicoherent_of_affineCharts M
    (fun A j _ => (hM A j).1)
  obtain ⟨J, hJ, U, hU, hAffine, hQC⟩ := exists_finiteAffineOpenCover_relativeSerre Y
  let := hJ
  let : ∀ j, QuasiCompact (U j).ι := hQC
  apply relativeProjectiveSerreMap_bijective_of_finiteOpenCover R ι a p f h n e U hU M
    (N := N) (q := q)
  intro N' _ r
  let : ∀ j, ((Scheme.Modules.pushforward (U j).ι).obj
      (N'.restrict (U j).ι)).IsQuasicoherent := fun j =>
    Scheme.Modules.QuasiCoherent.quasicoherent_pushforward_open (U j).ι
      (N'.restrict (U j).ι)
  apply relativeProjectiveSerreMap_biproduct_bijective R ι a p f h n e
    (fun j => (Scheme.Modules.pushforward (U j).ι).obj (N'.restrict (U j).ι)) M r
  intro j
  let : IsAffine (U j).toScheme := hAffine j
  exact relativeProjectiveSerreMap_openPushforward_bijective R ι a p f h n e
    (U j).ι (N'.restrict (U j).ι) M hM r

/-- Relative projective Serre duality for every specified structural base-ring action.
Its forward linear map is the original comparison, with the original pulled-back action. -/
def relativeProjectiveSerreDuality {S : Type u} [CommRing S]
    (α : S →+* Γ(Y, ⊤)) (n : ℕ) (e : ι ≃ Fin (n + 1))
    (N : Y.Modules) [N.IsQuasicoherent] (M : X.Modules)
    (hM : affineLocallyFiniteType X M) (q : ℕ) :
    letI := moduleCategoryLinearOfHom X (p.appTop.hom.comp α)
    letI := moduleCategoryLinearOfHom Y α
    Ext.{u + 1} M ((relativeTopDifferentialCoefficientsFunctor p n).obj N) q ≃ₗ[S]
      (DerivedCategory.Plus.ι.obj ((Scheme.Modules.derivedPushforwardPlus p).obj
          ((DerivedCategory.Plus.singleFunctor X.Modules 0).obj M)) ⟶
        ((DerivedCategory.singleFunctor Y.Modules (n : ℤ)).obj N)⟦(q : ℤ)⟧) := by
  let := moduleCategoryLinearOfHom X (p.appTop.hom.comp α)
  let := moduleCategoryLinearOfHom Y α
  exact LinearEquiv.ofBijective (relativeProjectiveSerreLinearMap R ι a p f h α n e N M q)
    (relativeProjectiveSerreMap_bijective R ι a p f h n e N M hM q)

/-- The equivalence does not change the original forward map. -/
theorem relativeProjectiveSerreDuality_apply {S : Type u} [CommRing S]
    (α : S →+* Γ(Y, ⊤)) (n : ℕ) (e : ι ≃ Fin (n + 1))
    (N : Y.Modules) [N.IsQuasicoherent] (M : X.Modules)
    (hM : affineLocallyFiniteType X M) (q : ℕ)
    (x : Ext.{u + 1} M ((relativeTopDifferentialCoefficientsFunctor p n).obj N) q) :
    relativeProjectiveSerreDuality R ι a p f h α n e N M hM q x =
      relativeProjectiveSerreMap R ι a p f h n e N M q x := rfl

end AlgebraicGeometry.Scheme.Cohomology
