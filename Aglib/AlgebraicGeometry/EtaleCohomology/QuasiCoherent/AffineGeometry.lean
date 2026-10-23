/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.CategoryTheory.Sites.SheafCohomology.BasisAcyclicity.CechChange
public import Mathlib.AlgebraicGeometry.AffineScheme
public import Mathlib.AlgebraicGeometry.Group.Affine
public import Mathlib.CategoryTheory.Limits.Over
public import Mathlib.CategoryTheory.Limits.Constructions.Over.Products
public import Mathlib.AlgebraicGeometry.Limits

/-! # Actual affine-to-spectrum geometry for Čech complexes

The base change is the native affine scheme isomorphism. Every affine object
is identified with its spectrum using its original map on global sections.
The comparison of Čech complexes retains every product projection and sign.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u a b w

namespace AlgebraicGeometry.Scheme.EtaleCohomology.QuasiCoherent

variable (X : Scheme.{u}) [IsAffine X]

/-- The actual slice equivalence induced by the canonical affine scheme isomorphism. -/
def affineSliceEquivalence : Over X ≌ Over (Spec Γ(X, ⊤)) :=
  Over.mapIso X.isoSpec

/-- An affine object over the affine base becomes the spectrum of its original
map on global sections, not a separately supplied affine model. -/
def affineOverSpecIso (T : Over X) [IsAffine T.left] :
    (affineSliceEquivalence X).functor.obj T ≅ Over.mk (Spec.map T.hom.appTop) :=
  Over.isoMk T.left.isoSpec (Scheme.isoSpec_hom_naturality T.hom)

/-- The same affine arrow is the native `algSpec` object for its original
algebra of global sections. The algebra structure is induced by `appTop`. -/
def affineOverAlgSpecIso (T : Over X) [IsAffine T.left] :
    letI : Algebra Γ(X, ⊤) Γ(T.left, ⊤) := T.hom.appTop.hom.toAlgebra
    (affineSliceEquivalence X).functor.obj T ≅
      (algSpec Γ(X, ⊤)).obj (op (CommAlgCat.of Γ(X, ⊤) Γ(T.left, ⊤))) := by
  letI : Algebra Γ(X, ⊤) Γ(T.left, ⊤) := T.hom.appTop.hom.toAlgebra
  exact affineOverSpecIso X T

/-- On underlying schemes the affine comparison is the original canonical isomorphism. -/
@[simp] theorem affineOverSpecIso_hom_left (T : Over X) [IsAffine T.left] :
    (affineOverSpecIso X T).hom.left = T.left.isoSpec.hom := rfl

/-- The original finite-family Čech complex transports along the actual base isomorphism. -/
def affineCechBaseIso {A : Type a} [Category.{b} A] [Preadditive A]
    [HasProducts.{w} A] {ι : Type w} (U : ι → Over X)
    (P : (Over (Spec Γ(X, ⊤)))ᵒᵖ ⥤ A) :
    (CategoryTheory.cechComplexFunctor U).obj
      ((affineSliceEquivalence X).functor.op ⋙ P) ≅
    (CategoryTheory.cechComplexFunctor
      (fun i => (affineSliceEquivalence X).functor.obj (U i))).obj P :=
  CategoryTheory.Cech.cechComplexProductChangeIso (affineSliceEquivalence X).functor U P

end AlgebraicGeometry.Scheme.EtaleCohomology.QuasiCoherent
