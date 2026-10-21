/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Cohomology.FormalFunctions.ReesCohomologyAffine
public import Aglib.AlgebraicGeometry.Cohomology.Functoriality.Modules.LinearAlong
public import Aglib.AlgebraicGeometry.Cohomology.Functoriality.Modules.PullbackComposition
public import Aglib.AlgebraicGeometry.Cohomology.Modules.Functor
public import Aglib.AlgebraicGeometry.Modules.Pullback.UnitTriangle
public import Aglib.AlgebraicGeometry.Modules.QuasiCoherent.Pullback

/-!
# Abstract cohomology comparisons for geometric thickenings

Typed comparisons are proved at variable schemes and coefficient arrows before
specializing to quotient-ring spectra and concrete fibre products.
-/

@[expose] public noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory
open AlgebraicGeometry.Scheme.Modules

namespace AlgebraicGeometry.Scheme.Cohomology

universe u
variable {A : Type u} [CommRing A] {X Y Z : Scheme.{u}}

/-- The original geometric cohomology map as a morphism of the native module functors. -/
def moduleCohomologyAlongHom (f : Y ⟶ X) (α : A →+* Γ(X, ⊤))
    (β : A →+* Γ(Y, ⊤)) (h : f.appTop.hom.comp α = β)
    {M : X.Modules} {N : Y.Modules} (φ : M ⟶ (pushforward f).obj N) (p : ℕ) :
    (moduleCohomologyFunctorOfHom X α p).obj M ⟶
      (moduleCohomologyFunctorOfHom Y β p).obj N :=
  ModuleCat.ofHom
    (X := (moduleCohomologyFunctorOfHom X α p).obj M)
    (Y := (moduleCohomologyFunctorOfHom Y β p).obj N)
    (moduleCohomologyMapAlongLinearOfEq f α β h φ p)

/-- This bundled constructor keeps the original geometric map. -/
theorem moduleCohomologyAlongHom_apply (f : Y ⟶ X) (α : A →+* Γ(X, ⊤))
    (β : A →+* Γ(Y, ⊤)) (h : f.appTop.hom.comp α = β)
    {M : X.Modules} {N : Y.Modules} (φ : M ⟶ (pushforward f).obj N) (p : ℕ)
    (x : (moduleCohomologyFunctorOfHom X α p).obj M) :
    moduleCohomologyAlongHom f α β h φ p x = moduleCohomologyMapAlong f φ p x :=
  moduleCohomologyMapAlongLinearOfEq_apply f α β h φ p x

/-- Equality transport of the actual geometric cohomology map. -/
theorem moduleCohomologyMapAlong_congr (a b : Y ⟶ X) (h : a = b)
    {M : X.Modules} {N : Y.Modules} (φ : M ⟶ (pushforward a).obj N)
    (ψ : M ⟶ (pushforward b).obj N)
    (hφ : φ ≫ (pushforwardCongr h).hom.app N = ψ) (p : ℕ)
    (x : Sheaf.H.{u + 1} (moduleAddSheaf X M) p) :
    moduleCohomologyMapAlong a φ p x = moduleCohomologyMapAlong b ψ p x := by
  subst b
  have hi : (pushforwardCongr (rfl : a = a)).hom.app N = 𝟙 _ := by
    apply Scheme.Modules.hom_ext
    intro U
    rw [pushforwardCongr_hom_app_app]
    change N.presheaf.map (𝟙 _) = 𝟙 _
    exact N.presheaf.map_id _
  rw [hi, Category.comp_id] at hφ
  subst ψ
  rfl

/-- Original cohomology maps respect a commutative triangle and its actual
coefficient compatibility, before specializing the schemes. -/
theorem moduleCohomologyMapAlong_triangle (a : Y ⟶ X) (b : Z ⟶ X) (v : Z ⟶ Y)
    (h : v ≫ a = b) {M M' : X.Modules} {N : Y.Modules} {N' : Z.Modules}
    (φ : M ⟶ (pushforward a).obj N) (ψ : M' ⟶ (pushforward b).obj N')
    (c : N ⟶ (pushforward v).obj N') (t : M ⟶ M')
    (hc : φ ≫ (pushforward a).map c ≫ (pushforwardComp v a).hom.app N' ≫
      (pushforwardCongr h).hom.app N' = t ≫ ψ)
    (p : ℕ) (x : Sheaf.H.{u + 1} (moduleAddSheaf X M) p) :
    moduleCohomologyMapAlong v c p (moduleCohomologyMapAlong a φ p x) =
      moduleCohomologyMapAlong b ψ p
        (Sheaf.H.map ((SheafOfModules.toSheaf X.ringCatSheaf).map t) p x) := by
  rw [moduleCohomologyMapAlong_comp, ← moduleCohomologyMapAlong_precomp]
  apply moduleCohomologyMapAlong_congr _ _ h
  simpa only [Category.assoc] using hc

variable [CompactSpace X] [X.IsSeparated]

/-- Coefficient comparison followed by the actual affine-pushforward equivalence. -/
def moduleCohomologyCoefficientAffineEquiv (a : Y ⟶ X) [IsAffineHom a]
    (N : Y.Modules) [N.IsQuasicoherent] (M : X.Modules)
    (e : M ≅ (pushforward a).obj N) (α : A →+* Γ(X, ⊤)) (p : ℕ) :
    (moduleCohomologyFunctorOfHom X α p).obj M ≃ₗ[A]
      (moduleCohomologyFunctorOfHom Y (a.appTop.hom.comp α) p).obj N :=
  ((moduleCohomologyFunctorOfHom X α p).mapIso e).toLinearEquiv.trans
    (moduleCohomologyAffinePushforwardEquiv a N α p)

/-- The forward map of the affine coefficient comparison is the original map along `a`. -/
theorem moduleCohomologyCoefficientAffineEquiv_apply (a : Y ⟶ X) [IsAffineHom a]
    (N : Y.Modules) [N.IsQuasicoherent] (M : X.Modules)
    (e : M ≅ (pushforward a).obj N) (α : A →+* Γ(X, ⊤)) (p : ℕ)
    (x : (moduleCohomologyFunctorOfHom X α p).obj M) :
    moduleCohomologyCoefficientAffineEquiv a N M e α p x =
      moduleCohomologyMapAlong a e.hom p x := by
  simp only [moduleCohomologyCoefficientAffineEquiv, LinearEquiv.trans_apply,
    Iso.toLinearEquiv_apply, CategoryTheory.Functor.mapIso_hom,
    moduleCohomologyFunctorOfHom_map_apply]
  change moduleCohomologyAffinePushforwardEquiv a N α p
    (Sheaf.H.map ((SheafOfModules.toSheaf X.ringCatSheaf).map e.hom) p x) = _
  rw [moduleCohomologyAffinePushforwardEquiv_apply]
  rw [← moduleCohomologyMapAlong_precomp, Category.comp_id]

/-- Naturality of a pair of linear equivalences for specified original module arrows.
The regular predicate keeps concrete geometric constructor comparisons atomic. -/
def cohomologyEquivNaturality {M N M' N' : ModuleCat.{u + 1} A}
    (e : M ≃ₗ[A] N) (e' : M' ≃ₗ[A] N') (c : N ⟶ N') (t : M ⟶ M') : Prop :=
  ∀ x, c (e x) = e' (t x)

/-- The affine coefficient equivalence is natural for the actual geometric
triangle map and the original coefficient arrow. All constructors are shared
with geometric specializations. -/
theorem moduleCohomologyCoefficientAffineEquiv_naturality
    (a : Y ⟶ X) (b : Z ⟶ X) (v : Z ⟶ Y) [IsAffineHom a] [IsAffineHom b]
    (h : v ≫ a = b) (N : Y.Modules) (N' : Z.Modules)
    [N.IsQuasicoherent] [N'.IsQuasicoherent] (M M' : X.Modules)
    (e : M ≅ (pushforward a).obj N) (e' : M' ≅ (pushforward b).obj N')
    (c : N ⟶ (pushforward v).obj N') (t : M ⟶ M')
    (hc : e.hom ≫ (pushforward a).map c ≫ (pushforwardComp v a).hom.app N' ≫
      (pushforwardCongr h).hom.app N' = t ≫ e'.hom)
    (α : A →+* Γ(X, ⊤))
    (hα : v.appTop.hom.comp (a.appTop.hom.comp α) = b.appTop.hom.comp α)
    (p : ℕ) :
    cohomologyEquivNaturality (moduleCohomologyCoefficientAffineEquiv a N M e α p)
      (moduleCohomologyCoefficientAffineEquiv b N' M' e' α p)
      (moduleCohomologyAlongHom v (a.appTop.hom.comp α) (b.appTop.hom.comp α) hα c p)
      ((moduleCohomologyFunctorOfHom X α p).map t) := by
  intro x
  rw [moduleCohomologyAlongHom_apply, moduleCohomologyCoefficientAffineEquiv_apply,
    moduleCohomologyCoefficientAffineEquiv_apply, moduleCohomologyFunctorOfHom_map_apply]
  exact moduleCohomologyMapAlong_triangle a b v h e.hom e'.hom c t hc p x

/-- Affine coefficient comparison on a genuine pullback triangle, using the
same original coefficient and pushforward arrow constructors on both sides. -/
theorem moduleCohomologyPullbackTriangleEquiv_naturality
    (a : Y ⟶ X) (b : Z ⟶ X) (v : Z ⟶ Y) [IsAffineHom a] [IsAffineHom b]
    (h : v ≫ a = b) (F : X.Modules) [F.IsQuasicoherent] (M M' : X.Modules)
    (e : M ≅ (pushforward a).obj ((pullback a).obj F))
    (e' : M' ≅ (pushforward b).obj ((pullback b).obj F)) (t : M ⟶ M')
    (hc : e.hom ≫ pullbackTrianglePushforwardMap F a v b h = t ≫ e'.hom)
    (α : A →+* Γ(X, ⊤))
    (hα : v.appTop.hom.comp (a.appTop.hom.comp α) = b.appTop.hom.comp α) (p : ℕ) :
    cohomologyEquivNaturality
      (moduleCohomologyCoefficientAffineEquiv a ((pullback a).obj F) M e α p)
      (moduleCohomologyCoefficientAffineEquiv b ((pullback b).obj F) M' e' α p)
      (moduleCohomologyAlongHom v (a.appTop.hom.comp α) (b.appTop.hom.comp α) hα
        (pullbackTriangleCoefficientMap F a v b h) p)
      ((moduleCohomologyFunctorOfHom X α p).map t) := by
  apply moduleCohomologyCoefficientAffineEquiv_naturality a b v h _ _ M M' e e'
    (pullbackTriangleCoefficientMap F a v b h) t _ α hα p
  simpa only [pullbackTrianglePushforwardMap, Category.assoc] using hc

end AlgebraicGeometry.Scheme.Cohomology
