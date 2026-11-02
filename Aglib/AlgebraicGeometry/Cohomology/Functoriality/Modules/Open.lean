/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Cohomology.Functoriality.Modules.Composition
public import Aglib.AlgebraicGeometry.Cohomology.MayerVietoris.Geometric.Coefficients
public import Aglib.AlgebraicGeometry.Cohomology.MayerVietoris.Geometric.Composition
public import Aglib.AlgebraicGeometry.Cohomology.MayerVietoris.GeometricTop

/-! # Original module coefficient arrows on native geometric open cohomology

The existing geometric open-Ext map respects original module coefficient
postcomposition, geometric composition and equality of morphisms. The
formulas retain native direct-image comparisons and actual preimage-open
transport, without introducing another cohomology map.
-/

@[expose] public section

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace Opposite

namespace CategoryTheory.Functor

open CategoryTheory.Abelian

universe i j k l u₀ v₀ u₁ v₁ w

variable {C : Type u₀} [Category.{v₀} C] [Abelian C] [HasExt.{w} C]
  {D : Type u₁} [Category.{v₁} D] [Abelian D] [HasExt.{w} D]
  {I : Type i} [Category.{j} I] {J : Type k} [Category.{l} J]

/-- Eliminate the original identity coefficient edge at the complete Ext-square
factory, before native module coefficients enter its four-map construction. -/
private theorem extDiagramCoefficientSquare_identity
    (L : C ⥤ D) [L.Additive] [PreservesFiniteLimits L] [PreservesFiniteColimits L]
    (F : I ⥤ C) (G : J ⥤ D) (H : I ⥤ J) (e : F ⋙ L ≅ H ⋙ G)
    {A : C} {B B' : D} (a : L.obj A ⟶ B) (a' : L.obj A ⟶ B')
    (g : B ⟶ B') (h : L.map (𝟙 A) ≫ a' = a ≫ g) (n : ℕ) :
    (L.extDiagramCoefficientSquare F G H e a a' (𝟙 A) g h n).f₂₄ =
      (L.extDiagramCoefficientSquare F G H e a a' (𝟙 A) g h n).f₁₃ ≫
        (L.extDiagramCoefficientSquare F G H e a a' (𝟙 A) g h n).f₃₄ := by
  have hs := (L.extDiagramCoefficientSquare F G H e a a' (𝟙 A) g h n).fac
  simpa only [extDiagramCoefficientSquare, Functor.map_id, Category.id_comp] using hs

end CategoryTheory.Functor

namespace TopCat.Sheaf

open CategoryTheory.Abelian

universe w

variable {X Y : TopCat.{u}}
  [HasExt.{w} (CategoryTheory.Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u})]
  [HasExt.{w} (CategoryTheory.Sheaf (Opens.grothendieckTopology Y) AddCommGrpCat.{u})]

attribute [local instance] reflectsLimits_of_reflectsIsomorphisms

local instance (p : Y ⟶ X) : (openCohomologyInverseImage p).IsLeftAdjoint :=
  (pullbackPushforwardAdjunction AddCommGrpCat.{u} p).isLeftAdjoint

local instance (p : Y ⟶ X) : RepresentablyFlat (Opens.map p) :=
  flat_of_preservesFiniteLimits _

local instance (p : Y ⟶ X) : PreservesFiniteLimits (openCohomologyInverseImage p) := by
  change PreservesFiniteLimits ((Opens.map p).sheafPullback AddCommGrpCat.{u} _ _)
  apply Functor.sheafPullbackConstruction.preservesFiniteLimits

local instance (p : Y ⟶ X) : (openCohomologyInverseImage p).Additive :=
  Functor.additive_of_preserves_binary_products _

private theorem openCohomologyCoefficientSquare_identity (p : Y ⟶ X)
    {A : CategoryTheory.Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}}
    {B B' : CategoryTheory.Sheaf (Opens.grothendieckTopology Y) AddCommGrpCat.{u}}
    (a : (openCohomologyInverseImage p).obj A ⟶ B)
    (a' : (openCohomologyInverseImage p).obj A ⟶ B') (g : B ⟶ B')
    (h : (openCohomologyInverseImage p).map (𝟙 A) ≫ a' = a ≫ g) (n : ℕ) :
    (openCohomologyCoefficientSquare p a a' (𝟙 A) g h n).f₂₄ =
      (openCohomologyCoefficientSquare p a a' (𝟙 A) g h n).f₁₃ ≫
        (openCohomologyCoefficientSquare p a a' (𝟙 A) g h n).f₃₄ :=
  (openCohomologyInverseImage p).extDiagramCoefficientSquare_identity
    (openFreeAbelianFunctor X) (openFreeAbelianFunctor Y) (Opens.map p)
    (openFreeAbelianPullbackIso p) a a' g h n

end TopCat.Sheaf

namespace AlgebraicGeometry.Scheme.Cohomology

variable {X Y Z : Scheme.{u}}

/-- The same complete original coefficient square for a module postcomposition. -/
abbrev modulePostcompositionCohomologySquare (p : Y ⟶ X)
    {M : X.Modules} {N P : Y.Modules}
    (φ : M ⟶ (Scheme.Modules.pushforward p).obj N) (ψ : N ⟶ P) (n : ℕ) :=
  zariskiCohomologyCoefficientSquare p (moduleCoefficientPullback p φ)
    (moduleCoefficientPullback p (φ ≫ (Scheme.Modules.pushforward p).map ψ))
    (𝟙 (moduleAddSheaf X M)) ((SheafOfModules.toSheaf Y.ringCatSheaf).map ψ)
    (by erw [CategoryTheory.Functor.map_id, Category.id_comp]
        exact moduleCoefficientPullback_postcomp p φ ψ) n

/-- Postcomposition respects the original open-cohomology maps. The projections
are the original two transfers and coefficient map from the same square. -/
theorem zariskiCohomologyOpenMap_module_postcomp (p : Y ⟶ X)
    {M : X.Modules} {N P : Y.Modules}
    (φ : M ⟶ (Scheme.Modules.pushforward p).obj N) (ψ : N ⟶ P) (n : ℕ) :
    (modulePostcompositionCohomologySquare p φ ψ n).f₂₄ =
      (modulePostcompositionCohomologySquare p φ ψ n).f₁₃ ≫
        (modulePostcompositionCohomologySquare p φ ψ n).f₃₄ :=
  TopCat.Sheaf.openCohomologyCoefficientSquare_identity p.base
    (moduleCoefficientPullback p φ)
    (moduleCoefficientPullback p (φ ≫ (Scheme.Modules.pushforward p).map ψ))
    ((SheafOfModules.toSheaf Y.ringCatSheaf).map ψ)
    (by erw [CategoryTheory.Functor.map_id, Category.id_comp]
        exact moduleCoefficientPullback_postcomp p φ ψ) n

/-- Successive original module coefficient maps compose with the actual native
module direct-image composition comparison. -/
theorem zariskiCohomologyOpenMap_module_comp_app (p : Y ⟶ X) (q : Z ⟶ Y)
    {M : X.Modules} {N : Y.Modules} {P : Z.Modules}
    (φ : M ⟶ (Scheme.Modules.pushforward p).obj N)
    (ψ : N ⟶ (Scheme.Modules.pushforward q).obj P) (n : ℕ) (U : X.Opensᵒᵖ) :
    (zariskiCohomologyOpenMap p (moduleAddSheaf X M) (moduleAddSheaf Y N)
        (moduleCoefficientPullback p φ) n).app U ≫
      (zariskiCohomologyOpenMap q (moduleAddSheaf Y N) (moduleAddSheaf Z P)
        (moduleCoefficientPullback q ψ) n).app ((Opens.map p.base).op.obj U) =
      (zariskiCohomologyOpenMap (q ≫ p) (moduleAddSheaf X M) (moduleAddSheaf Z P)
        (moduleCoefficientPullback (q ≫ p)
          (φ ≫ (Scheme.Modules.pushforward p).map ψ ≫
            (Scheme.Modules.pushforwardComp q p).hom.app P)) n).app U := by
  have H := zariskiCohomologyOpenMap_comp_app p q (moduleAddSheaf X M)
    (moduleAddSheaf Y N) (moduleAddSheaf Z P)
    (moduleCoefficientPullback p φ) (moduleCoefficientPullback q ψ) n U
  change (zariskiCohomologyOpenMap p (moduleAddSheaf X M) (moduleAddSheaf Y N)
      (moduleCoefficientPullback p φ) n).app U ≫
      (zariskiCohomologyOpenMap q (moduleAddSheaf Y N) (moduleAddSheaf Z P)
        (moduleCoefficientPullback q ψ) n).app ((Opens.map p.base).op.obj U) =
    (zariskiCohomologyOpenMap (q ≫ p) (moduleAddSheaf X M) (moduleAddSheaf Z P)
      ((TopCat.Sheaf.abelianPullbackCompIso p.base q.base).inv.app (moduleAddSheaf X M) ≫
        (zariskiPullback q).map (moduleCoefficientPullback p φ) ≫
          moduleCoefficientPullback q ψ) n).app U at H
  erw [moduleCoefficientPullback_comp p q φ ψ] at H
  exact H

/-- Equal geometric morphisms give the same native open-cohomology map, retaining the
actual module direct-image comparison and actual preimage-open equality transport. -/
theorem zariskiCohomologyOpenMap_module_congr_app (p q : Y ⟶ X) (h : p = q)
    {M : X.Modules} {N : Y.Modules} (φ : M ⟶ (Scheme.Modules.pushforward p).obj N)
    (n : ℕ) (U : X.Opensᵒᵖ) :
    (zariskiCohomologyOpenMap p (moduleAddSheaf X M) (moduleAddSheaf Y N)
        (moduleCoefficientPullback p φ) n).app U ≫
      ((moduleAddSheaf Y N).cohomologyPresheaf n).map
        (eqToHom (congrArg (fun f : Y ⟶ X => f ⁻¹ᵁ U.unop) h).symm).op =
      (zariskiCohomologyOpenMap q (moduleAddSheaf X M) (moduleAddSheaf Y N)
        (moduleCoefficientPullback q
          (φ ≫ (Scheme.Modules.pushforwardCongr h).hom.app N)) n).app U := by
  subst q
  have ha := moduleCoefficientPullback_congr p p (rfl : p = p) φ
  change 𝟙 _ ≫ moduleCoefficientPullback p
      (φ ≫ (Scheme.Modules.pushforwardCongr (rfl : p = p)).hom.app N) =
    moduleCoefficientPullback p φ at ha
  rw [Category.id_comp] at ha
  change (zariskiCohomologyOpenMap p (moduleAddSheaf X M) (moduleAddSheaf Y N)
      (moduleCoefficientPullback p φ) n).app U ≫
        ((moduleAddSheaf Y N).cohomologyPresheaf n).map (𝟙 _) = _
  erw [CategoryTheory.Functor.map_id, Category.comp_id]
  exact congrArg (fun a =>
    (zariskiCohomologyOpenMap p (moduleAddSheaf X M) (moduleAddSheaf Y N) a n).app U) ha.symm

/-- Successive original geometric maps on unchanged module cohomology compose with
actual coefficient arrows and the native direct-image composition comparison. -/
theorem moduleCohomologyMapAlong_comp (p : Y ⟶ X) (q : Z ⟶ Y)
    {M : X.Modules} {N : Y.Modules} {P : Z.Modules}
    (φ : M ⟶ (Scheme.Modules.pushforward p).obj N)
    (ψ : N ⟶ (Scheme.Modules.pushforward q).obj P)
    (n : ℕ) (x : Sheaf.H.{u + 1} (moduleAddSheaf X M) n) :
    moduleCohomologyMapAlong q ψ n (moduleCohomologyMapAlong p φ n x) =
      moduleCohomologyMapAlong (q ≫ p)
        (φ ≫ (Scheme.Modules.pushforward p).map ψ ≫
          (Scheme.Modules.pushforwardComp q p).hom.app P) n x := by
  obtain ⟨y, rfl⟩ := (sheafHPrimeTopAddEquiv X (moduleAddSheaf X M) n).surjective x
  dsimp only [moduleCohomologyMapAlong]
  rw [← sheafHPrimeTopAddEquiv_geometric p, ← sheafHPrimeTopAddEquiv_geometric q,
    ← sheafHPrimeTopAddEquiv_geometric (q ≫ p)]
  exact congrArg (sheafHPrimeTopAddEquiv Z (moduleAddSheaf Z P) n)
    (ConcreteCategory.congr_hom
      (zariskiCohomologyOpenMap_module_comp_app p q φ ψ n (op ⊤)) y)

end AlgebraicGeometry.Scheme.Cohomology
