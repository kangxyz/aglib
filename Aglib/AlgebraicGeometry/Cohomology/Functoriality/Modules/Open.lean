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

namespace AlgebraicGeometry.Scheme.Cohomology

variable {X Y Z : Scheme.{u}}

/-- Postcomposing an original module coefficient arrow gives the original coefficient map
on the unchanged native open-cohomology presheaf. -/
theorem zariskiCohomologyOpenMap_module_postcomp (p : Y ⟶ X)
    {M : X.Modules} {N P : Y.Modules}
    (φ : M ⟶ (Scheme.Modules.pushforward p).obj N) (ψ : N ⟶ P) (n : ℕ) :
    zariskiCohomologyOpenMap p (moduleAddSheaf X M) (moduleAddSheaf Y P)
        (moduleCoefficientPullback p (φ ≫ (Scheme.Modules.pushforward p).map ψ)) n =
      zariskiCohomologyOpenMap p (moduleAddSheaf X M) (moduleAddSheaf Y N)
          (moduleCoefficientPullback p φ) n ≫
        Functor.whiskerLeft (Opens.map p.base).op
          ((Sheaf.cohomologyPresheafFunctor.{u + 1} (Opens.grothendieckTopology Y) n).map
            ((SheafOfModules.toSheaf Y.ringCatSheaf).map ψ)) := by
  have H := zariskiCohomologyOpenMap_coefficients p (moduleCoefficientPullback p φ)
    (moduleCoefficientPullback p (φ ≫ (Scheme.Modules.pushforward p).map ψ))
    (𝟙 (moduleAddSheaf X M)) ((SheafOfModules.toSheaf Y.ringCatSheaf).map ψ)
    (by erw [CategoryTheory.Functor.map_id, Category.id_comp]
        exact moduleCoefficientPullback_postcomp p φ ψ) n
  simpa only [CategoryTheory.Functor.map_id, Category.id_comp] using H

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
