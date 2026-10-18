/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Cohomology.Functoriality.Modules
public import Aglib.Topology.Sheaves.FreeAbelianPullback.Composition

/-!
# Composition of the original additive module coefficient mates

The native inverse-image coefficient adjoint to a module direct-image arrow
commutes with coefficient maps and composition. All comparisons use the
original module direct-image composition and the native additive pullback
adjunction. There is no flatness or quasicoherence premise.
-/

@[expose] public section

noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

namespace AlgebraicGeometry.Scheme.Cohomology

universe u

variable {X Y Z : Scheme.{u}}

/-- The original coefficient mate has its original additive adjunction formula. -/
theorem moduleCoefficientPullback_homEquiv (p : Y ⟶ X) {M : X.Modules} {N : Y.Modules}
    (φ : M ⟶ (Scheme.Modules.pushforward p).obj N) :
    (TopCat.Sheaf.pullbackPushforwardAdjunction AddCommGrpCat.{u} p.base).homEquiv _ _
        (moduleCoefficientPullback p φ) =
      (SheafOfModules.toSheaf X.ringCatSheaf).map φ ≫
        (modulePushforwardAddSheafIso p N).hom :=
  Equiv.apply_symm_apply _ _

/-- Postcomposing module coefficients preserves their original inverse-image mate. -/
theorem moduleCoefficientPullback_postcomp (p : Y ⟶ X)
    {M : X.Modules} {N P : Y.Modules}
    (φ : M ⟶ (Scheme.Modules.pushforward p).obj N) (ψ : N ⟶ P) :
    moduleCoefficientPullback p (φ ≫ (Scheme.Modules.pushforward p).map ψ) =
      moduleCoefficientPullback p φ ≫ (SheafOfModules.toSheaf Y.ringCatSheaf).map ψ := by
  apply ((TopCat.Sheaf.pullbackPushforwardAdjunction AddCommGrpCat.{u}
    p.base).homEquiv _ _).injective
  erw [moduleCoefficientPullback_homEquiv p (φ ≫ (Scheme.Modules.pushforward p).map ψ)]
  erw [(TopCat.Sheaf.pullbackPushforwardAdjunction AddCommGrpCat.{u}
    p.base).homEquiv_naturality_right, moduleCoefficientPullback_homEquiv p φ]
  rfl

/-- Precomposing module coefficients preserves their original inverse-image mate. -/
theorem moduleCoefficientPullback_precomp (p : Y ⟶ X)
    {M P : X.Modules} {N : Y.Modules} (μ : P ⟶ M)
    (φ : M ⟶ (Scheme.Modules.pushforward p).obj N) :
    moduleCoefficientPullback p (μ ≫ φ) =
      (zariskiPullback p).map ((SheafOfModules.toSheaf X.ringCatSheaf).map μ) ≫
        moduleCoefficientPullback p φ := by
  apply ((TopCat.Sheaf.pullbackPushforwardAdjunction AddCommGrpCat.{u}
    p.base).homEquiv _ _).injective
  erw [moduleCoefficientPullback_homEquiv p (μ ≫ φ)]
  erw [(TopCat.Sheaf.pullbackPushforwardAdjunction AddCommGrpCat.{u}
    p.base).homEquiv_naturality_left, moduleCoefficientPullback_homEquiv p φ]
  rfl

/-- Successive original module coefficient mates give the original mate for the
composite morphism under the native pullback-composition comparison. -/
theorem moduleCoefficientPullback_comp (p : Y ⟶ X) (q : Z ⟶ Y)
    {M : X.Modules} {N : Y.Modules} {P : Z.Modules}
    (φ : M ⟶ (Scheme.Modules.pushforward p).obj N)
    (ψ : N ⟶ (Scheme.Modules.pushforward q).obj P) :
    (TopCat.Sheaf.abelianPullbackCompIso p.base q.base).inv.app (moduleAddSheaf X M) ≫
        (zariskiPullback q).map (moduleCoefficientPullback p φ) ≫
          moduleCoefficientPullback q ψ =
      moduleCoefficientPullback (q ≫ p)
        (φ ≫ (Scheme.Modules.pushforward p).map ψ ≫
          (Scheme.Modules.pushforwardComp q p).hom.app P) := by
  apply (cancel_epi
    ((TopCat.Sheaf.abelianPullbackCompIso p.base q.base).hom.app (moduleAddSheaf X M))).mp
  simp only [Iso.hom_inv_id_app_assoc]
  apply ((TopCat.Sheaf.abelianPullbackCompAdjunction p.base q.base).homEquiv _ _).injective
  conv_rhs =>
    erw [TopCat.Sheaf.abelianPullbackCompIso_homEquiv p.base q.base]
    erw [moduleCoefficientPullback_homEquiv (q ≫ p)]
  dsimp only [TopCat.Sheaf.abelianPullbackCompAdjunction]
  erw [Adjunction.homEquiv_ofNatIsoRight_apply]
  change (TopCat.Sheaf.pullbackPushforwardAdjunction AddCommGrpCat.{u} p.base).homEquiv _ _
      ((TopCat.Sheaf.pullbackPushforwardAdjunction AddCommGrpCat.{u} q.base).homEquiv _ _
        ((zariskiPullback q).map (moduleCoefficientPullback p φ) ≫
          moduleCoefficientPullback q ψ)) = _
  erw [(TopCat.Sheaf.pullbackPushforwardAdjunction AddCommGrpCat.{u}
    q.base).homEquiv_naturality_left, moduleCoefficientPullback_homEquiv q ψ]
  erw [(TopCat.Sheaf.pullbackPushforwardAdjunction AddCommGrpCat.{u}
    p.base).homEquiv_naturality_right, moduleCoefficientPullback_homEquiv p φ]
  rfl

/-- Equal geometric morphisms give the same original coefficient mate, with the actual
module direct-image equality comparison. -/
theorem moduleCoefficientPullback_congr (p q : Y ⟶ X) (h : p = q)
    {M : X.Modules} {N : Y.Modules} (φ : M ⟶ (Scheme.Modules.pushforward p).obj N) :
    (eqToIso (congrArg (fun f : Y ⟶ X => zariskiPullback f) h)).hom.app
        (moduleAddSheaf X M) ≫
      moduleCoefficientPullback q (φ ≫ (Scheme.Modules.pushforwardCongr h).hom.app N) =
        moduleCoefficientPullback p φ := by
  subst q
  have he : (Scheme.Modules.pushforwardCongr (rfl : p = p)).hom.app N = 𝟙 _ := by
    apply Scheme.Modules.hom_ext
    intro W
    rw [Scheme.Modules.pushforwardCongr_hom_app_app]
    change N.presheaf.map (𝟙 _) = 𝟙 _
    exact N.presheaf.map_id _
  rw [he, Category.comp_id]
  change 𝟙 _ ≫ moduleCoefficientPullback p φ = _
  exact Category.id_comp _

/-- Postcomposing the actual module coefficient arrow gives the original coefficient
map on unchanged module cohomology. -/
theorem moduleCohomologyMapAlong_postcomp (p : Y ⟶ X)
    {M : X.Modules} {N P : Y.Modules}
    (φ : M ⟶ (Scheme.Modules.pushforward p).obj N) (ψ : N ⟶ P)
    (n : ℕ) (x : Sheaf.H.{u + 1} (moduleAddSheaf X M) n) :
    moduleCohomologyMapAlong p (φ ≫ (Scheme.Modules.pushforward p).map ψ) n x =
      Sheaf.H.map ((SheafOfModules.toSheaf Y.ringCatSheaf).map ψ) n
        (moduleCohomologyMapAlong p φ n x) := by
  dsimp only [moduleCohomologyMapAlong]
  rw [moduleCoefficientPullback_postcomp]
  change ((Abelian.Ext.mk₀ _).comp
      (x.mapExactFunctor (zariskiPullback p)) (Nat.zero_add n)).comp
        (Abelian.Ext.mk₀ (moduleCoefficientPullback p φ ≫
          (SheafOfModules.toSheaf Y.ringCatSheaf).map ψ)) (Nat.add_zero n) =
    (((Abelian.Ext.mk₀ _).comp
      (x.mapExactFunctor (zariskiPullback p)) (Nat.zero_add n)).comp
        (Abelian.Ext.mk₀ (moduleCoefficientPullback p φ)) (Nat.add_zero n)).comp
          (Abelian.Ext.mk₀ ((SheafOfModules.toSheaf Y.ringCatSheaf).map ψ)) (Nat.add_zero n)
  simp only [Abelian.Ext.comp_assoc_of_third_deg_zero, Abelian.Ext.mk₀_comp_mk₀]

/-- Precomposing the actual module coefficient arrow gives the original coefficient
map before the original geometric cohomology map. -/
theorem moduleCohomologyMapAlong_precomp (p : Y ⟶ X)
    {M P : X.Modules} {N : Y.Modules} (μ : P ⟶ M)
    (φ : M ⟶ (Scheme.Modules.pushforward p).obj N)
    (n : ℕ) (x : Sheaf.H.{u + 1} (moduleAddSheaf X P) n) :
    moduleCohomologyMapAlong p (μ ≫ φ) n x =
      moduleCohomologyMapAlong p φ n
        (Sheaf.H.map ((SheafOfModules.toSheaf X.ringCatSheaf).map μ) n x) := by
  dsimp only [moduleCohomologyMapAlong]
  rw [moduleCoefficientPullback_precomp]
  change ((Abelian.Ext.mk₀ _).comp
      (x.mapExactFunctor (zariskiPullback p)) (Nat.zero_add n)).comp
        (Abelian.Ext.mk₀ ((zariskiPullback p).map
          ((SheafOfModules.toSheaf X.ringCatSheaf).map μ) ≫
          moduleCoefficientPullback p φ)) (Nat.add_zero n) =
    ((Abelian.Ext.mk₀ _).comp
      ((x.comp (Abelian.Ext.mk₀ ((SheafOfModules.toSheaf X.ringCatSheaf).map μ))
        (Nat.add_zero n)).mapExactFunctor (zariskiPullback p)) (Nat.zero_add n)).comp
          (Abelian.Ext.mk₀ (moduleCoefficientPullback p φ)) (Nat.add_zero n)
  simp only [Abelian.Ext.mapExactFunctor_comp, Abelian.Ext.mapExactFunctor_mk₀,
    Abelian.Ext.comp_assoc_of_third_deg_zero, Abelian.Ext.mk₀_comp_mk₀]

/-- An original square of arbitrary module coefficient arrows gives the original
naturality square on unchanged additive cohomology. -/
theorem moduleCohomologyMapAlong_naturality (p : Y ⟶ X)
    {M M' : X.Modules} {N N' : Y.Modules}
    (φ : M ⟶ (Scheme.Modules.pushforward p).obj N)
    (φ' : M' ⟶ (Scheme.Modules.pushforward p).obj N')
    (μ : M ⟶ M') (ν : N ⟶ N')
    (h : μ ≫ φ' = φ ≫ (Scheme.Modules.pushforward p).map ν)
    (n : ℕ) (x : Sheaf.H.{u + 1} (moduleAddSheaf X M) n) :
    moduleCohomologyMapAlong p φ' n
        (Sheaf.H.map ((SheafOfModules.toSheaf X.ringCatSheaf).map μ) n x) =
      Sheaf.H.map ((SheafOfModules.toSheaf Y.ringCatSheaf).map ν) n
        (moduleCohomologyMapAlong p φ n x) := by
  rw [← moduleCohomologyMapAlong_precomp, h, moduleCohomologyMapAlong_postcomp]

end AlgebraicGeometry.Scheme.Cohomology
