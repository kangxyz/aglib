/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Cohomology.BaseChange.HigherDirectImage.Nonflat.AffineRestriction
public import Aglib.AlgebraicGeometry.Cohomology.BaseChange.HigherDirectImage.Nonflat.ChartCoefficient
public import Aglib.AlgebraicGeometry.Cohomology.BaseChange.HigherDirectImage.Nonflat.OpenSquareComposition
public import Aglib.AlgebraicGeometry.Cohomology.BaseChange.Modules.Map.Composition

/-!
# Affine refinement through the original composite adjunction

Both restricted affine comparisons are transposed through the original
pullback and restriction adjunctions. Global sections of the original higher
direct image detect equality, and the original cohomology composition maps
supply the chart coefficient compatibility.
-/

@[expose] public section

noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

open CategoryTheory CategoryTheory.Limits CategoryTheory.Functor AlgebraicGeometry Opposite
open scoped TensorProduct ChangeOfRings

namespace AlgebraicGeometry.Scheme.Modules

open Cohomology

private theorem homEquiv_conjugate_precomp
    {C D : Type*} [Category C] [Category D]
    {L L' : C ⥤ D} {R R' : D ⥤ C}
    (A : L ⊣ R) (B : L' ⊣ R') (theta : L ⟶ L')
    (E : C) (F : D) (k : L'.obj E ⟶ F) :
    A.homEquiv E F (theta.app E ≫ k) =
      B.homEquiv E F k ≫ (conjugateEquiv B A theta).app F := by
  simp only [Adjunction.homEquiv_apply, Functor.map_comp, Category.assoc]
  rw [← reassoc_of% (unit_conjugateEquiv B A theta E),
    ← (conjugateEquiv B A theta).naturality k]

private theorem compositeHomEquiv_map_comp
    {C D E : Type*} [Category C] [Category D] [Category E]
    {L : C ⥤ D} {R : D ⥤ C} {P : D ⥤ E} {Q : E ⥤ D}
    (A : L ⊣ R) (B : P ⊣ Q) {X : C} {Y : D} {Z : E}
    (k : L.obj X ⟶ Y) (m : P.obj Y ⟶ Z) :
    (A.comp B).homEquiv X Z (P.map k ≫ m) =
      A.homEquiv X Y k ≫ R.map (B.homEquiv Y Z m) := by
  rw [Adjunction.comp_homEquiv]
  change A.homEquiv X _ (B.homEquiv _ _ (P.map k ≫ m)) = _
  rw [Adjunction.homEquiv_naturality_left, Adjunction.homEquiv_naturality_right]

private def pullbackMate {X Y : Scheme.{u}} (s : Y ⟶ X)
    {E : X.Modules} {F : Y.Modules} (k : (pullback s).obj E ⟶ F) :
    E ⟶ (pushforward s).obj F := (pullbackPushforwardAdjunction s).homEquiv E F k

private def restrictionMate {X Y : Scheme.{u}} (s : Y ⟶ X) [IsOpenImmersion s]
    {E : X.Modules} {F : Y.Modules} (k : E.restrict s ⟶ F) :
    E ⟶ (pushforward s).obj F := (restrictAdjunction s).homEquiv E F k

private def pullbackRestrictionMate {X Y Z : Scheme.{u}} (s : Y ⟶ X) (t : Z ⟶ Y)
    [IsOpenImmersion t] {E : X.Modules} {G : Z.Modules}
    (k : ((pullback s).obj E).restrict t ⟶ G) :
    E ⟶ (pushforward s).obj ((pushforward t).obj G) :=
  ((pullbackPushforwardAdjunction s).comp (restrictAdjunction t)).homEquiv E G k

private theorem pullbackRestrictionMate_map_comp_top
    {X Y Z : Scheme.{u}} (s : Y ⟶ X) (t : Z ⟶ Y) [IsOpenImmersion t]
    {E : X.Modules} {F : Y.Modules} {G : Z.Modules}
    (k : (pullback s).obj E ⟶ F) (m : F.restrict t ⟶ G)
    (x : E.presheaf.obj (op ⊤)) :
    (pullbackRestrictionMate s t ((restrictFunctor t).map k ≫ m)).app ⊤ x =
      (restrictionMate t m).app ⊤ ((pullbackMate s k).app ⊤ x) := by
  have h := compositeHomEquiv_map_comp
    (pullbackPushforwardAdjunction s) (restrictAdjunction t) k m
  exact congrArg (fun h => (h.app ⊤) x) h

private theorem restrictionPullbackMate_map_comp_top
    {X Y Z : Scheme.{u}} (r : Y ⟶ X) (s : Z ⟶ Y) [IsOpenImmersion r]
    {E : X.Modules} {F : Y.Modules} {G : Z.Modules}
    (k : E.restrict r ⟶ F) (m : (pullback s).obj F ⟶ G)
    (x : E.presheaf.obj (op ⊤)) :
    (((restrictAdjunction r).comp (pullbackPushforwardAdjunction s)).homEquiv E G
        ((pullback s).map k ≫ m)).app ⊤ x =
      (pullbackMate s m).app ⊤ ((restrictionMate r k).app ⊤ x) := by
  have h := compositeHomEquiv_map_comp
    (restrictAdjunction r) (pullbackPushforwardAdjunction s) k m
  exact congrArg (fun h => (h.app ⊤) x) h

private theorem affineMap_pullbackMate_top
    {R S : CommRingCat.{u}} {X Y : Scheme.{u}}
    (p : Y ⟶ X) (b : Y ⟶ Spec S) (f : X ⟶ Spec R) (σ : R ⟶ S)
    [QuasiCompact f] [QuasiSeparated f] [QuasiCompact b] [QuasiSeparated b]
    (hp : p ≫ f = b ≫ Spec.map σ)
    {M : X.Modules} {N : Y.Modules} [M.IsQuasicoherent] [N.IsQuasicoherent]
    (ψ : M ⟶ (pushforward p).obj N) (n : ℕ)
    (x : moduleSpecΓFunctor.obj (((pushforward f).rightDerived n).obj M)) :
    moduleHigherDirectImageAffineSectionsLinearEquiv b N (injectiveResolution N) n
        ((pullbackMate (Spec.map σ) (higherDirectImageAffineMap p b f σ hp ψ n)).app ⊤ x) =
      moduleCohomologyMapAlong p ψ n
        (moduleHigherDirectImageAffineSectionsLinearEquiv f M (injectiveResolution M) n x) := by
  let := moduleHigherDirectImageAffine_isQuasicoherent f M n
  have h := higherDirectImageAffineMap_one_tmul p b f σ hp ψ n x
  dsimp only at h
  rw [affinePullbackGlobalSectionsIso_one_tmul] at h
  exact h

private theorem openRestriction_restrictionMate_top
    {R S : CommRingCat.{u}} {X Y : Scheme.{u}}
    (a : Y ⟶ X) (b : Y ⟶ Spec S) (f : X ⟶ Spec R) (ρ : R ⟶ S)
    [QuasiCompact f] [QuasiSeparated f]
    [IsOpenImmersion a] [IsOpenImmersion (Spec.map ρ)]
    (h : IsPullback a b f (Spec.map ρ))
    (M : X.Modules) [M.IsQuasicoherent] (n : ℕ)
    (x : (moduleSpecΓFunctor (R := R)).obj (((pushforward f).rightDerived n).obj M)) :
    let : QuasiCompact b := MorphismProperty.of_isPullback h inferInstance
    let : QuasiSeparated b := MorphismProperty.of_isPullback h inferInstance
    moduleHigherDirectImageAffineSectionsLinearEquiv b (M.restrict a)
        (injectiveResolution (M.restrict a)) n
        ((restrictionMate
          (E := ((pushforward f).rightDerived n).obj M)
          (F := ((pushforward b).rightDerived n).obj (M.restrict a)) (Spec.map ρ)
          ((higherDirectImageOpenRestrictionIso a b f (Spec.map ρ) h n).hom.app M)).app ⊤ x) =
      moduleCohomologyMapAlong a ((restrictAdjunction a).unit.app M) n
        (moduleHigherDirectImageAffineSectionsLinearEquiv f M (injectiveResolution M) n x) := by
  let : QuasiCompact b := MorphismProperty.of_isPullback h inferInstance
  let : QuasiSeparated b := MorphismProperty.of_isPullback h inferInstance
  exact moduleHigherDirectImageAffineSectionsLinearEquiv_openRestriction a b f ρ h M
    (injectiveResolution M) (injectiveResolution (M.restrict a)) n x

private theorem moduleCohomologyMapAlong_congr_triangle
    {X Y : Scheme.{u}} (p q : Y ⟶ X) (h : p = q)
    {M : X.Modules} {N : Y.Modules}
    (φ : M ⟶ (pushforward p).obj N) (φ' : M ⟶ (pushforward q).obj N)
    (hφ : φ ≫ (pushforwardCongr h).hom.app N = φ')
    (n : ℕ) (x : Sheaf.H.{u + 1} (moduleAddSheaf X M) n) :
    moduleCohomologyMapAlong p φ n x = moduleCohomologyMapAlong q φ' n x := by
  subst q
  have hi : (pushforwardCongr (rfl : p = p)).hom.app N = 𝟙 _ := by
    apply Scheme.Modules.hom_ext
    intro U
    rw [pushforwardCongr_hom_app_app]
    change N.presheaf.map (𝟙 _) = 𝟙 _
    exact N.presheaf.map_id _
  rw [hi, Category.comp_id] at hφ
  subst φ'
  rfl

private theorem affineRefinementConjugate_app_top
    {T V U X : Scheme.{u}}
    (t : T ⟶ V) (s0 : T ⟶ U) (s : V ⟶ X) (r : U ⟶ X)
    [IsOpenImmersion t] [IsOpenImmersion r] (h : t ≫ s = s0 ≫ r)
    (G : T.Modules) :
    ((conjugateEquiv
        ((restrictAdjunction r).comp (pullbackPushforwardAdjunction s0))
        ((pullbackPushforwardAdjunction s).comp (restrictAdjunction t))
        (pullbackOpenSquare t s0 s r h).hom).app G).app (⊤ : X.Opens) =
      𝟙 (Γ(G, (⊤ : T.Opens))) := by
  rw [pullbackOpenSquare_conjugate_hom]
  simp only [NatTrans.comp_app, Hom.comp_app,
    pushforwardComp_hom_app_app, pushforwardComp_inv_app_app,
    pushforwardCongr_inv_app_app, Category.id_comp, Category.comp_id]
  change G.presheaf.map (𝟙 (op (⊤ : T.Opens))) = 𝟙 _
  exact G.presheaf.map_id _


private theorem openSquareMate_top
    {T V U X : Scheme.{u}}
    (t : T ⟶ V) (s₀ : T ⟶ U) (s : V ⟶ X) (r : U ⟶ X)
    [IsOpenImmersion t] [IsOpenImmersion r] (h : t ≫ s = s₀ ≫ r)
    (E : X.Modules) (G : T.Modules)
    (k : (pullback s₀).obj (E.restrict r) ⟶ G) (x : E.presheaf.obj (op ⊤)) :
    (pullbackRestrictionMate s t ((pullbackOpenSquare t s₀ s r h).hom.app E ≫ k)).app ⊤ x =
      (((restrictAdjunction r).comp (pullbackPushforwardAdjunction s₀)).homEquiv E G k).app
        ⊤ x := by
  have hm := homEquiv_conjugate_precomp
    ((pullbackPushforwardAdjunction s).comp (restrictAdjunction t))
    ((restrictAdjunction r).comp (pullbackPushforwardAdjunction s₀))
    (pullbackOpenSquare t s₀ s r h).hom E G k
  have hx := congrArg
    (fun φ : E ⟶ (pushforward s).obj ((pushforward t).obj G) => (φ.app ⊤) x) hm
  simp only [Hom.comp_app, ConcreteCategory.comp_apply] at hx
  rw [affineRefinementConjugate_app_top] at hx
  exact hx

private theorem openSquareMate_map_comp_top
    {T V U X : Scheme.{u}}
    (t : T ⟶ V) (s₀ : T ⟶ U) (s : V ⟶ X) (r : U ⟶ X)
    [IsOpenImmersion t] [IsOpenImmersion r] (h : t ≫ s = s₀ ≫ r)
    (E : X.Modules) (F : U.Modules) (G : T.Modules)
    (k : E.restrict r ⟶ F) (m : (pullback s₀).obj F ⟶ G)
    (x : E.presheaf.obj (op ⊤)) :
    (pullbackRestrictionMate s t
        ((pullbackOpenSquare t s₀ s r h).hom.app E ≫ (pullback s₀).map k ≫ m)).app ⊤ x =
      (pullbackMate s₀ m).app ⊤ ((restrictionMate r k).app ⊤ x) :=
  (openSquareMate_top t s₀ s r h E G ((pullback s₀).map k ≫ m) x).trans
    (restrictionPullbackMate_map_comp_top r s₀ k m x)


private theorem chartCohomology_naturality
    {X Y X₀ Y₀ : Scheme.{u}}
    (p : Y ⟶ X) (a : X₀ ⟶ X) (c : Y₀ ⟶ Y) (q : Y₀ ⟶ X₀)
    [IsOpenImmersion a] [IsOpenImmersion c] (hq : q ≫ a = c ≫ p)
    {M : X.Modules} {N : Y.Modules} (ψ : M ⟶ (pushforward p).obj N)
    (n : ℕ) (x : Sheaf.H.{u + 1} (moduleAddSheaf X M) n) :
    moduleCohomologyMapAlong c ((restrictAdjunction c).unit.app N) n
        (moduleCohomologyMapAlong p ψ n x) =
      moduleCohomologyMapAlong q (Nonflat.chartCoefficient p a c q hq ψ) n
        (moduleCohomologyMapAlong a ((restrictAdjunction a).unit.app M) n x) := by
  let ψ₀ := Nonflat.chartCoefficient p a c q hq ψ
  let ψ₁ := ψ ≫ (pushforward p).map ((restrictAdjunction c).unit.app N) ≫
    (pushforwardComp c p).hom.app (N.restrict c)
  let ψ₂ := (restrictAdjunction a).unit.app M ≫ (pushforward a).map ψ₀ ≫
    (pushforwardComp q a).hom.app (N.restrict c)
  have hψ : ψ₁ ≫ (pushforwardCongr hq.symm).hom.app (N.restrict c) = ψ₂ := by
    have h := congrArg (fun k => k ≫ (pushforwardComp q a).hom.app (N.restrict c))
      (Nonflat.chartCoefficient_unit p a c q hq ψ)
    simpa only [ψ₁, ψ₂, ψ₀, Category.assoc, Iso.inv_hom_id_app, Category.comp_id]
      using h.symm
  exact (moduleCohomologyMapAlong_comp p c ψ ((restrictAdjunction c).unit.app N) n x).trans
    ((moduleCohomologyMapAlong_congr_triangle (c ≫ p) (q ≫ a) hq.symm ψ₁ ψ₂ hψ n x).trans
      (moduleCohomologyMapAlong_comp a q ((restrictAdjunction a).unit.app M) ψ₀ n x).symm)

private theorem affineRefinement_left_sections
    {R S S₀ : CommRingCat.{u}} {X Y Y₀ : Scheme.{u}}
    (p : Y ⟶ X) (f : X ⟶ Spec R) (b : Y ⟶ Spec S) (σ : R ⟶ S)
    (hp : p ≫ f = b ≫ Spec.map σ)
    (c : Y₀ ⟶ Y) (b₀ : Y₀ ⟶ Spec S₀) (τ : S ⟶ S₀)
    [IsOpenImmersion c] [IsOpenImmersion (Spec.map τ)]
    (hC : IsPullback c b₀ b (Spec.map τ))
    [QuasiCompact f] [QuasiSeparated f] [QuasiCompact b] [QuasiSeparated b]
    {M : X.Modules} {N : Y.Modules} [M.IsQuasicoherent] [N.IsQuasicoherent]
    (ψ : M ⟶ (pushforward p).obj N) (n : ℕ)
    (x : (moduleSpecΓFunctor (R := R)).obj (((pushforward f).rightDerived n).obj M)) :
    let : QuasiCompact b₀ := MorphismProperty.of_isPullback hC inferInstance
    let : QuasiSeparated b₀ := MorphismProperty.of_isPullback hC inferInstance
    moduleHigherDirectImageAffineSectionsLinearEquiv b₀ (N.restrict c)
        (injectiveResolution (N.restrict c)) n
        ((pullbackRestrictionMate
          (E := ((pushforward f).rightDerived n).obj M)
          (G := ((pushforward b₀).rightDerived n).obj (N.restrict c))
          (Spec.map σ) (Spec.map τ)
          ((restrictFunctor (Spec.map τ)).map (higherDirectImageAffineMap p b f σ hp ψ n) ≫
            (higherDirectImageOpenRestrictionIso c b₀ b (Spec.map τ) hC n).hom.app N)).app ⊤ x) =
      moduleCohomologyMapAlong c ((restrictAdjunction c).unit.app N) n
        (moduleCohomologyMapAlong p ψ n
          (moduleHigherDirectImageAffineSectionsLinearEquiv f M (injectiveResolution M) n x)) := by
  let : QuasiCompact b₀ := MorphismProperty.of_isPullback hC inferInstance
  let : QuasiSeparated b₀ := MorphismProperty.of_isPullback hC inferInstance
  let A := higherDirectImageAffineMap p b f σ hp ψ n
  let uC : ((((pushforward b).rightDerived n).obj N).restrict (Spec.map τ)) ⟶
      ((pushforward b₀).rightDerived n).obj (N.restrict c) :=
    (higherDirectImageOpenRestrictionIso c b₀ b (Spec.map τ) hC n).hom.app N
  let y := (pullbackMate (Spec.map σ) A).app ⊤ x
  have h₁ := pullbackRestrictionMate_map_comp_top (Spec.map σ) (Spec.map τ)
    (E := ((pushforward f).rightDerived n).obj M)
    (F := ((pushforward b).rightDerived n).obj N)
    (G := ((pushforward b₀).rightDerived n).obj (N.restrict c)) A uC x
  exact (congrArg (moduleHigherDirectImageAffineSectionsLinearEquiv b₀ (N.restrict c)
      (injectiveResolution (N.restrict c)) n) h₁).trans
    ((openRestriction_restrictionMate_top c b₀ b τ hC N n y).trans
      (congrArg (moduleCohomologyMapAlong c ((restrictAdjunction c).unit.app N) n)
        (affineMap_pullbackMate_top p b f σ hp ψ n x)))

set_option maxRecDepth 2000 in
set_option maxHeartbeats 800000 in
-- Native section-equivalence conversion exhausted the standard kernel budget.
-- Both the comparison maps and their original scalar actions are retained.
private theorem affineRefinement_right_sections
    {R S R₀ S₀ : CommRingCat.{u}} {X X₀ Y₀ : Scheme.{u}}
    (a : X₀ ⟶ X) (f : X ⟶ Spec R) (f₀ : X₀ ⟶ Spec R₀) (ρ : R ⟶ R₀)
    [IsOpenImmersion a] [IsOpenImmersion (Spec.map ρ)]
    (hA : IsPullback a f₀ f (Spec.map ρ))
    (q : Y₀ ⟶ X₀) (b₀ : Y₀ ⟶ Spec S₀) (σ₀ : R₀ ⟶ S₀)
    (hp₀ : q ≫ f₀ = b₀ ≫ Spec.map σ₀) (σ : R ⟶ S) (τ : S ⟶ S₀)
    [IsOpenImmersion (Spec.map τ)]
    (hb : Spec.map τ ≫ Spec.map σ = Spec.map σ₀ ≫ Spec.map ρ)
    [QuasiCompact f] [QuasiSeparated f] [QuasiCompact b₀] [QuasiSeparated b₀]
    {M : X.Modules} {N₀ : Y₀.Modules} [M.IsQuasicoherent] [N₀.IsQuasicoherent]
    (ψ₀ : M.restrict a ⟶ (pushforward q).obj N₀) (n : ℕ)
    (x : (moduleSpecΓFunctor (R := R)).obj (((pushforward f).rightDerived n).obj M)) :
    let : QuasiCompact f₀ := MorphismProperty.of_isPullback hA inferInstance
    let : QuasiSeparated f₀ := MorphismProperty.of_isPullback hA inferInstance
    moduleHigherDirectImageAffineSectionsLinearEquiv b₀ N₀ (injectiveResolution N₀) n
        ((pullbackRestrictionMate
          (E := ((pushforward f).rightDerived n).obj M)
          (G := ((pushforward b₀).rightDerived n).obj N₀) (Spec.map σ) (Spec.map τ)
          ((pullbackOpenSquare (Spec.map τ) (Spec.map σ₀) (Spec.map σ) (Spec.map ρ) hb).hom.app
              (((pushforward f).rightDerived n).obj M) ≫
            (pullback (Spec.map σ₀)).map
              ((higherDirectImageOpenRestrictionIso a f₀ f (Spec.map ρ) hA n).hom.app M) ≫
            higherDirectImageAffineMap q b₀ f₀ σ₀ hp₀ ψ₀ n)).app ⊤ x) =
      moduleCohomologyMapAlong q ψ₀ n
        (moduleCohomologyMapAlong a ((restrictAdjunction a).unit.app M) n
          (moduleHigherDirectImageAffineSectionsLinearEquiv f M (injectiveResolution M) n x)) := by
  let : QuasiCompact f₀ := MorphismProperty.of_isPullback hA inferInstance
  let : QuasiSeparated f₀ := MorphismProperty.of_isPullback hA inferInstance
  let E := ((pushforward f).rightDerived n).obj M
  let E₀ := ((pushforward f₀).rightDerived n).obj (M.restrict a)
  let G := ((pushforward b₀).rightDerived n).obj N₀
  let uA : E.restrict (Spec.map ρ) ⟶ E₀ :=
    (higherDirectImageOpenRestrictionIso a f₀ f (Spec.map ρ) hA n).hom.app M
  let A₀ := higherDirectImageAffineMap q b₀ f₀ σ₀ hp₀ ψ₀ n
  let x₀ := (restrictionMate (E := E) (F := E₀) (Spec.map ρ) uA).app ⊤ x
  have h₁ := openSquareMate_map_comp_top
    (Spec.map τ) (Spec.map σ₀) (Spec.map σ) (Spec.map ρ) hb E E₀ G uA A₀ x
  exact (congrArg (moduleHigherDirectImageAffineSectionsLinearEquiv b₀ N₀
      (injectiveResolution N₀) n) h₁).trans
    ((affineMap_pullbackMate_top (M := M.restrict a) (N := N₀) q b₀ f₀ σ₀ hp₀ ψ₀ n x₀).trans
      (congrArg (moduleCohomologyMapAlong q ψ₀ n)
        (openRestriction_restrictionMate_top a f₀ f ρ hA M n x)))

private theorem affineHigherImage_isQuasicoherent
    {R : CommRingCat.{u}} {X : Scheme.{u}} (f : X ⟶ Spec R)
    [QuasiCompact f] [QuasiSeparated f] (M : X.Modules) [M.IsQuasicoherent] (n : ℕ) :
    (((pushforward f).rightDerived n).obj M).IsQuasicoherent :=
  moduleHigherDirectImageAffine_isQuasicoherent f M n

private def affineSectionsEvaluation
    {R : CommRingCat.{u}} {X : Scheme.{u}} (f : X ⟶ Spec R)
    [QuasiCompact f] [QuasiSeparated f] (M : X.Modules) [M.IsQuasicoherent] (n : ℕ) :
    moduleSpecΓFunctor.obj (((pushforward f).rightDerived n).obj M) →
      Sheaf.H.{u + 1} (moduleAddSheaf X M) n :=
  moduleHigherDirectImageAffineSectionsLinearEquiv f M (injectiveResolution M) n

private theorem affineSectionsEvaluation_injective
    {R : CommRingCat.{u}} {X : Scheme.{u}} (f : X ⟶ Spec R)
    [QuasiCompact f] [QuasiSeparated f] (M : X.Modules) [M.IsQuasicoherent] (n : ℕ) :
    Function.Injective (affineSectionsEvaluation f M n) :=
  (moduleHigherDirectImageAffineSectionsLinearEquiv f M (injectiveResolution M) n).injective

private theorem pullbackRestrictionMap_eq_of_top_eval
    {R S : CommRingCat.{u}} {Y : Scheme.{u}}
    (s : Y ⟶ Spec R) (t : Spec S ⟶ Y) [IsOpenImmersion t]
    (E : (Spec R).Modules) [E.IsQuasicoherent] (G : (Spec S).Modules)
    (k l : ((pullback s).obj E).restrict t ⟶ G)
    {H : Type*} (ell : (moduleSpecΓFunctor (R := S)).obj G → H) (hell : Function.Injective ell)
    (h : ∀ x : moduleSpecΓFunctor.obj E,
      ell ((pullbackRestrictionMate s t k).app ⊤ x) =
        ell ((pullbackRestrictionMate s t l).app ⊤ x)) : k = l := by
  apply (((pullbackPushforwardAdjunction s).comp (restrictAdjunction t)).homEquiv E G).injective
  apply hom_eq_of_globalSections_eq
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  apply hell
  exact h x

private theorem comp_inv_three_of_comp_eq
    {C : Type*} [Category C] {A B C₀ C₁ D : C}
    (f : A ⟶ B) (g₀ : A ⟶ C₀) (g₁ : C₀ ⟶ C₁) (g₂ : C₁ ⟶ D)
    (r : B ⟶ D) (i : D ⟶ B) (hr : r ≫ i = 𝟙 B)
    (h : f ≫ r = g₀ ≫ g₁ ≫ g₂) : f = g₀ ≫ g₁ ≫ g₂ ≫ i := by
  calc
    f = (f ≫ r) ≫ i := by rw [Category.assoc, hr, Category.comp_id]
    _ = (g₀ ≫ g₁ ≫ g₂) ≫ i := congrArg (fun k => k ≫ i) h
    _ = _ := by simp only [Category.assoc]

private theorem pullbackRestrictionMap_eq_iso_of_top_eval
    {R S : CommRingCat.{u}} {Y : Scheme.{u}}
    (s : Y ⟶ Spec R) (t : Spec S ⟶ Y) [IsOpenImmersion t]
    (E : (Spec R).Modules) [E.IsQuasicoherent] (G : (Spec S).Modules)
    {F F₀ F₁ : (Spec S).Modules}
    (L : ((pullback s).obj E).restrict t ⟶ F)
    (O : ((pullback s).obj E).restrict t ⟶ F₀)
    (g₁ : F₀ ⟶ F₁) (g₂ : F₁ ⟶ G) (rC : F ⟶ G) (iC : G ⟶ F)
    (hrC : rC ≫ iC = 𝟙 F)
    {H : Type*} (ell : (moduleSpecΓFunctor (R := S)).obj G → H) (hell : Function.Injective ell)
    (h : ∀ x : moduleSpecΓFunctor.obj E,
      ell ((pullbackRestrictionMate s t (L ≫ rC)).app ⊤ x) =
        ell ((pullbackRestrictionMate s t (O ≫ g₁ ≫ g₂)).app ⊤ x)) :
    L = O ≫ g₁ ≫ g₂ ≫ iC :=
  comp_inv_three_of_comp_eq L O g₁ g₂ rC iC hrC
    (pullbackRestrictionMap_eq_of_top_eval s t E G (L ≫ rC)
      (O ≫ g₁ ≫ g₂) ell hell h)

set_option maxRecDepth 2000 in
-- The native pointwise comparison retains the original higher-image section types.
private theorem affineRefinement_mate_evaluations_eq
    {R S R₀ S₀ : CommRingCat.{u}} {X Y X₀ Y₀ : Scheme.{u}}
    (p : Y ⟶ X) (f : X ⟶ Spec R) (b : Y ⟶ Spec S) (σ : R ⟶ S)
    (hp : p ≫ f = b ≫ Spec.map σ)
    (a : X₀ ⟶ X) (c : Y₀ ⟶ Y) (q : Y₀ ⟶ X₀)
    (f₀ : X₀ ⟶ Spec R₀) (b₀ : Y₀ ⟶ Spec S₀)
    (ρ : R ⟶ R₀) (τ : S ⟶ S₀) (σ₀ : R₀ ⟶ S₀)
    [IsOpenImmersion a] [IsOpenImmersion c]
    [IsOpenImmersion (Spec.map ρ)] [IsOpenImmersion (Spec.map τ)]
    (hA : IsPullback a f₀ f (Spec.map ρ))
    (hC : IsPullback c b₀ b (Spec.map τ))
    (hq : q ≫ a = c ≫ p) (hp₀ : q ≫ f₀ = b₀ ≫ Spec.map σ₀)
    (hb : Spec.map τ ≫ Spec.map σ = Spec.map σ₀ ≫ Spec.map ρ)
    [QuasiCompact f] [QuasiSeparated f] [QuasiCompact b] [QuasiSeparated b]
    [QuasiCompact f₀] [QuasiSeparated f₀] [QuasiCompact b₀] [QuasiSeparated b₀]
    {M : X.Modules} {N : Y.Modules} [M.IsQuasicoherent] [N.IsQuasicoherent]
    (ψ : M ⟶ (pushforward p).obj N) (n : ℕ)
    (x : (moduleSpecΓFunctor (R := R)).obj (((pushforward f).rightDerived n).obj M)) :
    affineSectionsEvaluation (R := S₀) b₀ (N.restrict c) n
        ((pullbackRestrictionMate
          (E := ((pushforward f).rightDerived n).obj M)
          (G := ((pushforward b₀).rightDerived n).obj (N.restrict c))
          (Spec.map σ) (Spec.map τ)
          ((restrictFunctor (Spec.map τ)).map (higherDirectImageAffineMap p b f σ hp ψ n) ≫
            (higherDirectImageOpenRestrictionIso c b₀ b (Spec.map τ) hC n).hom.app N)).app ⊤ x) =
      affineSectionsEvaluation (R := S₀) b₀ (N.restrict c) n
        ((pullbackRestrictionMate
          (E := ((pushforward f).rightDerived n).obj M)
          (G := ((pushforward b₀).rightDerived n).obj (N.restrict c))
          (Spec.map σ) (Spec.map τ)
          ((pullbackOpenSquare (Spec.map τ) (Spec.map σ₀) (Spec.map σ) (Spec.map ρ) hb).hom.app
              (((pushforward f).rightDerived n).obj M) ≫
            (pullback (Spec.map σ₀)).map
              ((higherDirectImageOpenRestrictionIso a f₀ f (Spec.map ρ) hA n).hom.app M) ≫
            higherDirectImageAffineMap (M := M.restrict a) (N := N.restrict c)
              q b₀ f₀ σ₀ hp₀ (Nonflat.chartCoefficient p a c q hq ψ) n)).app ⊤ x) := by
  exact (affineRefinement_left_sections (M := M) (N := N) p f b σ hp c b₀ τ hC ψ n x).trans
    ((chartCohomology_naturality p a c q hq ψ n
      (moduleHigherDirectImageAffineSectionsLinearEquiv f M (injectiveResolution M) n x)).trans
      (affineRefinement_right_sections (M := M) (N₀ := N.restrict c)
        a f f₀ ρ hA q b₀ σ₀ hp₀ σ τ hb (Nonflat.chartCoefficient p a c q hq ψ) n x).symm)

set_option maxRecDepth 2000 in
set_option maxHeartbeats 800000 in
-- The native final specialization exceeded the standard kernel budget.
/-- The actual affine higher-image comparison commutes with refinement of both affine
charts, through the original composite adjunction and original cohomology maps. -/
theorem higherDirectImageAffineMap_restrict
    {R S R₀ S₀ : CommRingCat.{u}} {X Y X₀ Y₀ : Scheme.{u}}
    (p : Y ⟶ X) (f : X ⟶ Spec R) (b : Y ⟶ Spec S) (σ : R ⟶ S)
    (hp : p ≫ f = b ≫ Spec.map σ)
    (a : X₀ ⟶ X) (c : Y₀ ⟶ Y) (q : Y₀ ⟶ X₀)
    (f₀ : X₀ ⟶ Spec R₀) (b₀ : Y₀ ⟶ Spec S₀)
    (ρ : R ⟶ R₀) (τ : S ⟶ S₀) (σ₀ : R₀ ⟶ S₀)
    [IsOpenImmersion a] [IsOpenImmersion c]
    [IsOpenImmersion (Spec.map ρ)] [IsOpenImmersion (Spec.map τ)]
    (hA : IsPullback a f₀ f (Spec.map ρ))
    (hC : IsPullback c b₀ b (Spec.map τ))
    (hq : q ≫ a = c ≫ p) (hp₀ : q ≫ f₀ = b₀ ≫ Spec.map σ₀)
    (hb : Spec.map τ ≫ Spec.map σ = Spec.map σ₀ ≫ Spec.map ρ)
    [QuasiCompact f] [QuasiSeparated f] [QuasiCompact b] [QuasiSeparated b]
    {M : X.Modules} {N : Y.Modules} [M.IsQuasicoherent] [N.IsQuasicoherent]
    (ψ : M ⟶ (pushforward p).obj N) (n : ℕ) :
    let : QuasiCompact f₀ :=
      MorphismProperty.of_isPullback (P := @QuasiCompact) hA inferInstance
    let : QuasiSeparated f₀ :=
      MorphismProperty.of_isPullback (P := @QuasiSeparated) hA inferInstance
    let : QuasiCompact b₀ :=
      MorphismProperty.of_isPullback (P := @QuasiCompact) hC inferInstance
    let : QuasiSeparated b₀ :=
      MorphismProperty.of_isPullback (P := @QuasiSeparated) hC inferInstance
    (restrictFunctor (Spec.map τ)).map
        (higherDirectImageAffineMap p b f σ hp ψ n) =
      (pullbackOpenSquare (Spec.map τ) (Spec.map σ₀) (Spec.map σ)
          (Spec.map ρ) hb).hom.app (((pushforward f).rightDerived n).obj M) ≫
        (pullback (Spec.map σ₀)).map
          ((higherDirectImageOpenRestrictionIso a f₀ f (Spec.map ρ) hA n).hom.app M) ≫
        higherDirectImageAffineMap (M := M.restrict a) (N := N.restrict c)
          q b₀ f₀ σ₀ hp₀ (Nonflat.chartCoefficient p a c q hq ψ) n ≫
        (higherDirectImageOpenRestrictionIso c b₀ b (Spec.map τ) hC n).inv.app N := by
  let : QuasiCompact f₀ := MorphismProperty.of_isPullback hA inferInstance
  let : QuasiSeparated f₀ := MorphismProperty.of_isPullback hA inferInstance
  let : QuasiCompact b₀ := MorphismProperty.of_isPullback hC inferInstance
  let : QuasiSeparated b₀ := MorphismProperty.of_isPullback hC inferInstance
  let : (((pushforward f).rightDerived n).obj M).IsQuasicoherent :=
    affineHigherImage_isQuasicoherent (R := R) f M n
  exact pullbackRestrictionMap_eq_iso_of_top_eval (R := R) (S := S₀) (Y := Spec S)
    (Spec.map σ) (Spec.map τ)
    (((pushforward f).rightDerived n).obj M)
    (((pushforward b₀).rightDerived n).obj (N.restrict c))
    (F := (((pushforward b).rightDerived n).obj N).restrict (Spec.map τ))
    (F₀ := (pullback (Spec.map σ₀)).obj
      ((((pushforward f).rightDerived n).obj M).restrict (Spec.map ρ)))
    (F₁ := (pullback (Spec.map σ₀)).obj
      (((pushforward f₀).rightDerived n).obj (M.restrict a)))
    ((restrictFunctor (Spec.map τ)).map (higherDirectImageAffineMap p b f σ hp ψ n))
    ((pullbackOpenSquare (Spec.map τ) (Spec.map σ₀) (Spec.map σ)
      (Spec.map ρ) hb).hom.app (((pushforward f).rightDerived n).obj M))
    ((pullback (Spec.map σ₀)).map
      ((higherDirectImageOpenRestrictionIso a f₀ f (Spec.map ρ) hA n).hom.app M))
    (higherDirectImageAffineMap (M := M.restrict a) (N := N.restrict c)
      q b₀ f₀ σ₀ hp₀ (Nonflat.chartCoefficient p a c q hq ψ) n)
    ((higherDirectImageOpenRestrictionIso c b₀ b (Spec.map τ) hC n).hom.app N)
    ((higherDirectImageOpenRestrictionIso c b₀ b (Spec.map τ) hC n).inv.app N)
    ((higherDirectImageOpenRestrictionIso c b₀ b (Spec.map τ) hC n).hom_inv_id_app N)
    (affineSectionsEvaluation (R := S₀) b₀ (N.restrict c) n)
    (affineSectionsEvaluation_injective (R := S₀) b₀ (N.restrict c) n)
    (affineRefinement_mate_evaluations_eq (M := M) (N := N)
      p f b σ hp a c q f₀ b₀ ρ τ σ₀ hA hC hq hp₀ hb ψ n)

end AlgebraicGeometry.Scheme.Modules
