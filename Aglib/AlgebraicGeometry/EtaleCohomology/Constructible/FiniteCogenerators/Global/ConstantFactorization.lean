/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.Constructible.FiniteCogenerators.Global.LocalStageFactorization
public import Aglib.AlgebraicGeometry.EtaleCohomology.Constructible.FiniteCogenerators.Global.FiniteAffineCover
public import Aglib.AlgebraicGeometry.EtaleCohomology.Constructible.FiniteCogenerators.Global.FiniteStageModel
public import Aglib.AlgebraicGeometry.EtaleCohomology.Constructible.FiniteCogenerators.Global.ComparisonMono
public import Aglib.AlgebraicGeometry.EtaleCohomology.Constructible.FiniteCogenerators.Global.LocalFactorization

/-! # Original integral constant arrows through actual global finite targets

FP on the original affine restrictions factors each original local arrow
through an actual finite algebra stage. Global finite-type module images
capture these stages in one generated relative algebra. Its genuinely finite
structural map and integral-surjective comparison yield one fixed original
coefficient mono. Original chart naturality transports the local factors
through that same mono, and the actual open cover detects the global factor.
No finite normalization, prescribed modulus, or global coefficient-colimit
premise is used.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.Scheme.EtaleCohomology.Constructible.FiniteCogenerators.Global

universe u

open AffineZariskiSite Scheme.Modules Scheme.Modules.QuasiCoherent
open AffineIntegralConstants

attribute [local instance] hasSheafifyLarge

/-- An original coefficient arrow through an actual global finite algebra
model, retaining the original relative source map and coefficient transition. -/
structure FiniteConstantFactorization {X Y : Scheme.{u}} (f : Y ⟶ X)
    (B : Type u) [AddCommGroup B] [Finite B] (F : AbelianSheaf.{u, u + 1} X)
    (α : F ⟶ (constantPushforwardFunctor (X := X) B).obj (op (Over.mk f))) where
  source : Scheme.{u}
  morphism : source ⟶ X
  [finite_morphism : IsFinite morphism]
  comparison : Y ⟶ source
  [comparison_surjective : Surjective comparison]
  [comparison_integral : IsIntegralHom comparison]
  over : comparison ≫ morphism = f
  map : F ⟶ (constantPushforwardFunctor (X := X) B).obj (op (Over.mk morphism))
  factor : map ≫ (constantPushforwardFunctor (X := X) B).map
    (Over.homMk comparison over).op = α

attribute [instance] FiniteConstantFactorization.finite_morphism
  FiniteConstantFactorization.comparison_surjective
  FiniteConstantFactorization.comparison_integral

private theorem nonempty_finiteConstantFactorization_of_openCover
    {X Y Z : Scheme.{u}} (f : Y ⟶ X)
    (B : Type u) [AddCommGroup B] [Finite B] (F : AbelianSheaf.{u, u + 1} X)
    (α : F ⟶ (constantPushforwardFunctor (X := X) B).obj (op (Over.mk f)))
    (cov : X.OpenCover.{u}) (g : Z ⟶ X) [IsFinite g]
    (H : Over.mk f ⟶ Over.mk g) [Surjective H.left] [IsIntegralHom H.left]
    (hlocal : ∀ k, ∃ β : (inverseImage (cov.f k)).obj F ⟶
        (inverseImage (cov.f k)).obj
          ((constantPushforwardFunctor (X := X) B).obj (op (Over.mk g))),
      β ≫ (inverseImage (cov.f k)).map
          ((constantPushforwardFunctor (X := X) B).map H.op) =
        (inverseImage (cov.f k)).map α) :
    Nonempty (FiniteConstantFactorization f B F α) := by
  let P : (Over X)ᵒᵖ ⥤ AbelianSheaf.{u, u + 1} X :=
    constantPushforwardFunctor (X := X) B
  let τ : P.obj (op (Over.mk g)) ⟶ P.obj (op (Over.mk f)) := P.map H.op
  have : Mono τ := constantPushforwardFunctor_map_mono B H
  obtain ⟨β, hβ⟩ := exists_factor_of_openCover (X := X) cov
    (A := P.obj (op (Over.mk g))) (B := P.obj (op (Over.mk f))) (F := F) τ α hlocal
  have hH : Over.homMk H.left (Over.w H) = H := by
    apply Over.OverMorphism.ext
    rfl
  have hfactor : β ≫ P.map (Over.homMk H.left (Over.w H)).op = α :=
    (congrArg (fun z : Over.mk f ⟶ Over.mk g => β ≫ P.map z.op) hH).trans hβ
  exact ⟨{
    source := Z
    morphism := g
    finite_morphism := inferInstance
    comparison := H.left
    comparison_surjective := inferInstance
    comparison_integral := inferInstance
    over := Over.w H
    map := β
    factor := hfactor }⟩

/-- Original maps to integral finite-constant direct images factor through one
actual finite global target, using FP only on the original affine restrictions. -/
theorem nonempty_finiteConstantFactorization
    {X Y : Scheme.{u}} [CompactSpace X] [QuasiSeparatedSpace X]
    (f : Y ⟶ X) [IsIntegralHom f] (B : Type u) [AddCommGroup B] [Finite B]
    (F : AbelianSheaf.{u, u + 1} X)
    (hFP : ∀ (R : CommRingCat.{u}) (j : Spec R ⟶ X) [IsOpenImmersion j],
      IsFinitelyPresentable.{u + 1} ((inverseImage j).obj F))
    (α : F ⟶ (constantPushforwardFunctor (X := X) B).obj (op (Over.mk f))) :
    Nonempty (FiniteConstantFactorization f B F α) := by
  classical
  let cov : X.OpenCover.{u} := finiteAffineSpecCover X
  let I : Type u := cov.I₀
  have : Finite I := inferInstanceAs (Finite (finiteAffineSpecCover X).I₀)
  let U : I → X.AffineZariskiSite := finiteAffineSpecCoverOpen X
  let R (k : I) : CommRingCat.{u} := Γ(X, (U k).1)
  let A (k : I) : CommRingCat.{u} := Γ(Y, f ⁻¹ᵁ (U k).1)
  let j (k : I) : Spec (R k) ⟶ X := (U k).2.fromSpec
  let (k : I) : Algebra (R k) (A k) := (f.app (U k).1).hom.toAlgebra
  have (k : I) : IsOpenImmersion (j k) :=
    IsAffineOpen.isOpenImmersion_fromSpec (U k).2
  let P : (Over X)ᵒᵖ ⥤ AbelianSheaf.{u, u + 1} X :=
    constantPushforwardFunctor (X := X) B
  have hv : Nonempty (∀ k : I, AffineConstantStage f B F α (U k)) := by
    refine ⟨fun k => ?_⟩
    have : IsFinitelyPresentable.{u + 1} ((inverseImage (j k)).obj F) := hFP (R k) (j k)
    exact affineConstantStage f B F α (U k)
  obtain ⟨v⟩ := hv
  let s (k : I) : Finset (A k) := (v k).stage
  obtain ⟨q⟩ := nonempty_finiteStageModel f U s
  let g : q.source ⟶ X := q.morphism
  let H : Over.mk f ⟶ Over.mk g := q.comparison
  let τ : P.obj (op (Over.mk g)) ⟶ P.obj (op (Over.mk f)) := P.map H.op
  have hlocal (k : I) :
      ∃ β : (inverseImage (cov.f k)).obj F ⟶
          (inverseImage (cov.f k)).obj (P.obj (op (Over.mk g))),
        β ≫ (inverseImage (cov.f k)).map τ = (inverseImage (cov.f k)).map α := by
    change ∃ β : (inverseImage (j k)).obj F ⟶
        (inverseImage (j k)).obj (P.obj (op (Over.mk g))),
      β ≫ (inverseImage (j k)).map τ = (inverseImage (j k)).map α
    have : IsOpenImmersion (U k).2.fromSpec :=
      IsAffineOpen.isOpenImmersion_fromSpec (U k).2
    let Q : (Over (Spec (R k)))ᵒᵖ ⥤ AbelianSheaf.{u, u + 1} (Spec (R k)) :=
      constantPushforwardFunctor (X := Spec (R k)) B
    let P₀ : (Over X)ᵒᵖ ⥤ AbelianSheaf.{u, u + 1} (Spec (R k)) :=
      P ⋙ inverseImage (U k).2.fromSpec
    let F₀ : AbelianSheaf.{u, u + 1} (Spec (R k)) :=
      (inverseImage (U k).2.fromSpec).obj F
    let α₀ : F₀ ⟶ P₀.obj (op (Over.mk f)) :=
      (inverseImage (U k).2.fromSpec).map α
    let T : Over X ⥤ Over (Spec (R k)) := Over.pullback (U k).2.fromSpec
    let e : P₀ ⋙ 𝟭 (AbelianSheaf.{u, u + 1} (Spec (R k))) ≅ T.op ⋙ Q :=
      constantPushforwardRestrictionIso (U k).2.fromSpec B
    let YA : Over (Spec (R k)) := Over.mk (Spec.algebraMap (R k) (A k))
    let a : YA ≅ T.obj (Over.mk f) := relativeAffineChartObjectIso f (U k)
    let C : Subalgebra (R k) (A k) := q.subalgebra k
    have hs : Algebra.FiniteTypeSubalgebraLimit.stage (R k) (A k) (s k) ≤ C := q.stage_le k
    let YC : Over (Spec (R k)) := Over.mk (Spec.algebraMap (R k) C)
    let r : YA ⟶ YC := subalgebraOverMap (R k) (A k) C
    let c : YC ≅ T.obj (Over.mk g) := q.chartIso k
    have hc : a.hom ≫ T.map H = r ≫ c.hom := q.comparison_chart k
    let E : P₀.obj (op (Over.mk f)) ≅ Q.obj (op YA) :=
      affineConstantPushforwardRestrictionIso f B (U k)
    have hE : E.hom = e.hom.app (op (Over.mk f)) ≫ Q.map a.hom.op :=
      affineConstantPushforwardRestrictionIso_hom f B (U k)
    let S : AbelianSheaf.{u, u + 1} (Spec (R k)) :=
      (constantPushforwardDiagram (R k) (A k) B).obj (op (op (s k)))
    let b : F₀ ⟶ S := (v k).map
    let t : S ⟶ Q.obj (op YC) :=
      Q.map (stageIntoSubalgebraOverMap (R k) (A k) C (s k) hs).op
    let leg : S ⟶ Q.obj (op YA) :=
      (constantPushforwardCocone (R k) (A k) B).ι.app (op (op (s k)))
    have ht : t ≫ Q.map r.op = leg :=
      subalgebra_stage_pushforward_map (R k) (A k) B C (s k) hs
    have hb := (v k).factor
    have localFactor : ∃ β : F₀ ⟶ P₀.obj (op (Over.mk g)), β ≫ P₀.map H.op = α₀ := by
      exact exists_factor_of_contraFunctorIso_chart_stage
        (A := Over X) (B := Over (Spec (R k)))
        (C := AbelianSheaf.{u, u + 1} (Spec (R k)))
        (D := AbelianSheaf.{u, u + 1} (Spec (R k)))
        P₀ Q T (𝟭 (AbelianSheaf.{u, u + 1} (Spec (R k)))) e
        (Y := Over.mk f) (Z := Over.mk g) H (Y' := YA) (Z' := YC) a c r hc E hE
        (F := F₀) α₀ (S := S) b t leg ht hb
    exact localFactor
  have : IsFinite g := q.finite_morphism
  have : Surjective H.left := q.comparison_surjective
  have : IsIntegralHom H.left := q.comparison_integral
  exact nonempty_finiteConstantFactorization_of_openCover f B F α cov g H hlocal

/-- Choose the actual finite global factor of the original supplied arrow. -/
def finiteConstantFactorization
    {X Y : Scheme.{u}} [CompactSpace X] [QuasiSeparatedSpace X]
    (f : Y ⟶ X) [IsIntegralHom f] (B : Type u) [AddCommGroup B] [Finite B]
    (F : AbelianSheaf.{u, u + 1} X)
    (hFP : ∀ (R : CommRingCat.{u}) (j : Spec R ⟶ X) [IsOpenImmersion j],
      IsFinitelyPresentable.{u + 1} ((inverseImage j).obj F))
    (α : F ⟶ (constantPushforwardFunctor (X := X) B).obj (op (Over.mk f))) :
    FiniteConstantFactorization f B F α :=
  Classical.choice (nonempty_finiteConstantFactorization f B F hFP α)

end AlgebraicGeometry.Scheme.EtaleCohomology.Constructible.FiniteCogenerators.Global
