/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.Constructible.FiniteCogenerators.Spectrum

/-! # Finite constant cogenerators on actual affine Noetherian schemes

The canonical affine isomorphism transports the actual integral covering strata
to a spectrum. Its original inverse image preserves ambient finite
presentability by the explicit inverse-image equivalence. The spectrum
construction then transports back through the original adjunction and the
original direct-image composition. Every target, finite map, value and mono
is retained in the resulting record.

The values are arbitrary finite abelian groups; no prescribed modulus or
genuine ZMod-linear mono is asserted here.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Scheme.EtaleCohomology.Constructible.FiniteCogenerators

universe u

attribute [local instance] hasSheafifyLarge Cardinal.fact_isRegular_aleph0

/-- Original scheme-isomorphism inverse images are an actual equivalence,
through the original identity and composition comparisons. -/
def inverseImageEquivalenceOfIso {X Y : Scheme.{u}} (e : X ≅ Y) :
    AbelianSheaf.{u, u + 1} Y ≌ AbelianSheaf.{u, u + 1} X :=
  CategoryTheory.Equivalence.mk (inverseImage e.hom) (inverseImage e.inv)
    ((inverseImageId Y).symm ≪≫
      eqToIso (congrArg (fun f : Y ⟶ Y => inverseImage f) e.inv_hom_id.symm) ≪≫
        inverseImageComp e.hom e.inv)
    ((inverseImageComp e.inv e.hom).symm ≪≫
      eqToIso (congrArg (fun f : X ⟶ X => inverseImage f) e.hom_inv_id) ≪≫
        inverseImageId X)

/-- Keep the actual integral pieces and compose their original inclusions
with the given scheme isomorphism. -/
def FiniteIntegralLocallyClosedCover.onIso {X Y : Scheme.{u}}
    {F : AbelianSheaf.{u, u + 1} X} (t : FiniteIntegralLocallyClosedCover F) (e : X ≅ Y) :
    FiniteIntegralLocallyClosedCover ((inverseImage e.inv).obj F) where
  index := t.index
  finite_index := t.finite_index
  stratum := t.stratum
  inclusion i := t.inclusion i ≫ e.hom
  immersion i := by
    have : IsImmersion (t.inclusion i) := t.immersion i
    infer_instance
  integral := t.integral
  covers y := by
    obtain ⟨i, z, hz⟩ := t.covers (e.inv y)
    refine ⟨i, z, ?_⟩
    change e.hom (t.inclusion i z) = y
    rw [hz]
    exact congrArg (fun f : Y ⟶ Y => f y) e.inv_hom_id
  locally_constant i := by
    have hi : (t.inclusion i ≫ e.hom) ≫ e.inv = t.inclusion i := by
      rw [Category.assoc, e.hom_inv_id, Category.comp_id]
    let c : (inverseImage (t.inclusion i ≫ e.hom)).obj ((inverseImage e.inv).obj F) ≅
        (inverseImage (t.inclusion i)).obj F :=
      ((inverseImageComp e.inv (t.inclusion i ≫ e.hom)).app F).symm ≪≫
        eqToIso (congrArg (fun f => (inverseImage f).obj F) hi)
    exact (isFiniteLocallyConstant_iff_of_iso c).mpr (t.locally_constant i)

/-- Transport an actual finite constant product embedding by the original
adjunction and direct-image composition, preserving the same values. -/
def FiniteConstantProductEmbedding.ofIso {X Y : Scheme.{u}} (e : X ≅ Y)
    {F : AbelianSheaf.{u, u + 1} X}
    (t : FiniteConstantProductEmbedding ((inverseImage e.inv).obj F)) :
    FiniteConstantProductEmbedding F := by
  have : (inverseImage e.inv).IsEquivalence :=
    (inverseImageEquivalenceOfIso e.symm).isEquivalence_functor
  let B := fun i => ConstantFinite.coefficient (t.value i) (t.source i)
  let T := fun i => (directImage (t.morphism i)).obj (B i)
  let W := fun i => (directImage (t.morphism i ≫ e.inv)).obj (B i)
  let q := fun i => (inverseImageAdjunction e.inv).homEquiv F (T i)
    (t.map ≫ Pi.π T i)
  let a (i : t.index) : F ⟶ W i :=
    q i ≫ (directImageCompIso e.inv (t.morphism i)).hom.app (B i)
  let α : F ⟶ ∏ᶜ W := Pi.lift (f := W) a
  have hmono : Mono α := by
    constructor
    intro G x y hxy
    apply (inverseImage e.inv).map_injective
    apply (cancel_mono t.map).mp
    apply Pi.hom_ext
    intro i
    have hi : x ≫ a i = y ≫ a i := by
      let π := Pi.π W i
      have hp : α ≫ π = a i := Pi.lift_comp_π (f := W) a i
      have hproj : x ≫ (α ≫ π) = y ≫ (α ≫ π) :=
        (Category.assoc x α π).symm.trans
          ((congrArg (fun k => k ≫ π) hxy).trans (Category.assoc y α π))
      exact (congrArg (fun k => x ≫ k) hp.symm).trans
        (hproj.trans (congrArg (fun k => y ≫ k) hp))
    have hq : x ≫ q i = y ≫ q i := by
      apply (cancel_mono ((directImageCompIso e.inv (t.morphism i)).hom.app (B i))).mp
      simpa only [a, Category.assoc] using hi
    have hm : (inverseImage e.inv).map x ≫ (t.map ≫ Pi.π T i) =
        (inverseImage e.inv).map y ≫ (t.map ≫ Pi.π T i) := by
      apply ((inverseImageAdjunction e.inv).homEquiv G (T i)).injective
      rw [Adjunction.homEquiv_naturality_left, Adjunction.homEquiv_naturality_left]
      exact hq
    simpa only [Category.assoc] using hm
  have (i : t.index) : IsFinite (t.morphism i ≫ e.inv) := inferInstance
  exact {
    index := t.index
    source := t.source
    morphism := fun i => t.morphism i ≫ e.inv
    value := t.value
    map := α
    mono := hmono }

/-- A geometrically constructible, ambient finitely presentable coefficient
on an actual affine Noetherian scheme has an original finite constant product
embedding, with no Japanese or finite-normalization premise. -/
def finiteConstantProductEmbeddingOfIsAffine (X : Scheme.{u}) [IsAffine X] [IsNoetherian X]
    (F : AbelianSheaf.{u, u + 1} X) [IsFinitelyPresentable.{u + 1} F]
    (hF : IsConstructible F) : FiniteConstantProductEmbedding F := by
  let R : Type u := Γ(X, ⊤)
  let e : X ≅ Spec (.of R) := X.isoSpec
  let G := (inverseImage e.inv).obj F
  have : (inverseImage e.inv).IsEquivalence :=
    (inverseImageEquivalenceOfIso e.symm).isEquivalence_functor
  have : IsFinitelyPresentable.{u + 1} G := inferInstance
  let t := finiteIntegralLocallyClosedCover F hF
  let s := finiteConstantProductEmbeddingOfIntegralCover G (t.onIso e)
  exact FiniteConstantProductEmbedding.ofIso e s

end AlgebraicGeometry.Scheme.EtaleCohomology.Constructible.FiniteCogenerators
