/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.Constructible.FiniteCogenerators.Spectrum
public import Aglib.AlgebraicGeometry.EtaleCohomology.Proper.Local.CogeneratorCriterion
public import Aglib.AlgebraicGeometry.EtaleCohomology.Constructible.PositivePresentation.NoetherianModels.BaseChange
public import Aglib.AlgebraicGeometry.EtaleCohomology.Finite.ExactImageComparison.OrdinaryBaseChange
public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Products

/-! # Original finite embeddings under inverse image and split factors

Exact original inverse image and ordinary finite exchange transport the
actual finite constant product record. Ambient finite presentability then
reduces the accepted all-stage embedding premise to the original canonical
bounded finite-colimit stages, without descending an idempotent.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry.Scheme.EtaleCohomology.Constructible.FiniteCogenerators

namespace AlgebraicGeometry.Scheme.EtaleCohomology.Constructible.PositivePresentation
namespace NoetherianModels

universe u

attribute [local instance] hasSheafifyLarge TorsionZMod.hasSheafifyStandard
  Cardinal.fact_isRegular_aleph0

/-- Precompose an actual finite constant product embedding with an original
mono, retaining its index, finite morphisms and finite value groups. -/
def finiteConstantProductEmbeddingOfMono {X : Scheme.{u}}
    {F G : AbelianSheaf.{u, u + 1} X} (a : F ⟶ G) [Mono a]
    (t : FiniteConstantProductEmbedding G) : FiniteConstantProductEmbedding F := {
  index := t.index
  finite_index := t.finite_index
  source := t.source
  morphism := t.morphism
  finite_morphism := t.finite_morphism
  value := t.value
  finite_value := t.finite_value
  map := a ≫ t.map
  mono := inferInstance }

/-- Assemble an actual finite embedding before specializing its original
coefficient arrow and whole target isomorphism. -/
def finiteConstantProductEmbeddingOfMonoIso {X : Scheme.{u}} {I : Type u} [Finite I]
    (Y : I → Scheme.{u}) (f : ∀ i, Y i ⟶ X) [∀ i, IsFinite (f i)]
    (A : I → AddCommGrpCat.{u}) [∀ i, Finite (A i)]
    {F G : AbelianSheaf.{u, u + 1} X} (a : F ⟶ G) [Mono a]
    (e : G ≅ ∏ᶜ fun i => (directImage (f i)).obj
      (ConstantFinite.coefficient (A i) (Y i))) : FiniteConstantProductEmbedding F where
  index := I
  source := Y
  morphism := f
  value := A
  map := a ≫ e.hom
  mono := inferInstance

/-- The original whole finite exchange, before evaluating a constant coefficient. -/
def finiteDirectImageInverseImageIso {X S Y : Scheme.{u}}
    (g : S ⟶ X) (f : Y ⟶ X) [IsFinite f] :
    directImage f ⋙ inverseImage g ≅
      inverseImage (pullback.fst f g) ⋙ directImage (pullback.snd f g) := by
  let h : IsPullback (pullback.fst f g) (pullback.snd f g) f g :=
    IsPullback.of_hasPullback f g
  let : IsIso (baseChangeMap f (pullback.snd f g) g (pullback.fst f g) h.w.symm) :=
    Finite.finiteBaseChange_isIso f (pullback.snd f g) g (pullback.fst f g) h
  exact asIso (baseChangeMap f (pullback.snd f g) g (pullback.fst f g) h.w.symm)

/-- Ordinary finite exchange followed by the original constant-sheaf
comparison, at the actual literal scheme pullback. -/
def finiteConstantInverseImageIso {X S Y : Scheme.{u}}
    (g : S ⟶ X) (f : Y ⟶ X) [IsFinite f] (A : AddCommGrpCat.{u}) :
    (inverseImage g).obj ((directImage f).obj (ConstantFinite.coefficient A Y)) ≅
      (directImage (pullback.snd f g)).obj (ConstantFinite.coefficient A (pullback f g)) :=
  (finiteDirectImageInverseImageIso g f).app (ConstantFinite.coefficient A Y) ≪≫
    (directImage (pullback.snd f g)).mapIso
      ((inverseImageConstantIso (pullback.fst f g)).app (ConstantFinite.value A))

/-- The actual finite-product inverse-image comparison, with the same
index and the actual finite direct images of constants on literal pullbacks. -/
def finiteConstantProductInverseImageIso {X S : Scheme.{u}}
    (g : S ⟶ X) {I : Type u} [Finite I]
    (Y : I → Scheme.{u}) (f : ∀ i, Y i ⟶ X) [∀ i, IsFinite (f i)]
    (A : I → AddCommGrpCat.{u}) :
    (inverseImage g).obj (∏ᶜ fun i =>
      (directImage (f i)).obj (ConstantFinite.coefficient (A i) (Y i))) ≅
      ∏ᶜ fun i => (directImage (pullback.snd (f i) g)).obj
        (ConstantFinite.coefficient (A i) (pullback (f i) g)) :=
  PreservesProduct.iso (inverseImage g) _ ≪≫
    Pi.mapIso (fun i => finiteConstantInverseImageIso g (f i) (A i))

/-- Pull back an actual finite constant product embedding along the original
scheme map. Each target is the constant on its literal finite pullback. -/
def finiteConstantProductEmbeddingInverseImage {X S : Scheme.{u}}
    (g : S ⟶ X) {F : AbelianSheaf.{u, u + 1} X}
    (t : FiniteConstantProductEmbedding F) :
    FiniteConstantProductEmbedding ((inverseImage g).obj F) := by
  let Y (i : t.index) := pullback (t.morphism i) g
  let f (i : t.index) : Y i ⟶ S := pullback.snd (t.morphism i) g
  have (i : t.index) : IsFinite (f i) := inferInstance
  exact finiteConstantProductEmbeddingOfMonoIso Y f t.value ((inverseImage g).map t.map)
    (finiteConstantProductInverseImageIso g t.source t.morphism t.value)

/-- Ambient FP factors the original identity through one native bounded
stage. Embedding that stage supplies the exact accepted all-stage record. -/
theorem exists_finiteConstantProductEmbedding_of_canonicalStages
    {X : Scheme.{u}} (n : ℕ)
    (hstage : ∀ C : BoundedPresentation.Coefficient X n,
      BoundedPresentation.finiteColimitStages X n C →
        Nonempty (FiniteConstantProductEmbedding C.obj))
    (M : Proper.Reduction.ZModSheaf X n)
    (hM : Proper.IsConstructibleFiniteStage X n M) :
    Nonempty (FiniteConstantProductEmbedding
      ((Proper.Reduction.zmodUnderlying X n).obj M)) := by
  let F := (Proper.Reduction.zmodUnderlying X n).obj M
  have : IsFinitelyPresentable.{u + 1} F := hM.2.1
  obtain ⟨I, hI, hfiltered, D, ι, ⟨hc⟩, hD⟩ :=
    BoundedPresentation.exists_filtered_presentation X n F
      (Proper.Reduction.zmodUnderlying_nsmul_id X n M)
  let := hI
  have : IsFiltered I := hfiltered
  obtain ⟨j, a, ha⟩ := IsFinitelyPresentable.exists_hom_of_isColimit hc (𝟙 F)
  have : Mono a := mono_of_mono_fac ha
  obtain ⟨t⟩ := hstage (D.obj j) (hD j)
  exact ⟨finiteConstantProductEmbeddingOfMono a t⟩

end NoetherianModels
end AlgebraicGeometry.Scheme.EtaleCohomology.Constructible.PositivePresentation
