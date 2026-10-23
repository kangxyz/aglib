/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.Algebra.Homology.DerivedCategory.Ext.EffacementComparison
public import Aglib.Algebra.Homology.DerivedCategory.Ext.InjectiveColimit
public import Aglib.Algebra.Homology.DerivedCategory.Ext.SurjectiveColimit

/-!
# Original cohomology comparison from cogenerators and actual colimits

Every original coefficient is supplied with an actual colimit presentation by
coefficients in a class `P`. Each such coefficient embeds, by an actual
monomorphism, in a coefficient in a test class `T`. If the original comparison
is surjective on the test class in every degree, source injective coefficient
images are acyclic, degree-zero comparison is injective, and target cohomology
preserves the displayed colimits, the original comparison is bijective.

This isolates the induction of SGA 4, Expose XII, 6.2 and 6.5--6.6. It does
not define constructibility by a desired presentation, and it does not
construct the geometric finite cogenerators. Those are separate inputs.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian

namespace CategoryTheory

universe u v u' v' u'' v'' w w' k l

variable {C : Type u} [Category.{v} C] [Abelian C]
  {D : Type u'} [Category.{v'} D] [Abelian D] [HasExt.{w} D]
  {E : Type u''} [Category.{v''} E] [Abelian E] [HasExt.{w'} E]
  (F : D ⥤ E) [F.Additive] [PreservesFiniteLimits F] [PreservesFiniteColimits F]
  (U : C ⥤ D) [U.Additive] [PreservesFiniteLimits U] [PreservesFiniteColimits U]
  {X : D} {A : E} (a : A ⟶ F.obj X)

/-- Actual coefficient colimits and cogenerator embeddings reduce the original
all-degree comparison to surjectivity on the test coefficients. -/
theorem Functor.extPrecompMap_bijective_on_image_of_cogenerators [EnoughInjectives C]
    (P T : C → Prop)
    {J : C → Type k} [∀ Y, Category.{l} (J Y)]
    (K : ∀ Y, J Y ⥤ C)
    (ι : ∀ Y, K Y ⟶ (Functor.const (J Y)).obj Y)
    (hc : ∀ Y, IsColimit (Cocone.mk Y (ι Y)))
    (hP : ∀ (Y : C) (i : J Y), P ((K Y).obj i))
    (hT : ∀ Y : C, P Y → ∃ (Z : C) (i : Y ⟶ Z), Mono i ∧ T Z)
    (hcoh : ∀ (Y : C) (n : ℕ),
      PreservesColimit (K Y) (U ⋙ F ⋙ extFunctorObj A n))
    (hI : ∀ (I : C) [Injective I] (n : ℕ),
      Subsingleton (Ext X (U.obj I) (n + 1)))
    (h₀ : ∀ Y : C, Function.Injective (F.extPrecompMap a (U.obj Y) 0))
    (htest : ∀ Z : C, T Z → ∀ n : ℕ,
      Function.Surjective (F.extPrecompMap a (U.obj Z) n)) (Y : C) (n : ℕ) :
    Function.Bijective (F.extPrecompMap a (U.obj Y) n) := by
  have hs : ∀ (q : ℕ) (W : C),
      Function.Surjective (F.extPrecompMap a (U.obj W) q) := by
    intro q
    induction q with
    | zero =>
      intro W
      let : PreservesColimit (K W) (U ⋙ F ⋙ extFunctorObj A 0) := hcoh W 0
      apply F.extPrecompMap_surjective_on_image_of_isColimit a U
        (K W) (Cocone.mk W (ι W)) (hc W) 0
      intro i
      obtain ⟨Z, j, hj, hZ⟩ := hT ((K W).obj i) (hP W i)
      let : Mono j := hj
      exact F.extPrecompMap_surjective_zero_of_mono_on_image U a h₀ j (htest Z hZ 0)
    | succ q ih =>
      intro W
      let : PreservesColimit (K W) (U ⋙ F ⋙ extFunctorObj A (q + 1)) := hcoh W (q + 1)
      apply F.extPrecompMap_surjective_on_image_of_isColimit a U
        (K W) (Cocone.mk W (ι W)) (hc W) (q + 1)
      intro i
      obtain ⟨Z, j, hj, hZ⟩ := hT ((K W).obj i) (hP W i)
      let : Mono j := hj
      exact F.extPrecompMap_surjective_succ_of_mono_on_image U a q
        (fun I _ => hI I q) ih j (htest Z hZ (q + 1))
  exact F.extPrecompMap_bijective_on_image_of_surjective U a hI h₀
    (fun Z q => hs q Z) Y n

/-- Degree-zero injectivity also follows from the original test objects when
both degree-zero functors preserve the supplied exact coefficient colimits. -/
theorem Functor.extPrecompMap_bijective_on_image_of_cogenerator_tests
    [EnoughInjectives C] (P T : C → Prop)
    {J : C → Type k} [∀ Y, Category.{l} (J Y)]
    [∀ Y, HasColimitsOfShape (J Y) AddCommGrpCat.{max w w'}]
    [∀ Y, (colim : (J Y ⥤ AddCommGrpCat.{max w w'}) ⥤
      AddCommGrpCat.{max w w'}).PreservesMonomorphisms]
    (K : ∀ Y, J Y ⥤ C)
    (ι : ∀ Y, K Y ⟶ (Functor.const (J Y)).obj Y)
    (hc : ∀ Y, IsColimit (Cocone.mk Y (ι Y)))
    (hP : ∀ (Y : C) (i : J Y), P ((K Y).obj i))
    (hT : ∀ Y : C, P Y → ∃ (Z : C) (i : Y ⟶ Z), Mono i ∧ T Z)
    (hsource : ∀ Y : C, PreservesColimit (K Y) (U ⋙ extFunctorObj X 0))
    (hcoh : ∀ (Y : C) (n : ℕ),
      PreservesColimit (K Y) (U ⋙ F ⋙ extFunctorObj A n))
    (hI : ∀ (I : C) [Injective I] (n : ℕ),
      Subsingleton (Ext X (U.obj I) (n + 1)))
    (hzero : ∀ Z : C, T Z → Function.Injective (F.extPrecompMap a (U.obj Z) 0))
    (htest : ∀ Z : C, T Z → ∀ n : ℕ,
      Function.Surjective (F.extPrecompMap a (U.obj Z) n)) (Y : C) (n : ℕ) :
    Function.Bijective (F.extPrecompMap a (U.obj Y) n) := by
  have h₀ (W : C) : Function.Injective (F.extPrecompMap a (U.obj W) 0) := by
    let : PreservesColimit (K W) (U ⋙ extFunctorObj X 0) := hsource W
    let : PreservesColimit (K W) (U ⋙ F ⋙ extFunctorObj A 0) := hcoh W 0
    apply F.extPrecompMap_injective_on_image_of_isColimit a U
      (K W) (Cocone.mk W (ι W)) (hc W) 0
    intro i
    obtain ⟨Z, j, hj, hZ⟩ := hT ((K W).obj i) (hP W i)
    let : Mono j := hj
    exact F.extPrecompMap_injective_zero_of_mono_on_image U a j (hzero Z hZ)
  exact F.extPrecompMap_bijective_on_image_of_cogenerators U a P T K ι hc hP hT
    hcoh hI h₀ htest Y n

end CategoryTheory
