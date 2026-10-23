/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.Algebra.Homology.DerivedCategory.Ext.ShortExactComparison

/-!
# Effacement and surjectivity tests for the original Ext comparison

An exact coefficient functor may send injectives to cohomologically acyclic
objects without preserving injectivity. For its original coefficients, the
exact-functor comparison is injective in degree `n` if it is injective in
degree zero and surjective in every degree below `n`. In particular,
all-degree surjectivity and degree-zero injectivity imply all-degree
bijectivity. The proof retains the original connecting extension classes.

This is the Ext form of SGA 4, Expose XII, Lemma 6.2. The acyclicity
hypothesis concerns source cohomology of actual coefficient images; it does
not assume acyclicity after the functor being compared.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian

namespace CategoryTheory

universe u v u' v' u'' v'' w w'

variable {C : Type u} [Category.{v} C] [Abelian C]
  {D : Type u'} [Category.{v'} D] [Abelian D] [HasExt.{w} D]
  {E : Type u''} [Category.{v''} E] [Abelian E] [HasExt.{w'} E]
  (F : D ⥤ E) [F.Additive] [PreservesFiniteLimits F] [PreservesFiniteColimits F]
  (U : C ⥤ D) [U.Additive] [PreservesFiniteLimits U] [PreservesFiniteColimits U]
  {X : D} {A : E} (a : A ⟶ F.obj X)

/-- An injective presentation and degree-`n` bijectivity give injectivity in degree `n+1`.
Only the source cohomology of the image of an injective must vanish. -/
theorem Functor.extPrecompMap_injective_succ_on_image [EnoughInjectives C] (n : ℕ)
    (hI : ∀ (I : C) [Injective I], Subsingleton (Ext X (U.obj I) (n + 1)))
    (hn : ∀ Y : C, Function.Bijective (F.extPrecompMap a (U.obj Y) n)) (Y : C) :
    Function.Injective (F.extPrecompMap a (U.obj Y) (n + 1)) := by
  classical
  let I : InjectivePresentation Y := Classical.arbitrary _
  let S := ShortComplex.mk I.f (cokernel.π I.f) (cokernel.condition I.f)
  have hS : S.ShortExact := { exact := ShortComplex.exact_cokernel I.f }
  let T := S.map U
  have hT : T.ShortExact := hS.map_of_exact U
  let : Subsingleton (Ext X T.X₂ (n + 1)) := hI S.X₂
  exact AddMonoidHom.injective_of_surjective_of_injective_of_right_exact
    ((Ext.mk₀ T.g).postcomp X (Nat.add_zero n))
    (hT.extClass.postcomp X (show n + 1 = n + 1 from rfl))
    ((Ext.mk₀ (F.map T.g)).postcomp A (Nat.add_zero n))
    ((hT.map_of_exact F).extClass.postcomp A (show n + 1 = n + 1 from rfl))
    (F.extPrecompMap a T.X₂ n) (F.extPrecompMap a T.X₃ n)
    (F.extPrecompMap a T.X₁ (n + 1))
    (F.extPrecompMap_postcomp a T.g n)
    (F.extPrecompMap_connecting a T hT n)
    ((ShortComplex.ab_exact_iff_function_exact _).mp
      (Ext.covariant_sequence_exact₃' X hT n (n + 1) rfl))
    ((ShortComplex.ab_exact_iff_function_exact _).mp
      (Ext.covariant_sequence_exact₃' A (hT.map_of_exact F) n (n + 1) rfl))
    (hn S.X₂).surjective (hn S.X₃).injective
    (fun x => Ext.covariant_sequence_exact₁ X hT x (Subsingleton.elim _ _) rfl)

/-- Surjectivity below a degree forces injectivity in that degree, starting from degree zero. -/
theorem Functor.extPrecompMap_injective_on_image_of_surjective_below [EnoughInjectives C]
    (hI : ∀ (I : C) [Injective I] (n : ℕ),
      Subsingleton (Ext X (U.obj I) (n + 1)))
    (h₀ : ∀ Y : C, Function.Injective (F.extPrecompMap a (U.obj Y) 0))
    (n : ℕ)
    (hs : ∀ (Y : C) (q : ℕ), q < n →
      Function.Surjective (F.extPrecompMap a (U.obj Y) q)) (Y : C) :
    Function.Injective (F.extPrecompMap a (U.obj Y) n) := by
  suffices h : ∀ k : ℕ,
      (∀ (Z : C) (q : ℕ), q < k →
        Function.Surjective (F.extPrecompMap a (U.obj Z) q)) →
      ∀ Z : C, Function.Injective (F.extPrecompMap a (U.obj Z) k) from h n hs Y
  intro k
  induction k with
  | zero => intro _ Z; exact h₀ Z
  | succ k ih =>
    intro hk Z
    apply F.extPrecompMap_injective_succ_on_image U a k (fun I _ => hI I k)
    intro W
    exact ⟨ih (fun V q hq => hk V q (by omega)) W, hk W k (by omega)⟩

/-- All-degree surjectivity and degree-zero injectivity suffice for the original comparison. -/
theorem Functor.extPrecompMap_bijective_on_image_of_surjective [EnoughInjectives C]
    (hI : ∀ (I : C) [Injective I] (n : ℕ),
      Subsingleton (Ext X (U.obj I) (n + 1)))
    (h₀ : ∀ Y : C, Function.Injective (F.extPrecompMap a (U.obj Y) 0))
    (hs : ∀ (Y : C) (n : ℕ),
      Function.Surjective (F.extPrecompMap a (U.obj Y) n)) (Y : C) (n : ℕ) :
    Function.Bijective (F.extPrecompMap a (U.obj Y) n) :=
  ⟨F.extPrecompMap_injective_on_image_of_surjective_below U a hI h₀ n
      (fun Z q _ => hs Z q) Y,
    hs Y n⟩

/-- The bounded surjectivity test also supplies injectivity in the next degree. -/
theorem Functor.extPrecompMap_bijective_through_on_image_of_surjective [EnoughInjectives C]
    (hI : ∀ (I : C) [Injective I] (q : ℕ),
      Subsingleton (Ext X (U.obj I) (q + 1)))
    (h₀ : ∀ Y : C, Function.Injective (F.extPrecompMap a (U.obj Y) 0))
    (n : ℕ)
    (hs : ∀ (Y : C) (q : ℕ), q ≤ n →
      Function.Surjective (F.extPrecompMap a (U.obj Y) q)) :
    (∀ (Y : C) (q : ℕ), q ≤ n →
      Function.Bijective (F.extPrecompMap a (U.obj Y) q)) ∧
    (∀ Y : C, Function.Injective (F.extPrecompMap a (U.obj Y) (n + 1))) := by
  constructor
  · intro Y q hq
    exact ⟨F.extPrecompMap_injective_on_image_of_surjective_below U a hI h₀ q
      (fun Z r hr => hs Z r (by omega)) Y, hs Y q hq⟩
  · intro Y
    exact F.extPrecompMap_injective_on_image_of_surjective_below U a hI h₀ (n + 1)
      (fun Z r hr => hs Z r (by omega)) Y

/-- A class comes from the original comparison exactly when some original monomorphism
kills it, provided comparison is surjective in the preceding degree. -/
theorem Functor.extPrecompMap_mem_range_iff_effaceable_on_image [EnoughInjectives C]
    (n : ℕ)
    (hI : ∀ (I : C) [Injective I], Subsingleton (Ext X (U.obj I) (n + 1)))
    (hn : ∀ Z : C, Function.Surjective (F.extPrecompMap a (U.obj Z) n))
    (Y : C) (y : Ext A (F.obj (U.obj Y)) (n + 1)) :
    y ∈ Set.range (F.extPrecompMap a (U.obj Y) (n + 1)) ↔
      ∃ (Z : C) (i : Y ⟶ Z), Mono i ∧
        y.comp (Ext.mk₀ (F.map (U.map i))) (Nat.add_zero (n + 1)) = 0 := by
  classical
  constructor
  · rintro ⟨x, rfl⟩
    let I : InjectivePresentation Y := Classical.arbitrary _
    let : Subsingleton (Ext X (U.obj I.J) (n + 1)) := hI I.J
    refine ⟨I.J, I.f, inferInstance, ?_⟩
    calc
      (F.extPrecompMap a (U.obj Y) (n + 1) x).comp
          (Ext.mk₀ (F.map (U.map I.f))) (Nat.add_zero (n + 1)) =
        F.extPrecompMap a (U.obj I.J) (n + 1)
          (x.comp (Ext.mk₀ (U.map I.f)) (Nat.add_zero (n + 1))) :=
        DFunLike.congr_fun (F.extPrecompMap_postcomp a (U.map I.f) (n + 1)) x
      _ = 0 := by rw [Subsingleton.elim
          (x.comp (Ext.mk₀ (U.map I.f)) (Nat.add_zero (n + 1))) 0, map_zero]
  · rintro ⟨Z, i, hi, hy⟩
    let : Mono i := hi
    let S := ShortComplex.mk i (cokernel.π i) (cokernel.condition i)
    have hS : S.ShortExact := { exact := ShortComplex.exact_cokernel i }
    let T := S.map U
    have hT : T.ShortExact := hS.map_of_exact U
    obtain ⟨z, hz⟩ := Ext.covariant_sequence_exact₁ A (hT.map_of_exact F) y hy rfl
    obtain ⟨x, hx⟩ := hn S.X₃ z
    refine ⟨x.comp hT.extClass rfl, ?_⟩
    rw [Functor.extPrecompMap_comp, Ext.mapExactFunctor_extClass, hx, hz]

/-- In degree zero, surjectivity on a coefficient containing the original one descends
along the actual monomorphism, if all degree-zero comparisons are injective. -/
theorem Functor.extPrecompMap_surjective_zero_of_mono_on_image
    (h₀ : ∀ W : C, Function.Injective (F.extPrecompMap a (U.obj W) 0))
    {Y Z : C} (i : Y ⟶ Z) [Mono i]
    (hZ : Function.Surjective (F.extPrecompMap a (U.obj Z) 0)) :
    Function.Surjective (F.extPrecompMap a (U.obj Y) 0) := by
  let S := ShortComplex.mk i (cokernel.π i) (cokernel.condition i)
  have hS : S.ShortExact := { exact := ShortComplex.exact_cokernel i }
  let T := S.map U
  have hT : T.ShortExact := hS.map_of_exact U
  let : Mono (F.map T.f) := (hT.map_of_exact F).mono_f
  exact AddMonoidHom.surjective_of_surjective_of_injective_of_left_exact
    ((Ext.mk₀ T.f).postcomp X (Nat.add_zero 0))
    ((Ext.mk₀ T.g).postcomp X (Nat.add_zero 0))
    ((Ext.mk₀ (F.map T.f)).postcomp A (Nat.add_zero 0))
    ((Ext.mk₀ (F.map T.g)).postcomp A (Nat.add_zero 0))
    (F.extPrecompMap a T.X₁ 0) (F.extPrecompMap a T.X₂ 0)
    (F.extPrecompMap a T.X₃ 0)
    (F.extPrecompMap_postcomp a T.f 0) (F.extPrecompMap_postcomp a T.g 0)
    ((ShortComplex.ab_exact_iff_function_exact _).mp
      (Ext.covariant_sequence_exact₂' X hT 0))
    ((ShortComplex.ab_exact_iff_function_exact _).mp
      (Ext.covariant_sequence_exact₂' A (hT.map_of_exact F) 0))
    hZ (h₀ S.X₃) (Ext.postcomp_mk₀_injective_of_mono A (F.map T.f))

/-- Surjectivity in positive degree descends along a coefficient monomorphism if
comparison in the preceding degree is already surjective for every coefficient. -/
theorem Functor.extPrecompMap_surjective_succ_of_mono_on_image [EnoughInjectives C]
    (n : ℕ)
    (hI : ∀ (I : C) [Injective I], Subsingleton (Ext X (U.obj I) (n + 1)))
    (hn : ∀ W : C, Function.Surjective (F.extPrecompMap a (U.obj W) n))
    {Y Z : C} (i : Y ⟶ Z) [Mono i]
    (hZ : Function.Surjective (F.extPrecompMap a (U.obj Z) (n + 1))) :
    Function.Surjective (F.extPrecompMap a (U.obj Y) (n + 1)) := by
  intro y
  let z := y.comp (Ext.mk₀ (F.map (U.map i))) (Nat.add_zero (n + 1))
  obtain ⟨W, j, hj, hz⟩ :=
    (F.extPrecompMap_mem_range_iff_effaceable_on_image U a n hI hn Z z).mp (hZ z)
  let : Mono j := hj
  apply (F.extPrecompMap_mem_range_iff_effaceable_on_image U a n hI hn Y y).mpr
  refine ⟨W, i ≫ j, inferInstance, ?_⟩
  rw [U.map_comp, F.map_comp, ← Ext.mk₀_comp_mk₀,
    ← Ext.comp_assoc_of_third_deg_zero]
  exact hz

/-- Injectivity in degree zero restricts along an actual coefficient monomorphism. -/
theorem Functor.extPrecompMap_injective_zero_of_mono_on_image
    {Y Z : C} (i : Y ⟶ Z) [Mono i]
    (hZ : Function.Injective (F.extPrecompMap a (U.obj Z) 0)) :
    Function.Injective (F.extPrecompMap a (U.obj Y) 0) := by
  let : Mono (U.map i) := inferInstance
  intro x y hxy
  apply Ext.postcomp_mk₀_injective_of_mono X (U.map i)
  apply hZ
  have hx := DFunLike.congr_fun (F.extPrecompMap_postcomp a (U.map i) 0) x
  have hy := DFunLike.congr_fun (F.extPrecompMap_postcomp a (U.map i) 0) y
  exact hx.symm.trans ((congrArg
    (fun z => z.comp (Ext.mk₀ (F.map (U.map i))) (Nat.add_zero 0)) hxy).trans hy)

end CategoryTheory
