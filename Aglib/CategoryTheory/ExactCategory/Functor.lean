/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Aglib.CategoryTheory.ExactCategory.MatrixDeflation
public import Mathlib.CategoryTheory.Preadditive.AdditiveFunctor
/-!
# Exact additive functors

An exact functor preserves the specified conflations. Preservation of pullbacks
along admissible epimorphisms is derived from additivity and exactness.
-/
@[expose] public section


noncomputable section
universe v₁ v₂ v₃ u₁ u₂ u₃
open CategoryTheory CategoryTheory.Limits CategoryTheory.Preadditive

attribute [local instance] hasBinaryBiproducts_of_finite_biproducts

namespace CategoryTheory.ExactCategory

variable {C : Type u₁} {D : Type u₂} [Category.{v₁} C] [Category.{v₂} D]
  [Preadditive C] [Preadditive D] [HasFiniteBiproducts C] [HasFiniteBiproducts D]

/-- An exact functor is an additive functor preserving the specified conflations. -/
structure ExactFunctor (E : ExactStructure C) (E' : ExactStructure D) where
  /-- The underlying functor from the source exact category to the target exact category. -/
  toFunctor : C ⥤ D
  [additive : toFunctor.Additive]
  map_conflation : ∀ (S : ShortComplex C), E.conflation S →
    E'.conflation (S.map toFunctor)

attribute [instance] ExactFunctor.additive

namespace ExactStructure

/-- A chosen kernel of an admissible epimorphism is its specified conflation. -/
lemma conflation_of_isKernel (E : ExactStructure C) {X Y Z : C}
    {i : X ⟶ Y} {p : Y ⟶ Z} (h : i ≫ p = 0)
    (hi : IsLimit (KernelFork.ofι i h)) (hp : E.deflation p) :
    E.conflation (ShortComplex.mk i p h) := by
  obtain ⟨X', i', h', hs⟩ := hp
  let hi' := E.kernel (ShortComplex.mk i' p h') hs
  let e : X' ≅ X := hi'.conePointUniqueUpToIso hi
  have he : e.hom ≫ i = i' :=
    hi'.conePointUniqueUpToIso_hom_comp hi WalkingParallelPair.zero
  let se : ShortComplex.mk i' p h' ≅ ShortComplex.mk i p h :=
    ShortComplex.isoMk e (Iso.refl _) (Iso.refl _) (by simpa using he) (by simp)
  exact E.iso_closed se hs

end ExactStructure

/-- The total kernel of a pullback square in an additive category. No abelian
hypothesis or ambient existence of arbitrary pullbacks is needed. -/
def pullbackMatrixKernel {P A B T : C} {a : P ⟶ A} {b : P ⟶ B}
    {i : A ⟶ T} {p : B ⟶ T} (sq : IsPullback a b i p) :
    IsLimit (KernelFork.ofι (biprod.lift a b)
      (show biprod.lift a b ≫ biprod.desc (-i) p = 0 by
        simp only [biprod.lift_desc, comp_neg, sq.w, neg_add_cancel])) := by
  refine KernelFork.IsLimit.ofι _ _
    (fun {W} f hf => sq.lift (f ≫ biprod.fst) (f ≫ biprod.snd) (by
      apply neg_add_eq_zero.mp
      simpa only [biprod.desc_eq, Preadditive.comp_add, Category.assoc, comp_neg] using hf))
    ?_ ?_
  · intro W f hf
    apply biprod.hom_ext <;> simp
  · intro W f hf m hm
    apply sq.hom_ext
    · simpa using congrArg (fun k => k ≫ biprod.fst) hm
    · simpa using congrArg (fun k => k ≫ biprod.snd) hm

namespace ExactFunctor

/-- The identity functor is exact. -/
def id (E : ExactStructure C) : ExactFunctor E E where
  toFunctor := 𝟭 C
  map_conflation _ hs := hs

/-- The composite of exact functors is exact. -/
def comp {E : ExactStructure C} {E' : ExactStructure D}
    {T : Type u₃} [Category.{v₃} T] [Preadditive T] [HasFiniteBiproducts T]
    {E'' : ExactStructure T} (F : ExactFunctor E E') (G : ExactFunctor E' E'') :
    ExactFunctor E E'' where
  toFunctor := F.toFunctor ⋙ G.toFunctor
  map_conflation S hs := G.map_conflation _ (F.map_conflation S hs)

variable {E : ExactStructure C} {E' : ExactStructure D} (F : ExactFunctor E E')

lemma map_deflation {X Y : C} (p : X ⟶ Y) (hp : E.deflation p) :
    E'.deflation (F.toFunctor.map p) := by
  obtain ⟨K, i, h, hs⟩ := hp
  exact E'.deflation_of_conflation (F.map_conflation _ hs)

lemma map_inflation {X Y : C} (i : X ⟶ Y) (hi : E.inflation i) :
    E'.inflation (F.toFunctor.map i) := by
  obtain ⟨K, p, h, hs⟩ := hi
  exact E'.inflation_of_conflation (F.map_conflation _ hs)

/-- Exact additive functors preserve pullback squares along admissible epimorphisms.
The proof applies exactness to the total kernel–cokernel pair of the square. -/
theorem map_isPullback {P A B T : C} {a : P ⟶ A} {b : P ⟶ B}
    {i : A ⟶ T} {p : B ⟶ T} (sq : IsPullback a b i p) (hp : E.deflation p) :
    IsPullback (F.toFunctor.map a) (F.toFunctor.map b)
      (F.toFunctor.map i) (F.toFunctor.map p) := by
  let S : ShortComplex C := ShortComplex.mk (biprod.lift a b) (biprod.desc (-i) p)
    (by simp only [biprod.lift_desc, comp_neg, sq.w, neg_add_cancel])
  have hs : E.conflation S := E.conflation_of_isKernel _ (pullbackMatrixKernel sq)
    (E.deflation_biprod_desc (-i) p hp)
  let hF := E'.kernel (S.map F.toFunctor) (F.map_conflation S hs)
  let pair (s : PullbackCone (F.toFunctor.map i) (F.toFunctor.map p)) :
      s.pt ⟶ F.toFunctor.obj (A ⊞ B) :=
    s.fst ≫ F.toFunctor.map biprod.inl + s.snd ≫ F.toFunctor.map biprod.inr
  have pair_zero (s : PullbackCone (F.toFunctor.map i) (F.toFunctor.map p)) :
      pair s ≫ F.toFunctor.map (biprod.desc (-i) p) = 0 := by
    dsimp only [pair]
    simp only [add_comp, Category.assoc, ← F.toFunctor.map_comp,
      biprod.inl_desc, biprod.inr_desc, F.toFunctor.map_neg, comp_neg,
      s.condition, neg_add_cancel]
  let cone (s : PullbackCone (F.toFunctor.map i) (F.toFunctor.map p)) :=
    KernelFork.ofι (pair s) (pair_zero s)
  have lift_fac (s : PullbackCone (F.toFunctor.map i) (F.toFunctor.map p)) :
      hF.lift (cone s) ≫ F.toFunctor.map (biprod.lift a b) = pair s :=
    hF.fac (cone s) WalkingParallelPair.zero
  have pair_fst (s : PullbackCone (F.toFunctor.map i) (F.toFunctor.map p)) :
      pair s ≫ F.toFunctor.map biprod.fst = s.fst := by
    simp [pair, ← F.toFunctor.map_comp]
  have pair_snd (s : PullbackCone (F.toFunctor.map i) (F.toFunctor.map p)) :
      pair s ≫ F.toFunctor.map biprod.snd = s.snd := by
    simp [pair, ← F.toFunctor.map_comp]
  have w : F.toFunctor.map a ≫ F.toFunctor.map i =
      F.toFunctor.map b ≫ F.toFunctor.map p := by
    simp only [← F.toFunctor.map_comp, sq.w]
  refine IsPullback.of_isLimit (PullbackCone.IsLimit.mk w
    (fun s => hF.lift (cone s)) ?_ ?_ ?_)
  · intro s
    have h := congrArg (fun k => k ≫ F.toFunctor.map biprod.fst) (lift_fac s)
    simpa only [Category.assoc, ← F.toFunctor.map_comp, biprod.lift_fst, pair_fst] using h
  · intro s
    have h := congrArg (fun k => k ≫ F.toFunctor.map biprod.snd) (lift_fac s)
    simpa only [Category.assoc, ← F.toFunctor.map_comp, biprod.lift_snd, pair_snd] using h
  · intro s m hm₁ hm₂
    let : Mono (F.toFunctor.map (biprod.lift a b)) := Fork.IsLimit.mono hF
    apply (cancel_mono (F.toFunctor.map (biprod.lift a b))).1
    rw [lift_fac]
    simp only [biprod.lift_eq, F.toFunctor.map_add, F.toFunctor.map_comp,
      comp_add, ← Category.assoc, hm₁, hm₂, pair]

/-- Preservation of pullbacks along admissible epimorphisms, expressed in
mathlib's standard limit-preservation language. -/
theorem preserves_pullback {A B T : C} (i : A ⟶ T) (p : B ⟶ T)
    (hp : E.deflation p) : PreservesLimit (cospan i p) F.toFunctor := by
  let : HasPullback p i := E.deflation.hasPullback i hp
  let : HasPullback i p := hasPullback_symmetry p i
  let sq := F.map_isPullback (IsPullback.of_hasPullback i p) hp
  apply preservesLimit_of_preserves_limit_cone (pullbackIsPullback i p)
  exact (PullbackCone.isLimitMapConeEquiv _ F.toFunctor).symm sq.isLimit

end ExactFunctor
end CategoryTheory.ExactCategory
