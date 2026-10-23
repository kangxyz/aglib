/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.Algebra.Homology.DerivedCategory.Plus.SingleTriangle
public import Aglib.Algebra.Homology.DerivedCategory.Plus.Postnikov.Layers
public import Mathlib.CategoryTheory.Abelian.DiagramLemmas.Four
public import Mathlib.CategoryTheory.Preadditive.Injective.Basic
public import Mathlib.CategoryTheory.Abelian.Exact

/-! # Injective tests for original bounded-below triangulated comparisons

A shift-compatible natural transformation between triangulated functors is
invertible on all original source singles if it is invertible on injective
singles and both functors send source singles to nonnegative objects. The
proof uses only native single triangles, their native long exact sequences,
and finite degree induction. No convergence or ordinary H0 comparison premise
is used, and no assertion about unbounded models is made.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated
open CategoryTheory.ComposableArrows

namespace DerivedCategory.Plus.InjectiveComparison

universe u v u' v' dC dD

variable {C : Type u} [Category.{v} C] [Abelian C] [HasDerivedCategory.{dC} C]
  [EnoughInjectives C]
  {D : Type u'} [Category.{v'} D] [Abelian D] [HasDerivedCategory.{dD} D]
  (F G : DerivedCategory.Plus C ⥤ DerivedCategory.Plus D)
  [F.CommShift ℤ] [G.CommShift ℤ] [F.IsTriangulated] [G.IsTriangulated]
  (α : F ⟶ G) [NatTrans.CommShift α ℤ]

/-- The original shift-compatible natural transformation gives the original
componentwise morphism between the two mapped triangles. -/
def triangleMap (T : Triangle (DerivedCategory.Plus C)) :
    F.mapTriangle.obj T ⟶ G.mapTriangle.obj T where
  hom₁ := α.app T.obj₁
  hom₂ := α.app T.obj₂
  hom₃ := α.app T.obj₃
  comm₁ := α.naturality T.mor₁
  comm₂ := α.naturality T.mor₂
  comm₃ := by
    dsimp
    simp only [Category.assoc, NatTrans.shift_app_comm α (1 : ℤ) T.obj₁,
      NatTrans.naturality_assoc]

/-- The native six-term homology sequences carry their original comparison
maps, including the actual connecting-map naturality square. -/
def homologyLadder (T : Triangle (DerivedCategory.Plus C)) (n : ℤ) :
    (homologyFunctor D 0).homologySequenceComposableArrows₅
        (F.mapTriangle.obj T) n (n + 1) rfl ⟶
      (homologyFunctor D 0).homologySequenceComposableArrows₅
        (G.mapTriangle.obj T) n (n + 1) rfl := by
  let φ := triangleMap F G α T
  refine homMk₅
    (((homologyFunctor D 0).shift n).map φ.hom₁)
    (((homologyFunctor D 0).shift n).map φ.hom₂)
    (((homologyFunctor D 0).shift n).map φ.hom₃)
    (((homologyFunctor D 0).shift (n + 1)).map φ.hom₁)
    (((homologyFunctor D 0).shift (n + 1)).map φ.hom₂)
    (((homologyFunctor D 0).shift (n + 1)).map φ.hom₃) ?_ ?_ ?_ ?_ ?_
  · change ((homologyFunctor D 0).shift n).map (F.mapTriangle.obj T).mor₁ ≫
        ((homologyFunctor D 0).shift n).map φ.hom₂ =
      ((homologyFunctor D 0).shift n).map φ.hom₁ ≫
        ((homologyFunctor D 0).shift n).map (G.mapTriangle.obj T).mor₁
    simpa only [Functor.map_comp] using
      congrArg (((homologyFunctor D 0).shift n).map) φ.comm₁
  · change ((homologyFunctor D 0).shift n).map (F.mapTriangle.obj T).mor₂ ≫
        ((homologyFunctor D 0).shift n).map φ.hom₃ =
      ((homologyFunctor D 0).shift n).map φ.hom₂ ≫
        ((homologyFunctor D 0).shift n).map (G.mapTriangle.obj T).mor₂
    simpa only [Functor.map_comp] using
      congrArg (((homologyFunctor D 0).shift n).map) φ.comm₂
  · change (homologyFunctor D 0).homologySequenceδ (F.mapTriangle.obj T) n (n + 1) rfl ≫
        ((homologyFunctor D 0).shift (n + 1)).map φ.hom₁ =
      ((homologyFunctor D 0).shift n).map φ.hom₃ ≫
        (homologyFunctor D 0).homologySequenceδ (G.mapTriangle.obj T) n (n + 1) rfl
    exact ((homologyFunctor D 0).homologySequenceδ_naturality φ n (n + 1) rfl).symm
  · change ((homologyFunctor D 0).shift (n + 1)).map (F.mapTriangle.obj T).mor₁ ≫
        ((homologyFunctor D 0).shift (n + 1)).map φ.hom₂ =
      ((homologyFunctor D 0).shift (n + 1)).map φ.hom₁ ≫
        ((homologyFunctor D 0).shift (n + 1)).map (G.mapTriangle.obj T).mor₁
    simpa only [Functor.map_comp] using
      congrArg (((homologyFunctor D 0).shift (n + 1)).map) φ.comm₁
  · change ((homologyFunctor D 0).shift (n + 1)).map (F.mapTriangle.obj T).mor₂ ≫
        ((homologyFunctor D 0).shift (n + 1)).map φ.hom₃ =
      ((homologyFunctor D 0).shift (n + 1)).map φ.hom₂ ≫
        ((homologyFunctor D 0).shift (n + 1)).map (G.mapTriangle.obj T).mor₂
    simpa only [Functor.map_comp] using
      congrArg (((homologyFunctor D 0).shift (n + 1)).map) φ.comm₂

/-- One degree of full coefficient comparison gives monicity in the next
degree on every source single, using a native injective presentation. -/
theorem homology_mono_successor
    (hI : ∀ (I : C) [Injective I],
      IsIso (α.app ((singleFunctor C 0).obj I)))
    (n : ℤ)
    (hPrev : ∀ Y : C,
      IsIso ((homologyFunctor D n).map (α.app ((singleFunctor C 0).obj Y))))
    (Y : C) :
    Mono ((homologyFunctor D (n + 1)).map (α.app ((singleFunctor C 0).obj Y))) := by
  obtain ⟨P⟩ := EnoughInjectives.presentation Y
  let S : ShortComplex C := ShortComplex.mk P.f (cokernel.π P.f) (cokernel.condition P.f)
  have hS : S.ShortExact := { exact := ShortComplex.exact_cokernel P.f }
  let T := hS.singleTrianglePlus
  let φ := homologyLadder F G α T n
  have hF := (homologyFunctor D 0).homologySequenceComposableArrows₅_exact
    (F.mapTriangle.obj T) (F.map_distinguished T hS.singleTrianglePlus_distinguished)
    n (n + 1) rfl
  have hG := (homologyFunctor D 0).homologySequenceComposableArrows₅_exact
    (G.mapTriangle.obj T) (G.map_distinguished T hS.singleTrianglePlus_distinguished)
    n (n + 1) rfl
  have h₁ : Epi (app' φ 1) := by
    change Epi ((homologyFunctor D n).map (α.app ((singleFunctor C 0).obj P.J)))
    have := hPrev P.J
    infer_instance
  have h₂ : Mono (app' φ 2) := by
    change Mono ((homologyFunctor D n).map
      (α.app ((singleFunctor C 0).obj (cokernel P.f))))
    have := hPrev (cokernel P.f)
    exact IsIso.mono_of_iso _
  have h₄ : Mono (app' φ 4) := by
    change Mono ((homologyFunctor D (n + 1)).map (α.app ((singleFunctor C 0).obj P.J)))
    have := hI P.J
    infer_instance
  exact Abelian.mono_of_epi_of_mono_of_mono''
    (k := 1) (by decide : 1 + 3 ≤ 5) hF hG φ 1 2 3 4 rfl rfl rfl rfl h₁ h₂ h₄

/-- The native opposite four lemma upgrades the just-proved next-degree
monicity to full invertibility in that degree for every source single. -/
theorem homology_isIso_successor
    (hI : ∀ (I : C) [Injective I],
      IsIso (α.app ((singleFunctor C 0).obj I)))
    (n : ℤ)
    (hPrev : ∀ Y : C,
      IsIso ((homologyFunctor D n).map (α.app ((singleFunctor C 0).obj Y))))
    (Y : C) :
    IsIso ((homologyFunctor D (n + 1)).map (α.app ((singleFunctor C 0).obj Y))) := by
  have : Mono ((homologyFunctor D (n + 1)).map
      (α.app ((singleFunctor C 0).obj Y))) := homology_mono_successor F G α hI n hPrev Y
  obtain ⟨P⟩ := EnoughInjectives.presentation Y
  let S : ShortComplex C := ShortComplex.mk P.f (cokernel.π P.f) (cokernel.condition P.f)
  have hS : S.ShortExact := { exact := ShortComplex.exact_cokernel P.f }
  let T := hS.singleTrianglePlus
  let φ := homologyLadder F G α T n
  have hF := (homologyFunctor D 0).homologySequenceComposableArrows₅_exact
    (F.mapTriangle.obj T) (F.map_distinguished T hS.singleTrianglePlus_distinguished)
    n (n + 1) rfl
  have hG := (homologyFunctor D 0).homologySequenceComposableArrows₅_exact
    (G.mapTriangle.obj T) (G.map_distinguished T hS.singleTrianglePlus_distinguished)
    n (n + 1) rfl
  have h₂ : Epi (app' φ 2) := by
    change Epi ((homologyFunctor D n).map
      (α.app ((singleFunctor C 0).obj (cokernel P.f))))
    have := hPrev (cokernel P.f)
    infer_instance
  have h₄ : Epi (app' φ 4) := by
    change Epi ((homologyFunctor D (n + 1)).map (α.app ((singleFunctor C 0).obj P.J)))
    have := hI P.J
    infer_instance
  have h₅ : Mono (app' φ 5) := by
    change Mono ((homologyFunctor D (n + 1)).map
      (α.app ((singleFunctor C 0).obj (cokernel P.f))))
    exact homology_mono_successor F G α hI n hPrev (cokernel P.f)
  have : Epi ((homologyFunctor D (n + 1)).map
      (α.app ((singleFunctor C 0).obj Y))) :=
    Abelian.epi_of_epi_of_epi_of_mono''
      (k := 2) (by decide : 2 + 3 ≤ 5) hF hG φ 2 3 4 5 rfl rfl rfl rfl h₂ h₄ h₅
  exact isIso_of_mono_of_epi _

omit [EnoughInjectives C] [F.CommShift ℤ] [G.CommShift ℤ]
  [F.IsTriangulated] [G.IsTriangulated] [NatTrans.CommShift α ℤ] in
/-- Nonnegative images of source singles have zero negative homology, so
any actual comparison map between them is invertible in negative degrees. -/
theorem homology_isIso_negative
    (hF : ∀ Y : C, (F.obj ((singleFunctor C 0).obj Y)).IsGE 0)
    (hG : ∀ Y : C, (G.obj ((singleFunctor C 0).obj Y)).IsGE 0)
    (Y : C) (n : ℤ) (hn : n < 0) :
    IsIso ((homologyFunctor D n).map (α.app ((singleFunctor C 0).obj Y))) := by
  have := hF Y
  have := hG Y
  exact (isZero_homology_of_isGE (F.obj ((singleFunctor C 0).obj Y)) 0 n hn).isIso
    (isZero_homology_of_isGE (G.obj ((singleFunctor C 0).obj Y)) 0 n hn) _

/-- Invertibility on actual injective singles extends to every actual source
single by finite degree induction, retaining independent derived-category universes.
The left t-exactness inputs concern the actual images of these singles only. -/
theorem isIso_app_single_of_injective
    (hF : ∀ Y : C, (F.obj ((singleFunctor C 0).obj Y)).IsGE 0)
    (hG : ∀ Y : C, (G.obj ((singleFunctor C 0).obj Y)).IsGE 0)
    (hI : ∀ (I : C) [Injective I],
      IsIso (α.app ((singleFunctor C 0).obj I))) (Y : C) :
    IsIso (α.app ((singleFunctor C 0).obj Y)) := by
  have hNat : ∀ n : ℕ, ∀ Z : C,
      IsIso ((homologyFunctor D (n : ℤ)).map (α.app ((singleFunctor C 0).obj Z))) := by
    intro n
    induction n with
    | zero =>
      exact homology_isIso_successor F G α hI (-1)
        (fun Z => homology_isIso_negative F G α hF hG Z (-1) (by omega))
    | succ n hn =>
      exact homology_isIso_successor F G α hI (n : ℤ) hn
  apply (DerivedCategory.Plus.isIso_iff _).mpr
  intro n
  by_cases hn : n < 0
  · exact homology_isIso_negative F G α hF hG Y n hn
  · have he : (n.toNat : ℤ) = n := Int.toNat_of_nonneg (by omega)
    rw [← he]
    exact hNat n.toNat Y

end DerivedCategory.Plus.InjectiveComparison
