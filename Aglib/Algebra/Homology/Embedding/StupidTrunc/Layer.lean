/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Aglib.Algebra.Homology.Embedding.StupidTrunc.Transition
public import Mathlib.Algebra.Homology.Single
/-! # The genuine one-term cofiber of adjacent brutal truncations

The displayed sequence uses the original nested inclusion and the original
term identification to project onto the existing single-complex functor.
It is short exact and split in each degree for every ambient complex.
Neither boundedness nor any projectivity hypothesis is needed.
-/
@[expose] public section

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Limits HomologicalComplex
universe v u
namespace CochainComplex
variable {A : Type u} [Category.{v} A] [Abelian A]

/-- The original degree-n term, placed in degree n using the existing single functor. -/
abbrev stupidTruncGELayerFunctor (n : ℤ) : CochainComplex A ℤ ⥤ CochainComplex A ℤ :=
  eval A (ComplexShape.up ℤ) n ⋙ single A (ComplexShape.up ℤ) n

/-- The actual projection to the original single-term quotient. -/
def stupidTruncGELayerProjection (K : CochainComplex A ℤ) (n : ℤ) :
    stupidTruncGE K n ⟶ (stupidTruncGELayerFunctor n).obj K :=
  mkHomToSingle (stupidTruncGEXIso K n n le_rfl).hom (fun i hi ↦
    (stupidTruncGE_isZero_X K n i (by change i + 1 = n at hi; omega)).eq_of_src _ _)

@[simp]
theorem stupidTruncGELayerProjection_f (K : CochainComplex A ℤ) (n : ℤ) :
    (stupidTruncGELayerProjection K n).f n =
      (stupidTruncGEXIso K n n le_rfl).hom ≫
        (singleObjXSelf (ComplexShape.up ℤ) n (K.X n)).inv :=
  mkHomToSingle_f _ _

/-- The projection is natural for the original chain-map components. -/
@[reassoc]
theorem stupidTruncGELayerProjection_naturality {K L : CochainComplex A ℤ}
    (f : K ⟶ L) (n : ℤ) :
    (stupidTruncGEFunctor n).map f ≫ stupidTruncGELayerProjection L n =
      stupidTruncGELayerProjection K n ≫ (stupidTruncGELayerFunctor n).map f := by
  apply to_single_hom_ext
  have h := congrArg (fun t ↦ t.f n) (stupidTruncGEInclusion_naturality f n)
  simp only [comp_f, stupidTruncGEInclusion_f_of_le K n n le_rfl,
    stupidTruncGEInclusion_f_of_le L n n le_rfl] at h
  simpa only [comp_f, stupidTruncGELayerProjection_f, Functor.comp_map,
    single_map_f_self, eval_obj, eval_map, Category.assoc, Iso.inv_hom_id_assoc] using
    congrArg (fun t ↦ t ≫ (singleObjXSelf (ComplexShape.up ℤ) n (L.X n)).inv) h

/-- The actual natural quotient map of the existing functors. -/
def stupidTruncGELayerProjectionNat (n : ℤ) :
    stupidTruncGEFunctor (A := A) n ⟶ stupidTruncGELayerFunctor n where
  app K := stupidTruncGELayerProjection K n
  naturality _ _ f := stupidTruncGELayerProjection_naturality f n

/-- The original adjacent inclusion is annihilated by the original term projection. -/
@[reassoc (attr := simp)]
theorem stupidTruncGELayer_zero (K : CochainComplex A ℤ) (n : ℤ) :
    stupidTruncGETransition K (by omega : n ≤ n + 1) ≫ stupidTruncGELayerProjection K n = 0 := by
  apply to_single_hom_ext
  exact (stupidTruncGE_isZero_X K (n + 1) n (by omega)).eq_of_src _ _

/-- The displayed adjacent brutal-truncation sequence, with unchanged maps. -/
def stupidTruncGELayerSequence (K : CochainComplex A ℤ) (n : ℤ) :
    ShortComplex (CochainComplex A ℤ) :=
  ShortComplex.mk (stupidTruncGETransition K (by omega : n ≤ n + 1))
    (stupidTruncGELayerProjection K n) (stupidTruncGELayer_zero K n)

/-- The actual one-step layer sequence is short exact in every degree. -/
theorem stupidTruncGELayerSequence_degree_shortExact (K : CochainComplex A ℤ) (n i : ℤ) :
    ((stupidTruncGELayerSequence K n).map (eval A (ComplexShape.up ℤ) i)).ShortExact := by
  let S := (stupidTruncGELayerSequence K n).map (eval A (ComplexShape.up ℤ) i)
  let : IsSplitMono S.f := stupidTruncGETransition_degreewiseSplitMono K (by omega : n ≤ n + 1) i
  by_cases hi : i = n
  · subst i
    have hπ : IsIso S.g := by
      change IsIso ((stupidTruncGELayerProjection K n).f n)
      rw [stupidTruncGELayerProjection_f]
      infer_instance
    exact {
      mono_f := inferInstance
      epi_g := inferInstance
      exact := (ShortComplex.exact_iff_mono S
        ((stupidTruncGE_isZero_X K (n + 1) n (by omega)).eq_of_src _ _)).2 inferInstance }
  · have hz := isZero_single_obj_X (ComplexShape.up ℤ) n (K.X n) i hi
    refine { mono_f := inferInstance, epi_g := hz.epi S.g, exact := ?_ }
    by_cases hni : n + 1 ≤ i
    · have hf : IsIso S.f := by
        change IsIso (stupidTruncGETransitionF K (by omega : n ≤ n + 1) i)
        simp only [stupidTruncGETransitionF, dite_eq_left hni]
        infer_instance
      exact (ShortComplex.exact_iff_epi S (hz.eq_of_tgt _ _)).2 inferInstance
    · exact ShortComplex.exact_of_isZero_X₂ S (stupidTruncGE_isZero_X K n i (by omega))

/-- The displayed sequence is an actual short exact sequence of complexes. -/
theorem stupidTruncGELayerSequence_shortExact (K : CochainComplex A ℤ) (n : ℤ) :
    (stupidTruncGELayerSequence K n).ShortExact :=
  (shortExact_iff_degreewise_shortExact _).2 (stupidTruncGELayerSequence_degree_shortExact K n)

/-- Its first arrow is split degreewise, with no chain-map retraction asserted. -/
theorem stupidTruncGELayerSequence_degreewiseSplitMono (K : CochainComplex A ℤ) (n : ℤ) :
    degreewiseSplitMono (stupidTruncGELayerSequence K n).f :=
  stupidTruncGETransition_degreewiseSplitMono K (by omega : n ≤ n + 1)

/-- An actual splitting of each degree of the displayed cofiber sequence. -/
def stupidTruncGELayerSequenceSplitting (K : CochainComplex A ℤ) (n i : ℤ) :
    ((stupidTruncGELayerSequence K n).map (eval A (ComplexShape.up ℤ) i)).Splitting := by
  let S := (stupidTruncGELayerSequence K n).map (eval A (ComplexShape.up ℤ) i)
  let : IsSplitMono S.f := stupidTruncGETransition_degreewiseSplitMono K (by omega : n ≤ n + 1) i
  have hs := stupidTruncGELayerSequence_degree_shortExact K n i
  exact ShortComplex.Splitting.ofExactOfRetraction S hs.exact (retraction S.f)
    (IsSplitMono.id S.f) hs.epi_g

/-- The actual chosen cokernel is canonically the displayed original single complex. -/
def stupidTruncGELayerCokernelIso (K : CochainComplex A ℤ) (n : ℤ) :
    cokernel (stupidTruncGELayerSequence K n).f ≅ (stupidTruncGELayerFunctor n).obj K :=
  (cokernelIsCokernel _).coconePointUniqueUpToIso (stupidTruncGELayerSequence_shortExact K
    n).gIsCokernel

@[reassoc (attr := simp)]
theorem stupidTruncGELayerCokernelIso_projection (K : CochainComplex A ℤ) (n : ℤ) :
    cokernel.π (stupidTruncGELayerSequence K n).f ≫ (stupidTruncGELayerCokernelIso K n).hom =
      stupidTruncGELayerProjection K n :=
  (cokernelIsCokernel _).comp_coconePointUniqueUpToIso_hom
    (stupidTruncGELayerSequence_shortExact K n).gIsCokernel WalkingParallelPair.one

end CochainComplex
