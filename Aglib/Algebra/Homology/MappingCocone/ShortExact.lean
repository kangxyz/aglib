/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aglib contributors
-/
module

public import Aglib.Algebra.Homology.MappingCocone.Map
public import Aglib.Algebra.Homology.MappingCone.Acyclicity
public import Mathlib.Algebra.Homology.HomologySequenceLemmas
public import Mathlib.Algebra.Homology.HomologicalComplexAbelian
public import Mathlib.Algebra.Homology.HomotopyCategory.ShiftSequence

/-!
# The original mapping cocone of an epimorphism

For a short exact sequence of integer cochain complexes, the native lift of
its first arrow to the mapping cocone of its second arrow is a quasi-isomorphism.
The proof identifies its cokernel with the original mapping cocone of the
identity. All complexes, shifts, maps and signs are those of Mathlib.
-/

@[expose] public noncomputable section

universe v u

open CategoryTheory CategoryTheory.Limits HomologicalComplex

namespace CochainComplex.mappingCocone

variable {C : Type u} [Category.{v} C]

section Preadditive

variable [Preadditive C] [HasBinaryBiproducts C]

/-- The native projections identify a mapping-cocone term with its two original terms. -/
def termIso {K L : CochainComplex C ℤ} (g : K ⟶ L) (n : ℤ) :
    (mappingCocone g).X n ≅ K.X n ⊞ L.X (n + -1) where
  hom := biprod.lift ((fst g).f n) ((snd g).v n (n + -1) rfl)
  inv := biprod.desc ((inl g).v n n (add_zero n))
    ((inr g).1.v (n + -1) n (by omega))
  hom_inv_id := by simp only [biprod.lift_desc]; exact id_X g n (n + -1) rfl
  inv_hom_id := by
    apply biprod.hom_ext <;> apply biprod.hom_ext' <;> simp

/-- On the original terms, the native cocone map is the block-diagonal map. -/
lemma termIso_naturality {K L K' L' : CochainComplex C ℤ}
    (g : K ⟶ L) (g' : K' ⟶ L') (a : K ⟶ K') (b : L ⟶ L')
    (h : g ≫ b = a ≫ g') (n : ℤ) :
    (termIso g n).hom ≫ biprod.map (a.f n) (b.f (n + -1)) =
      (map g g' a b h).f n ≫ (termIso g' n).hom := by
  apply biprod.hom_ext
  · have hn := congrArg (fun t => t.f n) (map_fst g g' a b h)
    simpa only [termIso, Category.assoc, biprod.map_fst, biprod.lift_fst,
      biprod.lift_fst_assoc,
      HomologicalComplex.comp_f] using hn.symm
  · simp [termIso]

/-- The literal zero-homotopy lift associated to a short complex. -/
def liftShortComplex (S : ShortComplex (CochainComplex C ℤ)) :
    S.X₁ ⟶ mappingCocone S.g :=
  lift S.g S.f 0 (by simp)

@[reassoc (attr := simp)]
lemma liftShortComplex_fst (S : ShortComplex (CochainComplex C ℤ)) :
    liftShortComplex S ≫ fst S.g = S.f := by
  simp [liftShortComplex]

end Preadditive

variable [Abelian C] (S : ShortComplex (CochainComplex C ℤ))

private def quotientMap : mappingCocone S.g ⟶ mappingCocone (𝟙 S.X₃) :=
  map S.g (𝟙 S.X₃) S.g (𝟙 S.X₃) (by simp)

private lemma quotientMap_f_fst (n : ℤ) :
    (quotientMap S).f n ≫ (fst (𝟙 S.X₃)).f n = (fst S.g).f n ≫ S.g.f n := by
  simpa only [quotientMap, HomologicalComplex.comp_f] using
    congrArg (fun t => t.f n) (map_fst S.g (𝟙 S.X₃) S.g (𝟙 S.X₃) (by simp))

private def quotientShortComplex : ShortComplex (CochainComplex C ℤ) :=
  ShortComplex.mk (liftShortComplex S) (quotientMap S) (by
    ext n
    apply ext_to_term (𝟙 S.X₃) n
    · simp only [HomologicalComplex.comp_f, HomologicalComplex.zero_f,
        Category.assoc, quotientMap_f_fst]
      simp [liftShortComplex, ← HomologicalComplex.comp_f]
    · simp [quotientMap, liftShortComplex, Category.assoc])

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
private lemma quotientShortComplex_shortExact (hS : S.ShortExact) :
    (quotientShortComplex S).ShortExact := by
  apply HomologicalComplex.shortExact_of_degreewise_shortExact
  intro n
  have hSn := (HomologicalComplex.shortExact_iff_degreewise_shortExact S).mp hS n
  have hmono : Mono (S.f.f n) := hSn.mono_f
  have hepi : Epi (S.g.f n) := hSn.epi_g
  let T := (quotientShortComplex S).map (HomologicalComplex.eval C (.up ℤ) n)
  have hfst : (liftShortComplex S).f n ≫ (fst S.g).f n = S.f.f n := by
    simp [liftShortComplex]
  have hm : Mono T.f := by
    change Mono ((liftShortComplex S).f n)
    exact mono_of_mono_fac hfst
  have he : Epi T.g := by
    change Epi ((quotientMap S).f n)
    rw [← epi_comp_iff_of_isIso _ (termIso (𝟙 S.X₃) n).hom]
    have hn := termIso_naturality S.g (𝟙 S.X₃) S.g (𝟙 S.X₃) (by simp) n
    rw [show (quotientMap S).f n ≫ (termIso (𝟙 S.X₃) n).hom =
      (termIso S.g n).hom ≫ biprod.map (S.g.f n) (𝟙 _) by simpa [quotientMap] using hn.symm]
    infer_instance
  have hkernel {W : C} (m : W ⟶ T.X₂) (hm : m ≫ T.g = 0) :
      (m ≫ (fst S.g).f n) ≫ S.g.f n = 0 := by
    change m ≫ (quotientMap S).f n = 0 at hm
    have h := congrArg (fun t => t ≫ (fst (𝟙 S.X₃)).f n) hm
    simpa only [Category.assoc, quotientMap_f_fst, zero_comp] using h
  have hsecond {W : C} (m : W ⟶ T.X₂) (hm : m ≫ T.g = 0) :
      m ≫ (snd S.g).v n (n + -1) rfl = 0 := by
    change m ≫ (quotientMap S).f n = 0 at hm
    have h := congrArg (fun t => t ≫ (snd (𝟙 S.X₃)).v n (n + -1) rfl) hm
    simpa only [quotientMap, Category.assoc, map_f_snd_v,
      HomologicalComplex.id_f, Category.comp_id, zero_comp] using h
  have hk : IsLimit (KernelFork.ofι T.f T.zero) := by
    refine KernelFork.IsLimit.ofι _ _ (fun {W} m hm =>
      hSn.fIsKernel.lift (KernelFork.ofι (m ≫ (fst S.g).f n) (hkernel m hm))) ?_ ?_
    · intro W m hm
      change _ ≫ (liftShortComplex S).f n = m
      apply ext_to_term S.g n
      · rw [Category.assoc, hfst]
        exact hSn.fIsKernel.fac
          (KernelFork.ofι (m ≫ (fst S.g).f n) (hkernel m hm)) WalkingParallelPair.zero
      · simpa only [Category.assoc, liftShortComplex, lift_f_snd_v,
          HomComplex.Cochain.zero_v, comp_zero] using (hsecond m hm).symm
    · intro W m hm t ht
      apply (cancel_mono (S.f.f n)).1
      change t ≫ (liftShortComplex S).f n = m at ht
      have ht' : t ≫ S.f.f n = m ≫ (fst S.g).f n := by
        have h := congrArg (fun z => z ≫ (fst S.g).f n) ht
        simpa only [Category.assoc, hfst] using h
      have hf := hSn.fIsKernel.fac
        (KernelFork.ofι (m ≫ (fst S.g).f n) (hkernel m hm)) WalkingParallelPair.zero
      exact ht'.trans hf.symm
  exact { exact := T.exact_of_f_is_kernel hk, mono_f := hm, epi_g := he }

/-- A short exact sequence gives a quasi-isomorphism to the original mapping
cocone of its epimorphism, using the literal native zero-homotopy lift. -/
theorem quasiIso_liftShortComplex (hS : S.ShortExact) :
    QuasiIso (liftShortComplex S) := by
  have hT := quotientShortComplex_shortExact S hS
  have hz (n : ℤ) : IsZero ((mappingCocone (𝟙 S.X₃)).homology n) := by
    have h := (HomologicalComplex.exactAt_iff_isZero_homology _ _).mp
      (mappingCone_acyclic_of_quasiIso (𝟙 S.X₃) (n + -1))
    exact h.of_iso ((CochainComplex.ShiftSequence.shiftIso C (-1) n (n + -1)
      (by omega)).app (mappingCone (𝟙 S.X₃)))
  rw [quasiIso_iff]
  intro n
  rw [quasiIsoAt_iff_isIso_homologyMap]
  have hm : Mono (homologyMap (liftShortComplex S) n) :=
    (hT.homology_exact₁ (n + -1) n (by simp)).mono_g ((hz (n + -1)).eq_of_src _ _)
  have he : Epi (homologyMap (liftShortComplex S) n) :=
    (hT.homology_exact₂ n).epi_f ((hz n).eq_of_tgt _ _)
  exact isIso_of_mono_of_epi _

end CochainComplex.mappingCocone
