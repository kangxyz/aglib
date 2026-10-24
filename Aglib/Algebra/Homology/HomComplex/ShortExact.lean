/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.Algebra.Homology.HomComplex.Precomposition
public import Mathlib.Algebra.Homology.ShortComplex.Ab
public import Mathlib.Algebra.Homology.HomologySequenceLemmas
public import Mathlib.CategoryTheory.ConcreteCategory.EpiMono

/-!
# Native contravariant Hom-complex exactness

A genuine short exact sequence of source complexes gives the original
reversed short exact sequence of Hom complexes into a termwise-injective
target. Exactness is proved by degreewise cokernel descent of cochains;
no extension of cycles or chain maps is assumed.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe v u

namespace CochainComplex.HomComplex

variable {C : Type u} [Category.{v} C] [Abelian C]

@[simp]
lemma precompMap_zero (K L I : CochainComplex C ℤ) :
    precompMap (0 : K ⟶ L) I = 0 := by
  ext n z
  change (Cochain.ofHom (0 : K ⟶ L)).comp z (zero_add n) = 0
  rw [Cochain.ofHom_zero]
  exact Cochain.zero_comp z (zero_add n)

/-- The component equation of the original precomposition cochain. -/
lemma precompCochain_v {K L I : CochainComplex C ℤ} (f : K ⟶ L)
    {n : ℤ} (z : Cochain L I n) (p q : ℤ) (hpq : p + n = q) :
    ((Cochain.ofHom f).comp z (zero_add n)).v p q hpq = f.f p ≫ z.v p q hpq :=
  (Cochain.zero_cochain_comp_v (Cochain.ofHom f) z p q hpq).trans
    (congrArg (fun a => a ≫ z.v p q hpq) (Cochain.ofHom_v f p))

/-- The original reversed precomposition maps form a short complex. -/
def precompShortComplex (S : ShortComplex (CochainComplex C ℤ)) (I : CochainComplex C ℤ) :
    ShortComplex (CochainComplex AddCommGrpCat.{v} ℤ) :=
  ShortComplex.mk (precompMap S.g I) (precompMap S.f I) (by
    rw [← precompMap_comp, S.zero, precompMap_zero])

/-- A termwise-injective target makes the original contravariant Hom complex exact. -/
theorem precompShortComplex_shortExact (S : ShortComplex (CochainComplex C ℤ))
    (hS : S.ShortExact) (I : CochainComplex C ℤ) [∀ n, Injective (I.X n)] :
    (precompShortComplex S I).ShortExact := by
  have : Mono S.f := hS.mono_f
  have : Epi S.g := hS.epi_g
  have hep (p : ℤ) : Epi (S.g.f p) :=
    (HomologicalComplex.eval C (.up ℤ) p).map_epi S.g
  have hdeg (p : ℤ) : (S.map (HomologicalComplex.eval C (.up ℤ) p)).ShortExact :=
    hS.map (HomologicalComplex.eval C (.up ℤ) p)
  have hep' (p : ℤ) : Epi (S.map (HomologicalComplex.eval C (.up ℤ) p)).g :=
    (hdeg p).epi_g
  apply HomologicalComplex.shortExact_of_degreewise_shortExact
  intro n
  let T := (precompShortComplex S I).map (HomologicalComplex.eval AddCommGrpCat.{v} (.up ℤ) n)
  change T.ShortExact
  have : Mono T.f := by
    apply ConcreteCategory.mono_of_injective
    intro z z' hz
    change (Cochain.ofHom S.g).comp z (zero_add n) =
      (Cochain.ofHom S.g).comp z' (zero_add n) at hz
    apply Cochain.ext
    intro p q hpq
    apply (cancel_epi (S.g.f p)).1
    exact (precompCochain_v S.g z p q hpq).symm.trans
      ((Cochain.congr_v hz p q hpq).trans (precompCochain_v S.g z' p q hpq))
  have : Epi T.g := by
    change Epi ((precompMap S.f I).f n)
    exact ConcreteCategory.epi_of_surjective _ (precompMap_surjective S.f I n)
  refine ⟨(T.ab_exact_iff).mpr ?_⟩
  intro z hz
  change (Cochain.ofHom S.f).comp z (zero_add n) = 0 at hz
  have hk (p q : ℤ) (hpq : p + n = q) : S.f.f p ≫ z.v p q hpq = 0 := by
    exact (precompCochain_v S.f z p q hpq).symm.trans
      (Cochain.congr_v hz p q hpq)
  let b : Cochain S.X₃ I n := Cochain.mk (fun p q hpq =>
    (hdeg p).exact.desc (z.v p q hpq) (hk p q hpq))
  refine ⟨b, ?_⟩
  change (Cochain.ofHom S.g).comp b (zero_add n) = z
  apply Cochain.ext
  intro p q hpq
  simp only [Cochain.zero_cochain_comp_v, Cochain.ofHom_v, b, Cochain.mk_v]
  exact (hdeg p).exact.g_desc (z.v p q hpq) (hk p q hpq)

/-- The actual middle Hom complex is acyclic when both end Hom complexes are acyclic. -/
theorem acyclic_middle_of_shortExact (S : ShortComplex (CochainComplex C ℤ))
    (hS : S.ShortExact) (I : CochainComplex C ℤ) [∀ n, Injective (I.X n)]
    (h₁ : (HomComplex S.X₃ I).Acyclic) (h₃ : (HomComplex S.X₁ I).Acyclic) :
    (HomComplex S.X₂ I).Acyclic :=
  (precompShortComplex_shortExact S hS I).acyclic_X₂ h₁ h₃

end CochainComplex.HomComplex
