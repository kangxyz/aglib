/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Mathlib.Algebra.Module.Presentation.Finite
public import Mathlib.Algebra.Category.ModuleCat.FilteredColimits
public import Mathlib.CategoryTheory.Limits.ConcreteCategory.Filtered

/-! # Maps from finitely presented modules into filtered colimits

Finite generators lift to a common stage of the supplied native cocone.
Finite relations vanish at a further common stage, where the native module
presentation constructs the required linear map. The conclusion retains the
original cocone leg. Ring, value, and index universes are independent.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace ModuleCat

universe r w i j

variable {R : Type r} [Ring R] {I : Type i} [Category.{j} I] [IsFiltered I]

/-- A map from a finitely presented module to an actual filtered colimit factors
through one of its original cocone legs. -/
theorem exists_factor_of_finitePresentation
    (D : I ⥤ ModuleCat.{w} R) (c : Cocone D) (hc : IsColimit c)
    [PreservesColimitsOfShape I (forget (ModuleCat.{w} R))]
    (M : ModuleCat.{w} R) [Module.FinitePresentation R M] (a : M ⟶ c.pt) :
    ∃ (i : I) (b : M ⟶ D.obj i), b ≫ c.ι.app i = a := by
  classical
  obtain ⟨pres, hG, hR⟩ :=
    (Module.finitePresentation_iff_exists_presentation.{0, 0}).mp
      (inferInstance : Module.FinitePresentation R M)
  let :=  hG
  let :=  hR
  let :=  Fintype.ofFinite pres.G
  have hgen (g : pres.G) : ∃ i z, c.ι.app i z = a (pres.var g) :=
    Types.jointly_surjective_of_isColimit
      (isColimitOfPreserves (forget (ModuleCat.{w} R)) hc) _
  choose idx z hz using hgen
  obtain ⟨i, hi⟩ := IsFiltered.sup_objs_exists (Finset.univ.image idx)
  let f (g : pres.G) : idx g ⟶ i :=
    (hi (Finset.mem_image_of_mem _ (Finset.mem_univ g))).some
  let v (g : pres.G) : D.obj i := D.map (f g) (z g)
  let l := Finsupp.linearCombination R v
  have hl : (c.ι.app i).hom ∘ₗ l = a.hom ∘ₗ pres.toSolution.π := by
    ext g
    simp only [LinearMap.coe_comp, Function.comp_apply, Finsupp.lsingle_apply,
      Finsupp.linearCombination_single, one_smul, l,
      Module.Relations.Solution.π_single]
    change (D.map (f g) ≫ c.ι.app i) (z g) = _
    rw [c.w (f g)]
    exact hz g
  have hrel (x : pres.R) : ∃ (k : I) (f : i ⟶ k), D.map f (l (pres.relation x)) = 0 := by
    have heq : c.ι.app i (l (pres.relation x)) = c.ι.app i 0 := by
      change ((c.ι.app i).hom ∘ₗ l) (pres.relation x) = _
      rw [hl]
      simp only [LinearMap.comp_apply, Module.Relations.Solution.π_relation, map_zero]
    obtain ⟨k, f, hf⟩ := (hc.eq_iff' _ _).mp heq
    exact ⟨k, f, by simpa only [map_zero] using hf⟩
  choose k q hq using hrel
  obtain ⟨j, p, t, ht⟩ := IsFiltered.wideSpan q
  let l' := (D.map p).hom ∘ₗ l
  have hl' (x : pres.R) : l' (pres.relation x) = 0 := by
    change D.map p (l (pres.relation x)) = 0
    rw [← ht x, D.map_comp]
    change D.map (t x) (D.map (q x) (l (pres.relation x))) = 0
    rw [hq x, map_zero]
  let sol : pres.toRelations.Solution (D.obj j) :=
    .ofπ l' hl'
  let b : M ⟶ D.obj j := ofHom (pres.toIsPresentation.desc sol)
  refine ⟨j, b, ?_⟩
  apply hom_ext
  apply pres.toIsPresentation.postcomp_injective
  ext g
  change c.ι.app j (pres.toIsPresentation.desc sol (pres.var g)) = a (pres.var g)
  rw [Module.Relations.Solution.IsPresentation.desc_var]
  change c.ι.app j (D.map p (l (Finsupp.single g 1))) = _
  change (D.map p ≫ c.ι.app j) (l (Finsupp.single g 1)) = _
  rw [c.w p]
  exact (LinearMap.congr_fun hl (Finsupp.single g 1)).trans (by simp)

end ModuleCat
