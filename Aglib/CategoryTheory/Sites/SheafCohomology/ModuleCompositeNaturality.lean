/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.CategoryTheory.Sites.SheafCohomology.ModuleComposite

/-! # Complete naturality of the original module/cohomology composite

Three independently proved squares are assembled on opaque original carriers:
the section map, the pre-coefficient comparison, and the final coefficient map.
The two sites, value universes, Ext ranges and scalar rings remain independent.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Abelian

universe c v a e r m h c' v' a' e' r' m' h'

namespace CategoryTheory.Sheaf

variable {C : Type c} [Category.{v} C] {J : GrothendieckTopology C}
  [HasSheafify J AddCommGrpCat.{a}] [HasExt.{e} (Sheaf J AddCommGrpCat.{a})]
  {R : Type r} [Ring R] {M N : ModuleCat.{m} R}
  {H : Type h} [AddCommGroup H] [Module R H]
  {F G : Sheaf J AddCommGrpCat.{a}}
  {C' : Type c'} [Category.{v'} C'] {J' : GrothendieckTopology C'}
  [HasSheafify J' AddCommGrpCat.{a'}] [HasExt.{e'} (Sheaf J' AddCommGrpCat.{a'})]
  {R' : Type r'} [Ring R'] {M' N' : ModuleCat.{m'} R'}
  {H' : Type h'} [AddCommGroup H'] [Module R' H']
  {F' G' : Sheaf J' AddCommGrpCat.{a'}}

/-- The complete original composite is natural when its separate original
section, pre-coefficient and final coefficient squares commute. -/
theorem moduleCohomologyComposite_naturality
    (q q' : ℕ) (i : M ≅ N) (l : N ≃ₗ[R] H)
    (E : H ≃+ Sheaf.H.{e} F q) (β : F ≅ G)
    (i' : M' ≅ N') (l' : N' ≃ₗ[R'] H')
    (E' : H' ≃+ Sheaf.H.{e'} F' q') (β' : F' ≅ G')
    (s : M → M') (w : M → N')
    (k : Sheaf.H.{e} F q → Sheaf.H.{e'} F' q')
    (t : Sheaf.H.{e} G q → Sheaf.H.{e'} G' q')
    (hs : ∀ x, i'.hom (s x) = w x)
    (hm : ∀ x, E' (l' (w x)) = k (E (l (i.hom x))))
    (hβ : ∀ z, Sheaf.H.map β'.hom q' (k z) = t (Sheaf.H.map β.hom q z))
    (x : M) :
    moduleCohomologyComposite q' i' l' E' β' (s x) =
      t (moduleCohomologyComposite q i l E β x) := by
  simp only [moduleCohomologyComposite_apply]
  exact (congrArg (fun y => Sheaf.H.map β'.hom q' (E' (l' y))) (hs x)).trans
    ((congrArg (Sheaf.H.map β'.hom q') (hm x)).trans (hβ (E (l (i.hom x)))))

end CategoryTheory.Sheaf
