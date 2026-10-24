/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Morphisms.Separated.Cover

/-!
# Separatedness of an open subscheme that is a disjoint union of separated opens

Let `f : P ⟶ S` be a morphism of schemes and `U ⊆ P` an open that is the union of pairwise
disjoint opens `V k`, each with `V k ⟶ S` separated. Then `U ⟶ S` is separated
(`isSeparated_ι_comp_of_iSup_eq_of_pairwise_disjoint`): the preimages of the `V k` form a cover
of `U` by pairwise disjoint opens, to which `isSeparated_of_cover_of_pairwise_disjoint` applies.
This is the disjoint-union case of Kleiman, *The Picard scheme*, arXiv:math/0504020v1, proof of
Thm 4.8, p. 28 ("Plainly an `S`-scheme is separated if it is a disjoint union of separated open
subschemes"), for an open subscheme of `P`; combined with `isSeparated_of_cover_of_disjoint_or_le`
it gives the separatedness of a scheme covered by opens that are disjoint or nested, each of which
is a disjoint union of separated opens.

The comparison of the preimage of `V k` in `U` with `V k` uses that `U.ι ⁻¹ᵁ V ⟶ U ⟶ P` has image
`V` for `V ≤ U` (`Scheme.Opens.range_ι_comp_ι_of_le`), and that, for two open immersions `j` and
`j'` into `P` with the same image, `j ≫ f` is separated if and only if `j' ≫ f` is
(`isSeparated_comp_iff_of_range_eq`, through Mathlib's `IsOpenImmersion.isoOfRangeEq`). No
finiteness or Noetherian hypothesis is used.
-/

@[expose] public section

open CategoryTheory Limits

universe u

namespace AlgebraicGeometry

variable {P S : Scheme.{u}}

/-- For opens `V ≤ U` of `P`, the open immersion `U.ι ⁻¹ᵁ V ⟶ U ⟶ P` has image `V`. -/
theorem Scheme.Opens.range_ι_comp_ι_of_le {U V : P.Opens} (h : V ≤ U) :
    Set.range ((U.ι ⁻¹ᵁ V).ι ≫ U.ι) = V := by
  have hr : ((U.ι ⁻¹ᵁ V).ι ≫ U.ι).opensRange = V := by
    rw [Scheme.Hom.opensRange_comp, Scheme.Opens.opensRange_ι,
      Scheme.Hom.image_preimage_eq_opensRange_inf, Scheme.Opens.opensRange_ι, inf_eq_right.mpr h]
  exact congrArg SetLike.coe hr

/-- For two open immersions into `P` with the same image, separatedness over `S` of one is that of
the other: they differ by an isomorphism of their sources. -/
theorem isSeparated_comp_iff_of_range_eq {V V' : Scheme.{u}} (j : V ⟶ P) (j' : V' ⟶ P)
    [IsOpenImmersion j] [IsOpenImmersion j'] (hj : Set.range j = Set.range j') (f : P ⟶ S) :
    IsSeparated (j ≫ f) ↔ IsSeparated (j' ≫ f) := by
  rw [← IsOpenImmersion.isoOfRangeEq_hom_fac j j' hj, Category.assoc]
  constructor
  · intro hsep
    have : IsSeparated ((IsOpenImmersion.isoOfRangeEq j j' hj).inv ≫
        (IsOpenImmersion.isoOfRangeEq j j' hj).hom ≫ j' ≫ f) := inferInstance
    rwa [Iso.inv_hom_id_assoc] at this
  · intro hsep
    infer_instance

/-- **An open that is a disjoint union of separated opens is separated**: if the pairwise disjoint
opens `V k` of `P` have union `U` and every `V k ⟶ S` is separated, then `U ⟶ S` is separated
(Kleiman, arXiv:math/0504020v1, proof of Thm 4.8, p. 28, disjoint unions). -/
theorem isSeparated_ι_comp_of_iSup_eq_of_pairwise_disjoint (f : P ⟶ S) (U : P.Opens) {κ : Type*}
    (V : κ → P.Opens) (hV : ⨆ k, V k = U) (hsep : ∀ k, IsSeparated ((V k).ι ≫ f))
    (hd : Pairwise (Function.onFun Disjoint V)) : IsSeparated (U.ι ≫ f) := by
  have hle (k : κ) : V k ≤ U := hV ▸ le_iSup V k
  refine isSeparated_of_cover_of_pairwise_disjoint (U.ι ≫ f) (fun k => U.ι ⁻¹ᵁ V k) ?_ ?_ ?_
  · change ⨆ k, U.ι ⁻¹ᵁ V k = ⊤
    rw [← Scheme.Hom.preimage_iSup, hV, Scheme.Opens.ι_preimage_self]
  · intro k
    change IsSeparated ((U.ι ⁻¹ᵁ V k).ι ≫ U.ι ≫ f)
    have hrange : Set.range (V k).ι = Set.range ((U.ι ⁻¹ᵁ V k).ι ≫ U.ι) := by
      rw [Scheme.Opens.range_ι, Scheme.Opens.range_ι_comp_ι_of_le (hle k)]
    have := hsep k
    rw [← Category.assoc]
    exact (isSeparated_comp_iff_of_range_eq _ _ hrange f).mp this
  · intro k l hkl
    change Disjoint (U.ι ⁻¹ᵁ V k) (U.ι ⁻¹ᵁ V l)
    rw [disjoint_iff, ← Scheme.Hom.preimage_inf, disjoint_iff.mp (hd hkl), Scheme.Hom.preimage_bot]

end AlgebraicGeometry
