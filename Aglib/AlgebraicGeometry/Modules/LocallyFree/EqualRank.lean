/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Modules.LocallyFree.Kernel
public import Aglib.AlgebraicGeometry.Modules.LocallyFree.RankAdditivity
public import Aglib.AlgebraicGeometry.Modules.Locality.Exactness

/-!
# Epimorphisms between finite locally free sheaves of equal rank

* `isZero_of_sheafHasRank_zero`: a sheaf of modules with a local basis of rank zero is zero; on
  each member of the cover it is isomorphic to the free sheaf on the empty type.
* `isIso_of_epi_of_sheafHasRank`: an epimorphism `f : M ⟶ N` between sheaves of modules of the
  same constant rank `k` is an isomorphism. Its kernel is finite locally free
  (`finiteLocallyFree_X₁_of_shortExact`), of rank `k - k = 0` at every point by additivity of the
  fibre ranks (`sheafRank_X₂_eq_add_of_shortExact`), hence zero.
* `exists_iso_of_kernel_ι_comp_eq_zero_of_sheafHasRank`: for two quotients `q : free I ⟶ Q` and
  `q' : free I ⟶ Q'` of the same constant rank with `ker q ⊆ ker q'`, the induced surjection
  `Q ⟶ Q'` is an isomorphism under `free I`.

This is the step "a surjection of locally free sheaves of the same rank is an isomorphism" in the
proof that the Grassmannian point of a pulled-back universal family is the given map (Nitsure,
*Construction of Hilbert and Quot schemes*, arXiv:math/0504590v1, §5, pp. 26–27). The analogous
statement for modules is the surjective-endomorphism property of finite modules
(Stacks, Tag 05G8); here it is obtained from ranks, without Nakayama.
-/

@[expose] public section

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Scheme.Modules

variable {X : Scheme.{u}}

/-- **A sheaf of modules of rank zero is zero**: a local basis with empty generator types makes
the sheaf zero on every member of a cover of `X`. -/
theorem isZero_of_sheafHasRank_zero {M : X.Modules} (h : SheafHasRank M 0) : IsZero M := by
  obtain ⟨q, hq, hn⟩ := h
  refine isZero_of_restrict_openCover (fun i => Scheme.Opens.toScheme (X := X) (q.X i))
    (fun i => Scheme.Opens.ι (X := X) (q.X i)) (fun x => ?_) M fun i => ?_
  · obtain ⟨i, hi⟩ := ((Opens.coversTop_iff X q.X).mp q.coversTop).exists_mem x
    exact ⟨i, ⟨x, hi⟩, rfl⟩
  · have : IsEmpty (q.generators i).I := (hn i).some.isEmpty
    have h0 : IsZero (SheafOfModules.free (R := X.ringCatSheaf.over (q.X i))
        (q.generators i).I) :=
      (IsZero.iff_id_eq_zero _).mpr
        (Cofan.IsColimit.hom_ext (SheafOfModules.isColimitFreeCofan _) _ _ fun j => isEmptyElim j)
    have := hq.isIso i
    have h1 : IsZero (M.over (q.X i)) := h0.of_iso (asIso (q.generators i).π).symm
    exact ((overEquiv (q.X i)).functor.map_isZero h1).of_iso
      ((overFunctorEquiv (q.X i)).app M).symm

/-- **An epimorphism between sheaves of modules of the same constant rank is an isomorphism**:
its kernel is finite locally free of rank zero. -/
theorem isIso_of_epi_of_sheafHasRank {M N : X.Modules} (f : M ⟶ N) [Epi f] {k : ℕ}
    (hM : SheafHasRank M k) (hN : SheafHasRank N k) : IsIso f := by
  have := hM.isFiniteLocallyFree
  have := hN.isFiniteLocallyFree
  let S := ShortComplex.mk (kernel.ι f) f (kernel.condition f)
  have hS : S.ShortExact :=
    { exact := ShortComplex.exact_of_f_is_kernel _ (kernelIsKernel f)
      mono_f := inferInstanceAs (Mono (kernel.ι f))
      epi_g := inferInstanceAs (Epi f) }
  have : IsFiniteLocallyFree X S.X₂ := inferInstanceAs (IsFiniteLocallyFree X M)
  have : IsFiniteLocallyFree X S.X₃ := inferInstanceAs (IsFiniteLocallyFree X N)
  have : IsFiniteLocallyFree X S.X₁ := finiteLocallyFree_X₁_of_shortExact hS
  have h0 : SheafHasRank (kernel f) 0 := (sheafHasRank_iff_rank_eq (kernel f) 0).mpr fun x => by
    have h := sheafRank_X₂_eq_add_of_shortExact hS x
    have hM' := (sheafHasRank_iff_rank_eq M k).mp hM x
    have hN' := (sheafHasRank_iff_rank_eq N k).mp hN x
    change sheafRank M x = sheafRank (kernel f) x + sheafRank N x at h
    omega
  have : Mono f := Preadditive.mono_of_isZero_kernel _ (isZero_of_sheafHasRank_zero h0)
  exact isIso_of_mono_of_epi f

-- As in its former home `HilbertScheme/EqualRank`: `free I` is a `SheafOfModules` and the
-- zero morphisms come from `X.Modules`.
set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- **Equal rank**: for two rank-`k` locally free quotients `q : free I ⟶ Q` and
`q' : free I ⟶ Q'` with `ker q ⊆ ker q'`, the induced surjection `Q ⟶ Q'` is an isomorphism
under `free I`. -/
theorem exists_iso_of_kernel_ι_comp_eq_zero_of_sheafHasRank {I : Type u} {k : ℕ}
    {Q Q' : X.Modules}
    (q : SheafOfModules.free I ⟶ Q) [Epi q] (q' : SheafOfModules.free I ⟶ Q') [Epi q']
    (hQ : SheafHasRank Q k) (hQ' : SheafHasRank Q' k) (h : kernel.ι q ≫ q' = 0) :
    ∃ i : Q ≅ Q', q ≫ i.hom = q' := by
  let c := Abelian.epiIsCokernelOfKernel _ (kernelIsKernel q)
  let d := c.desc (CokernelCofork.ofπ q' h)
  have hd : q ≫ d = q' := c.fac (CokernelCofork.ofπ q' h) WalkingParallelPair.one
  have : Epi d := epi_of_epi_fac hd
  have := isIso_of_epi_of_sheafHasRank d hQ hQ'
  exact ⟨asIso d, hd⟩

end AlgebraicGeometry.Scheme.Modules
