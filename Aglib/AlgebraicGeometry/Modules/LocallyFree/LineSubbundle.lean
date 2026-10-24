/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Modules.LocallyFree.Pullback
public import Aglib.AlgebraicGeometry.Modules.LocallyFree.Kernel
public import Aglib.AlgebraicGeometry.Modules.LocallyFree.RankAdditivity
public import Aglib.AlgebraicGeometry.Modules.Locality.Monomorphisms
public import Aglib.AlgebraicGeometry.Modules.Invertible.Affine
public import Aglib.AlgebraicGeometry.Modules.Invertible.Nonzero
public import Aglib.AlgebraicGeometry.Picard.Comparison.Endomorphisms
public import Mathlib.AlgebraicGeometry.ResidueField
public import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure

/-!
# Line subbundles from fibrewise nonzero maps

Let `N` be a locally rank-one module sheaf and `E` a finite locally free module sheaf on a scheme
`X`, and let `u : N ⟶ E` be nonzero on every field-valued fibre: `(pullback t).map u ≠ 0` for
every field `K` and every `t : Spec K ⟶ X`. Then `u` is locally split
(`exists_isSplitMono_pullback_map_of_ne_zero`): every point has an open immersion along which
the pulled back `u` is a split monomorphism. Consequently `u` is a monomorphism
(`mono_of_pullback_map_ne_zero`), its cokernel is finite locally free
(`isFiniteLocallyFree_cokernel_of_pullback_map_ne_zero`), of rank `r - 1` when `E` has
rank `r` (`sheafHasRank_cokernel_of_pullback_map_ne_zero`), and `0 → N → E → coker u → 0` is
short exact (`shortExact_cokernel_of_pullback_map_ne_zero`). Conversely, the first map of a short
exact sequence with locally rank-one first term and finite locally free last term is nonzero on
every field fibre (`pullback_map_f_ne_zero_of_shortExact`). Nonvanishing at algebraically closed
field points implies nonvanishing at all field points
(`pullback_map_ne_zero_of_isAlgClosed`).

This is the Nakayama step in the proof of Kleiman, *The Picard scheme*, arXiv:math/0504020v1,
Thm 3.13, p. 25 ("`u ⊗ k_t ≠ 0` ... `N` is invertible ... Hence, by Nakayama's lemma, `u` is
surjective"), in the dual form used when `LinSys` is represented by line subbundles of a
locally free `E` (Picard plan row F15). Over an affine base it is Stacks Project, Tag 00O0
(Algebra, Lemma 10.79.4). The proof is local: after trivializing `N` and `E` near a point, one
coordinate of `u` has nonzero residue there, hence is a unit on its basic open, and dividing by
that coordinate splits `u`. The scheme is arbitrary; no Noetherian, reducedness or
quasi-compactness hypothesis is used.
-/

@[expose] public section

noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

open CategoryTheory Limits AlgebraicGeometry Opposite TopologicalSpace
open AlgebraicGeometry.Scheme.Modules.Invertible

namespace AlgebraicGeometry.Scheme.Modules

section Coordinates

variable {V : Scheme.{u}} {I : Type u} [DecidableEq I]

/-- The coordinate projection of a free module sheaf onto its `i`-th summand. -/
def freeCoordinate (i : I) :
    SheafOfModules.free (R := V.ringCatSheaf) I ⟶ SheafOfModules.unit V.ringCatSheaf :=
  Sigma.desc (Pi.single i (𝟙 (SheafOfModules.unit V.ringCatSheaf)))

/-- The coordinate projections and the summand inclusions decompose the identity of a finite
free module sheaf. -/
theorem sum_freeCoordinate_comp_ιFree [Fintype I] :
    ∑ i, freeCoordinate (V := V) i ≫ SheafOfModules.ιFree i =
      𝟙 (SheafOfModules.free (R := V.ringCatSheaf) I) := by
  refine Sigma.hom_ext _ _ fun j => ?_
  rw [Preadditive.comp_sum, Finset.sum_eq_single j]
  · rw [freeCoordinate, Sigma.ι_comp_desc_assoc, Pi.single_eq_same, Category.id_comp]
    exact (Category.comp_id _).symm
  · intro b _ hb
    rw [freeCoordinate, Sigma.ι_comp_desc_assoc, Pi.single_eq_of_ne (Ne.symm hb), zero_comp]
  · intro h
    exact absurd (Finset.mem_univ j) h

end Coordinates

section Residue

variable {V : Scheme.{u}}

/-- Multiplication by a function that does not generate the unit ideal at the image point of a
field point pulls back to zero along that field point. -/
theorem pullback_map_globalScalarEndomorphism_eq_zero (M : V.Modules) (a : Γ(V, ⊤))
    (K : Type u) [Field K] (t : Spec (.of K) ⟶ V) (v : V)
    (htv : t (IsLocalRing.closedPoint K) = v) (hv : v ∉ V.basicOpen a) :
    (Scheme.Modules.pullback t).map (globalScalarEndomorphism V M a) = 0 := by
  let Y := Spec (CommRingCat.of K)
  have hzero : t.appTop a = 0 := by
    let : Field Γ(Y, ⊤) := (isField_of_isIntegral_of_subsingleton Y).toField
    apply (Y.Γevaluation (IsLocalRing.closedPoint K)).hom.injective
    rw [map_zero]
    have hn := Scheme.Γevaluation_naturality_apply t (IsLocalRing.closedPoint K) a
    have ha : V.Γevaluation (t (IsLocalRing.closedPoint K)) a = 0 := by
      rw [htv]
      exact (V.evaluation_eq_zero_iff_notMem_basicOpen (U := ⊤) v trivial a).mpr hv
    rw [ha, map_zero] at hn
    exact hn.symm
  rw [pullback_map_globalScalarEndomorphism, hzero]
  have hc : globalScalarCenter Y 0 = 0 := map_zero _
  exact congrArg (fun z : CatCenter Y.Modules ↦ z.app ((Scheme.Modules.pullback t).obj M)) hc

/-- If a map `O ⟶ O^I`, with `I` finite, is nonzero after pulling back along a field point, then
one of its coordinates is a unit at the image of that point. -/
theorem exists_mem_basicOpen_of_pullback_map_ne_zero {I : Type u} [Finite I] [DecidableEq I]
    (ψ : SheafOfModules.unit V.ringCatSheaf ⟶ SheafOfModules.free (R := V.ringCatSheaf) I)
    (K : Type u) [Field K] (t : Spec (.of K) ⟶ V)
    (hψ : (Scheme.Modules.pullback t).map ψ ≠ 0) (v : V)
    (htv : t (IsLocalRing.closedPoint K) = v) :
    ∃ i : I, v ∈ V.basicOpen
      (unitHomGlobalSectionsEquiv V (SheafOfModules.unit V.ringCatSheaf)
        (ψ ≫ freeCoordinate i)) := by
  by_contra hcon
  simp only [not_exists] at hcon
  apply hψ
  let := Fintype.ofFinite I
  have hsum : ψ = ∑ i, (ψ ≫ freeCoordinate i) ≫ SheafOfModules.ιFree i := by
    conv_lhs => rw [← Category.comp_id ψ, ← sum_freeCoordinate_comp_ιFree]
    rw [Preadditive.comp_sum]
    simp only [Category.assoc]
  rw [hsum, Functor.map_sum]
  refine Finset.sum_eq_zero fun i _ => ?_
  have hc : ψ ≫ freeCoordinate i =
      globalScalarEndomorphism V (SheafOfModules.unit V.ringCatSheaf)
        (unitHomGlobalSectionsEquiv V (SheafOfModules.unit V.ringCatSheaf)
          (ψ ≫ freeCoordinate i)) :=
    (globalScalarEndomorphism_unitHomGlobalSectionsEquiv (ψ ≫ freeCoordinate i)).symm
  rw [Functor.map_comp, hc,
    pullback_map_globalScalarEndomorphism_eq_zero _ _ K t v htv (hcon i), zero_comp]

/-- On an open contained in the basic open of the `i`-th coordinate of `ψ : O ⟶ O^I`, the map
`ψ` becomes a split monomorphism: dividing by that coordinate gives a retraction. -/
theorem isSplitMono_pullback_ι_map_of_le_basicOpen {I : Type u} [DecidableEq I]
    (ψ : SheafOfModules.unit V.ringCatSheaf ⟶ SheafOfModules.free (R := V.ringCatSheaf) I)
    (i : I) (W : V.Opens)
    (hW : W ≤ V.basicOpen (unitHomGlobalSectionsEquiv V (SheafOfModules.unit V.ringCatSheaf)
      (ψ ≫ freeCoordinate i))) :
    IsSplitMono ((Scheme.Modules.pullback W.ι).map ψ) := by
  set a := unitHomGlobalSectionsEquiv V (SheafOfModules.unit V.ringCatSheaf)
    (ψ ≫ freeCoordinate i) with ha
  have hunit : IsUnit (W.ι.appTop a) := by
    apply W.toScheme.toRingedSpace.isUnit_of_isUnit_germ ⊤ (W.ι.appTop a)
    intro w _
    have hw : w ∈ W.toScheme.basicOpen (W.ι.appTop a) := by
      rw [← Scheme.preimage_basicOpen_top]
      exact hW w.2
    exact (W.toScheme.mem_basicOpen_top (W.ι.appTop a) w).mp hw
  obtain ⟨b, hb⟩ := hunit
  have hc : ψ ≫ freeCoordinate i =
      globalScalarEndomorphism V (SheafOfModules.unit V.ringCatSheaf) a :=
    (globalScalarEndomorphism_unitHomGlobalSectionsEquiv (ψ ≫ freeCoordinate i)).symm
  have hiso : IsIso ((Scheme.Modules.pullback W.ι).map (ψ ≫ freeCoordinate i)) := by
    rw [hc, pullback_map_globalScalarEndomorphism, ← hb]
    exact inferInstanceAs (IsIso (globalScalarIso _ b).hom)
  rw [Functor.map_comp] at hiso
  exact IsSplitMono.mk' ⟨(Scheme.Modules.pullback W.ι).map (freeCoordinate i) ≫
    inv ((Scheme.Modules.pullback W.ι).map ψ ≫
      (Scheme.Modules.pullback W.ι).map (freeCoordinate i)),
    by rw [← Category.assoc, IsIso.hom_inv_id]⟩

end Residue

section LineSubbundle

/-- A morphism isomorphic, by conjugation with isomorphisms, to a split monomorphism is a split
monomorphism. -/
theorem isSplitMono_of_eq_iso_comp {C : Type*} [Category C] {A B A' B' : C} {f : A ⟶ B}
    {f' : A' ⟶ B'} (eA : A ≅ A') (eB : B' ≅ B) (h : f = eA.hom ≫ f' ≫ eB.hom)
    (hf' : IsSplitMono f') : IsSplitMono f :=
  IsSplitMono.mk' ⟨eB.inv ≫ retraction f' ≫ eA.inv, by simp [h]⟩

variable {X : Scheme.{u}} {N E : X.Modules}

/-- **Local splitting** (Kleiman, arXiv:math/0504020v1, Thm 3.13, proof, p. 25; Stacks Project,
Tag 00O0). A map from a locally rank-one module sheaf to a finite locally free one which is
nonzero on every field-valued fibre becomes a split monomorphism after pulling back along an
open immersion around any given point. -/
theorem exists_isSplitMono_pullback_map_of_ne_zero (hN : IsLocallyRankOne X N)
    [IsFiniteLocallyFree X E] (u : N ⟶ E)
    (hu : ∀ (K : Type u) [Field K] (t : Spec (.of K) ⟶ X),
      (Scheme.Modules.pullback t).map u ≠ 0)
    (x : X) :
    ∃ (W : Scheme.{u}) (k : W ⟶ X), IsOpenImmersion k ∧ x ∈ Set.range k ∧
      IsSplitMono ((Scheme.Modules.pullback k).map u) := by
  classical
  obtain ⟨U, hxU, G, hG, hfin⟩ :=
    finiteLocallyFree_iff_pointwise.mp (inferInstance : IsFiniteLocallyFree X E) x
  have : Finite G.I := hfin.finite
  let xU : U.toScheme := ⟨x, hxU⟩
  let NU := pullbackLineBundle U.ι ⟨N, hN⟩
  obtain ⟨V, hxV, ⟨eN'⟩⟩ := (isLocallyRankOne_iff_restrict_unit NU.val).mp NU.property xU
  let y : V.toScheme := ⟨xU, hxV⟩
  let eN : (Scheme.Modules.pullback (V.ι ≫ U.ι)).obj N ≅
      SheafOfModules.unit V.toScheme.ringCatSheaf :=
    (Scheme.Modules.pullbackComp V.ι U.ι).symm.app N ≪≫
      ((Scheme.Modules.restrictFunctorIsoPullback V.ι).app NU.val).symm ≪≫ eN'
  let eE : (Scheme.Modules.pullback (V.ι ≫ U.ι)).obj E ≅
      SheafOfModules.free (R := V.toScheme.ringCatSheaf) G.I :=
    (Scheme.Modules.pullbackComp V.ι U.ι).symm.app E ≪≫
      (Scheme.Modules.pullback V.ι).mapIso
        (((Scheme.Modules.restrictFunctorIsoPullback U.ι).app E).symm ≪≫
          (restrictBasisIso E U G).symm) ≪≫
      pullbackFreeIso V.ι G.I
  let ψ := eN.inv ≫ (Scheme.Modules.pullback (V.ι ≫ U.ι)).map u ≫ eE.hom
  have hm : (Scheme.Modules.pullback (V.ι ≫ U.ι)).map u = eN.hom ≫ ψ ≫ eE.inv := by
    simp [ψ]
  let t := V.toScheme.fromSpecResidueField y
  have hψ : (Scheme.Modules.pullback t).map ψ ≠ 0 := by
    intro h
    apply hu (V.toScheme.residueField y) (t ≫ V.ι ≫ U.ι)
    have h2 : (Scheme.Modules.pullback t).map
        ((Scheme.Modules.pullback (V.ι ≫ U.ι)).map u) = 0 := by
      rw [hm, Functor.map_comp, Functor.map_comp, h, zero_comp, comp_zero]
    rw [← NatIso.naturality_1 (Scheme.Modules.pullbackComp t (V.ι ≫ U.ι)) u, Functor.comp_map,
      h2, zero_comp, comp_zero]
  have hty : t (IsLocalRing.closedPoint (V.toScheme.residueField y)) = y :=
    Scheme.fromSpecResidueField_apply y _
  obtain ⟨i, hi⟩ := exists_mem_basicOpen_of_pullback_map_ne_zero ψ
    (V.toScheme.residueField y) t hψ y hty
  set W := V.toScheme.basicOpen (unitHomGlobalSectionsEquiv V.toScheme
    (SheafOfModules.unit V.toScheme.ringCatSheaf) (ψ ≫ freeCoordinate i)) with hW
  refine ⟨W.toScheme, W.ι ≫ V.ι ≫ U.ι, inferInstance, ⟨⟨y, hi⟩, ?_⟩, ?_⟩
  · simp [y, xU]
  · have h1 : IsSplitMono ((Scheme.Modules.pullback W.ι).map ψ) :=
      isSplitMono_pullback_ι_map_of_le_basicOpen ψ i W hW.le
    have h2 : IsSplitMono ((Scheme.Modules.pullback W.ι).map
        ((Scheme.Modules.pullback (V.ι ≫ U.ι)).map u)) :=
      isSplitMono_of_eq_iso_comp ((Scheme.Modules.pullback W.ι).mapIso eN)
        ((Scheme.Modules.pullback W.ι).mapIso eE.symm)
        (by rw [hm]; simp only [Functor.map_comp, Functor.mapIso_hom, Iso.symm_hom]) h1
    exact isSplitMono_of_eq_iso_comp
      ((Scheme.Modules.pullbackComp W.ι (V.ι ≫ U.ι)).app N).symm
      ((Scheme.Modules.pullbackComp W.ι (V.ι ≫ U.ι)).app E)
      (NatIso.naturality_1 (Scheme.Modules.pullbackComp W.ι (V.ι ≫ U.ι)) u).symm h2

/-- The cokernel of a split monomorphism between finite locally free module sheaves is finite
locally free: it is the kernel of the complementary split epimorphism. -/
theorem isFiniteLocallyFree_cokernel_of_isSplitMono {W : Scheme.{u}} {A B : W.Modules}
    (m : A ⟶ B) [IsSplitMono m] [IsFiniteLocallyFree W A] [IsFiniteLocallyFree W B] :
    IsFiniteLocallyFree W (cokernel m) := by
  let S := ShortComplex.mk m (cokernel.π m) (cokernel.condition m)
  have hS : S.Exact := ShortComplex.exact_of_g_is_cokernel (S := S) (cokernelIsCokernel m)
  let σ : S.Splitting := ShortComplex.Splitting.ofExactOfRetraction S hS (retraction m)
    (IsSplitMono.id m) (inferInstanceAs (Epi (cokernel.π m)))
  let S' := ShortComplex.mk σ.s σ.r σ.s_r
  let σ' : S'.Splitting :=
    { r := S.g
      s := S.f
      f_r := σ.s_g
      s_g := σ.f_r
      id := by rw [add_comm]; exact σ.id }
  have : IsFiniteLocallyFree W S'.X₂ := inferInstanceAs (IsFiniteLocallyFree W B)
  have : IsFiniteLocallyFree W S'.X₃ := inferInstanceAs (IsFiniteLocallyFree W A)
  exact finiteLocallyFree_X₁_of_shortExact σ'.shortExact

/-- A locally rank-one module sheaf has residue-field rank one at every point. -/
theorem sheafRank_eq_one_of_isLocallyRankOne {M : X.Modules} (hM : IsLocallyRankOne X M)
    (x : X) : sheafRank M x = 1 := by
  obtain ⟨q, hq, hr⟩ := hM
  have hf : ∀ i, Finite (q.generators i).I := fun i => Finite.of_equiv _ (hr i).some.symm
  obtain ⟨i, hi⟩ := (Opens.coversTop_iff X q.X).mp q.coversTop |>.exists_mem x
  rw [sheafRank_eq_card_of_mem M q hq hf x i hi, Nat.card_congr (hr i).some, Nat.card_unique]

/-- Nonvanishing on all algebraically closed field fibres implies nonvanishing on all field
fibres. -/
theorem pullback_map_ne_zero_of_isAlgClosed {M M' : X.Modules} (v : M ⟶ M')
    (h : ∀ (K : Type u) [Field K] [IsAlgClosed K] (t : Spec (.of K) ⟶ X),
      (Scheme.Modules.pullback t).map v ≠ 0)
    (K : Type u) [Field K] (t : Spec (.of K) ⟶ X) : (Scheme.Modules.pullback t).map v ≠ 0 := by
  intro h0
  let s : Spec (.of (AlgebraicClosure K)) ⟶ Spec (.of K) :=
    Spec.map (CommRingCat.ofHom (algebraMap K (AlgebraicClosure K)))
  apply h (AlgebraicClosure K) (s ≫ t)
  rw [← NatIso.naturality_1 (Scheme.Modules.pullbackComp s t) v, Functor.comp_map, h0,
    Functor.map_zero, zero_comp, comp_zero]

/-- **Converse.** The first map of a short exact sequence whose first term is locally rank one
and whose last term is finite locally free is nonzero on every field-valued fibre: pullback
keeps it a monomorphism out of a line bundle on `Spec K`. -/
theorem pullback_map_f_ne_zero_of_shortExact {S : ShortComplex X.Modules} (hS : S.ShortExact)
    (h₁ : IsLocallyRankOne X S.X₁) [IsFiniteLocallyFree X S.X₃] (K : Type u) [Field K]
    (t : Spec (.of K) ⟶ X) : (Scheme.Modules.pullback t).map S.f ≠ 0 := by
  have : Mono ((Scheme.Modules.pullback t).map S.f) := (shortExact_pullback t hS).mono_f
  exact lineBundleMap_ne_zero_of_mono (Spec (.of K)) (pullbackLineBundle t ⟨S.X₁, h₁⟩)
    ((Scheme.Modules.pullback t).map S.f)

variable (hN : IsLocallyRankOne X N) [IsFiniteLocallyFree X E] (u : N ⟶ E)
  (hu : ∀ (K : Type u) [Field K] (t : Spec (.of K) ⟶ X),
    (Scheme.Modules.pullback t).map u ≠ 0)
include hN hu

/-- A map from a locally rank-one module sheaf to a finite locally free one which is nonzero on
every field-valued fibre is a monomorphism. -/
theorem mono_of_pullback_map_ne_zero : Mono u := by
  choose W k hk hx hs using exists_isSplitMono_pullback_map_of_ne_zero hN u hu
  have : ∀ x, IsOpenImmersion (k x) := hk
  refine mono_of_restrict_openCover W k (fun x => ⟨x, Set.mem_range.mp (hx x)⟩) u fun x => ?_
  have := hs x
  exact mono_restrict_of_mono_pullback (k x) u

/-- The cokernel of a map from a locally rank-one module sheaf to a finite locally free one
which is nonzero on every field-valued fibre is finite locally free. -/
theorem isFiniteLocallyFree_cokernel_of_pullback_map_ne_zero :
    IsFiniteLocallyFree X (cokernel u) := by
  have : IsFiniteLocallyFree X N := isFiniteLocallyFree_of_isLocallyRankOne hN
  choose W k hk hx hs using exists_isSplitMono_pullback_map_of_ne_zero hN u hu
  have : ∀ x, IsOpenImmersion (k x) := hk
  refine finiteLocallyFree_of_openImmersionCover (cokernel u) W k
    (fun x => ⟨x, Set.mem_range.mp (hx x)⟩) fun x => ?_
  have := hs x
  have h1 : IsFiniteLocallyFree (W x) (cokernel ((Scheme.Modules.pullback (k x)).map u)) :=
    isFiniteLocallyFree_cokernel_of_isSplitMono _
  exact finiteLocallyFree_of_iso (h := h1)
    ((PreservesCokernel.iso (Scheme.Modules.pullback (k x)) u).symm ≪≫
      ((Scheme.Modules.restrictFunctorIsoPullback (k x)).app (cokernel u)).symm)

/-- `0 → N → E → coker u → 0` is short exact. -/
theorem shortExact_cokernel_of_pullback_map_ne_zero :
    (ShortComplex.mk u (cokernel.π u) (cokernel.condition u)).ShortExact := by
  have := mono_of_pullback_map_ne_zero hN u hu
  exact ⟨ShortComplex.exact_of_g_is_cokernel
    (S := ShortComplex.mk u (cokernel.π u) (cokernel.condition u)) (cokernelIsCokernel u)⟩

/-- If `E` has rank `r`, the cokernel has rank `r - 1`: it is a point of the Grassmannian of
rank-`(r - 1)` quotients of `E`. -/
theorem sheafHasRank_cokernel_of_pullback_map_ne_zero {r : ℕ} (hE : SheafHasRank E r) :
    SheafHasRank (cokernel u) (r - 1) := by
  have : IsFiniteLocallyFree X N := isFiniteLocallyFree_of_isLocallyRankOne hN
  have : IsFiniteLocallyFree X (cokernel u) :=
    isFiniteLocallyFree_cokernel_of_pullback_map_ne_zero hN u hu
  have hS := shortExact_cokernel_of_pullback_map_ne_zero hN u hu
  rw [sheafHasRank_iff_rank_eq]
  intro x
  have h1 := sheafRank_X₂_eq_add_of_shortExact hS x
  have h2 : sheafRank E x = r := (sheafHasRank_iff_rank_eq E r).mp hE x
  have h3 : sheafRank N x = 1 := sheafRank_eq_one_of_isLocallyRankOne hN x
  change sheafRank E x = sheafRank N x + sheafRank (cokernel u) x at h1
  omega

end LineSubbundle

end AlgebraicGeometry.Scheme.Modules
