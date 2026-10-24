/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Picard.Scheme.Glue
public import Aglib.AlgebraicGeometry.Morphisms.Separated.DisjointUnion
public import Aglib.AlgebraicGeometry.ProjectiveSpace.QuasiProjective.Coproduct

/-!
# The stratification of the Picard scheme

In the setting of [Glue](Glue.lean) (`i : X ⟶ P^N_A` a closed immersion with `ι ≃ Fin (N + 1)`,
`p = i ≫ toSpec A ι` flat with geometrically integral fibres, and the representability premise
`h : Strata.FineStrataRepresentableByHQuasiProjective i N e`), write `ξ` for the universal section
of `Pic_{X/S,(fppf)}` over the Picard scheme `P = picardScheme h`. This file proves the
decomposition of Kleiman, *The Picard scheme*, arXiv:math/0504020v1, Thm 4.8 (2), pp. 27–28
("a disjoint union of open subschemes, each an increasing union of open quasi-projective
`S`-schemes"), with the strata of the proof, pp. 28–29:

* `picardStratumOpens h φ`, the open of `eulerCondition φ` of `ξ` (Kleiman's `P^φ`), is open and
  closed (`isClopen_picardStratumOpens`); these opens are pairwise disjoint
  (`pairwise_disjoint_picardStratumOpens`) and cover `P` (`iSup_picardStratumOpens`; p. 29: "the
  `T^φ` are disjoint and cover `T`");
* `picardLevelOpens h φ m`, the open of `coarseCondition φ m` of `ξ` (`P^φ_m`, with the
  nonvanishing condition `H^0(X_t, L_t(m)) ≠ 0`), increases with `m`
  (`monotone_picardLevelOpens`), with union `picardStratumOpens h φ` (`iSup_picardLevelOpens`;
  p. 29: "a nested sequence of open subschemes ... whose union is `T`");
* `picardBaseLevelOpens h φ ψ m` refines `picardLevelOpens h φ m` by the base polynomial `ψ`; it is
  the disjoint union over `k` of the chart images `(fineCondition φ ψ m (k + 1)).opens ξ`
  (`iSup_fineCondition_opens_eq_picardBaseLevelOpens`, `pairwise_disjoint_fineCondition_opens`);
* the functorial meaning: a morphism `a : T ⟶ P` lands in the open of a fibre condition `C` if and
  only if its section lies in `Pic^C(T)` (`picardSchemeRepresentableBy_homEquiv_mem_iff`, from
  `FiberCondition.map_mem_subfunctor_iff`), in particular for `Pic^φ` and `Pic^φ_m`.

**H-quasi-projectivity of `Pic^φ_m`**
(`isHQuasiProjective_picardLevelOpens_of_finiteFineStrataRanks`; Kleiman p. 29: "it suffices to
represent each `P^φ_m` by a quasi-projective `S`-scheme"). Over a Noetherian `A`,
`picardLevelOpens h φ m` is the disjoint union of the chart images over `(ψ, k)`, each isomorphic to
an H-quasi-projective chart, and only finitely many are nonempty
(`finite_setOf_fineCondition_holds_of_finiteFineStrataRanks`), so the finite disjoint union lemma
`IsHQuasiProjective.of_iSup_eq_top_of_pairwise_disjoint` applies. The finiteness has two parts:

* `ψ` takes finitely many values on the Noetherian base
  (`finite_setOf_exists_hasFiberStructureEulerPolynomial`);
* for fixed `(φ₀, ψ)` only finitely many ranks `k + 1 = h^0(X_t, L_t)` occur on the fine strata at
  level `0`: this is the premise `Strata.FiniteFineStrataRanks i N e`, transported to level `m` by
  the twist (`fineCondition_zero_holds_add_twistClass_iff`). The representability premise
  describes each rank separately and gives no bound on the ranks. Kleiman's proof (p. 30) does not
  fix the rank: there `P^{φ₀}_0` is represented by a quasi-projective quotient of the single
  quasi-projective open `Z = P^{φ₀}_0 ×_P Div_{X/S}` of `Div_{X/S}`, which lies in `Hilb^θ`. In the
  refined form the opens `Z_r = Pic^{φ₀,ψ,r}_0 ×_P Div^θ`, `θ = ψ - φ₀`, of the single Noetherian
  scheme `Div^θ` are pairwise disjoint, so only finitely many are nonempty, and
  `Z_r ⟶ Pic^{φ₀,ψ,r}_0` is surjective (`Strata.finiteFineStrataRanks`,
  [Representability/FineStrata](../Representability/FineStrata.lean)).
-/

@[expose] public section

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
open AlgebraicGeometry.ProjectiveSpace
open AlgebraicGeometry.Scheme.LocalRepresentability

namespace AlgebraicGeometry.Scheme.RelativePicard

namespace Strata

variable {A : Type u} [CommRing A] {ι : Type u} {X : Scheme.{u}}
  (i : X ⟶ ProjectiveSpace A ι) [IsClosedImmersion i] [Flat (i ≫ toSpec A ι)]
  (N : ℕ) (e : ι ≃ Fin (N + 1))

/-- **Finitely many ranks on the fine strata at level `0`**: for all `φ₀, ψ ∈ ℚ[X]`, only finitely
many `k` admit a line bundle on a fibre satisfying `fineCondition φ₀ ψ 0 (k + 1)`, that is,
`χ(X_t, L_t^{-1}(n)) = φ₀(n)`, `χ(X_t, O_{X_t}(n)) = ψ(n)`, `H^q(X_t, L_t(n)) = 0` for `q ≥ 1` and
`n ≥ 0`, and `h^0(X_t, L_t) = k + 1`. In Kleiman, arXiv:math/0504020v1, proof of Thm 4.8, p. 30,
the corresponding stratum `P^{φ₀}_0` is represented by one quasi-projective, hence quasi-compact,
scheme, on which the locally constant rank takes finitely many values. -/
def FiniteFineStrataRanks : Prop :=
  ∀ φ₀ ψ : Polynomial ℚ, {k : ℕ | ∃ (T : Over (Spec (.of A)))
    (a : (familyPicardFunctor (i ≫ toSpec A ι)).obj (op T)) (t : T.left),
      (fineCondition i N e φ₀ ψ 0 (k + 1)).Holds T a t}.Finite

end Strata

open Strata

variable {A : Type u} [CommRing A] {ι : Type u} {X : Scheme.{u}}
  {i : X ⟶ ProjectiveSpace A ι} [IsClosedImmersion i] [Flat (i ≫ toSpec A ι)]
  [GeometricallyIntegral (i ≫ toSpec A ι)] {N : ℕ} {e : ι ≃ Fin (N + 1)}
  (h : FineStrataRepresentableByHQuasiProjective i N e)

/-! ### The functorial meaning of the open loci -/

/-- **Fibre conditions on the Picard scheme**: a morphism `a : T ⟶ P` pulls the universal section
into `Pic^C` if and only if it factors through the open of `C` of the universal section (Kleiman,
arXiv:math/0504020v1, pp. 28–29: "`T^φ` represents `P^φ ×_P T`"). -/
theorem picardSchemeRepresentableBy_homEquiv_mem_iff (C : FiberCondition (i ≫ toSpec A ι))
    {T : Scheme.LocallyNoetherianOver (Spec (.of A))} (a : T ⟶ picardScheme h) :
    (picardSchemeRepresentableBy h).homEquiv a ∈ C.subfunctor.obj (op T.obj) ↔
      a.hom.left ⁻¹ᵁ C.opens (picardUniversalSection h) = ⊤ :=
  C.map_mem_subfunctor_iff (picardUniversalSection h) a.hom

/-! ### The strata `Pic^φ` -/

/-- **The stratum `Pic^φ`** of the Picard scheme: the open where the universal section satisfies
`χ(X_t, L_t^{-1}(n)) = φ(n)` (Kleiman, arXiv:math/0504020v1, p. 28, (4.8.1)). -/
def picardStratumOpens (φ : Polynomial ℚ) : (picardScheme h).obj.left.Opens :=
  (eulerCondition i N e φ).opens (picardUniversalSection h)

/-- `Pic^φ` is open and closed. -/
theorem isClopen_picardStratumOpens (φ : Polynomial ℚ) :
    IsClopen (picardStratumOpens h φ : Set (picardScheme h).obj.left) :=
  isClopen_setOf_holdsAt_eulerCondition (picardUniversalSection h) φ

/-- **The `Pic^φ` are pairwise disjoint** (Kleiman, arXiv:math/0504020v1, p. 29). -/
theorem pairwise_disjoint_picardStratumOpens :
    Pairwise (Function.onFun Disjoint (picardStratumOpens h)) :=
  fun _ _ hφ => disjoint_opens_eulerCondition (picardUniversalSection h) hφ

/-- **The `Pic^φ` cover the Picard scheme** (Kleiman, arXiv:math/0504020v1, p. 29). -/
theorem iSup_picardStratumOpens : ⨆ φ, picardStratumOpens h φ = ⊤ :=
  iSup_opens_eulerCondition (picardUniversalSection h)

/-- A morphism `a : T ⟶ P` lands in `Pic^φ` if and only if its section lies in `Pic^φ(T)`. -/
theorem picardSchemeRepresentableBy_homEquiv_mem_eulerCondition_iff (φ : Polynomial ℚ)
    {T : Scheme.LocallyNoetherianOver (Spec (.of A))} (a : T ⟶ picardScheme h) :
    (picardSchemeRepresentableBy h).homEquiv a ∈
        (eulerCondition i N e φ).subfunctor.obj (op T.obj) ↔
      a.hom.left ⁻¹ᵁ picardStratumOpens h φ = ⊤ :=
  picardSchemeRepresentableBy_homEquiv_mem_iff h _ a

/-! ### The levels `Pic^φ_m` -/

/-- **The level `Pic^φ_m`** of the stratum `Pic^φ`: the open where the universal section
satisfies (4.8.1), (4.8.3) for `n ≥ m`, and `H^0(X_t, L_t(m)) ≠ 0` (Kleiman,
arXiv:math/0504020v1, p. 29, with the nonvanishing condition). -/
def picardLevelOpens (φ : Polynomial ℚ) (m : ℤ) : (picardScheme h).obj.left.Opens :=
  (coarseCondition i N e φ m).opens (picardUniversalSection h)

/-- **The levels increase with `m`** (Kleiman, arXiv:math/0504020v1, p. 29). -/
theorem monotone_picardLevelOpens (φ : Polynomial ℚ) : Monotone (picardLevelOpens h φ) :=
  fun _ _ hm => opens_coarseCondition_mono (picardUniversalSection h) φ hm

/-- **The levels cover the stratum**: `⋃_m Pic^φ_m = Pic^φ` (Kleiman, arXiv:math/0504020v1,
p. 29). -/
theorem iSup_picardLevelOpens (φ : Polynomial ℚ) :
    ⨆ m, picardLevelOpens h φ m = picardStratumOpens h φ :=
  iSup_opens_coarseCondition (picardUniversalSection h) φ

theorem picardLevelOpens_le_picardStratumOpens (φ : Polynomial ℚ) (m : ℤ) :
    picardLevelOpens h φ m ≤ picardStratumOpens h φ :=
  (coarseCondition i N e φ m).opens_mono (fun _ _ _ hc => hc.1) (picardUniversalSection h)

/-- A morphism `a : T ⟶ P` lands in `Pic^φ_m` if and only if its section lies in `Pic^φ_m(T)`. -/
theorem picardSchemeRepresentableBy_homEquiv_mem_coarseCondition_iff (φ : Polynomial ℚ) (m : ℤ)
    {T : Scheme.LocallyNoetherianOver (Spec (.of A))} (a : T ⟶ picardScheme h) :
    (picardSchemeRepresentableBy h).homEquiv a ∈
        (coarseCondition i N e φ m).subfunctor.obj (op T.obj) ↔
      a.hom.left ⁻¹ᵁ picardLevelOpens h φ m = ⊤ :=
  picardSchemeRepresentableBy_homEquiv_mem_iff h _ a

/-! ### The refinement by the base polynomial and the rank -/

/-- The open `Pic^{φ,ψ}_m`: the part of `Pic^φ_m` where `χ(X_t, O_{X_t}(n)) = ψ(n)`. -/
def picardBaseLevelOpens (φ ψ : Polynomial ℚ) (m : ℤ) : (picardScheme h).obj.left.Opens :=
  picardLevelOpens h φ m ⊓ (baseCondition i N e ψ).opens (picardUniversalSection h)

/-- The chart image of `⟨φ, ψ, m, k⟩` is the open of `fineCondition φ ψ m (k + 1)`. -/
theorem range_picardChart_mk (φ ψ : Polynomial ℚ) (m : ℤ) (k : ℕ) :
    Set.range ((picardSubfunctorCover h).ιp (ULift.up (φ, ψ, m, k))).hom.left =
      SetLike.coe ((fineCondition i N e φ ψ m (k + 1)).opens (picardUniversalSection h)) :=
  range_picardChart h _

theorem fineCondition_opens_le_baseCondition_opens (φ ψ : Polynomial ℚ) (m : ℤ) (r : ℕ) :
    (fineCondition i N e φ ψ m r).opens (picardUniversalSection h) ≤
      (baseCondition i N e ψ).opens (picardUniversalSection h) :=
  (fineCondition i N e φ ψ m r).opens_mono (fun _ _ _ hc => hc.2.1) (picardUniversalSection h)

theorem fineCondition_opens_le_picardLevelOpens (φ ψ : Polynomial ℚ) (m : ℤ) (k : ℕ) :
    (fineCondition i N e φ ψ m (k + 1)).opens (picardUniversalSection h) ≤
      picardLevelOpens h φ m :=
  opens_fineCondition_le_coarseCondition (picardUniversalSection h) φ ψ m (Nat.succ_ne_zero k)

theorem fineCondition_opens_le_picardBaseLevelOpens (φ ψ : Polynomial ℚ) (m : ℤ) (k : ℕ) :
    (fineCondition i N e φ ψ m (k + 1)).opens (picardUniversalSection h) ≤
      picardBaseLevelOpens h φ ψ m :=
  le_inf (fineCondition_opens_le_picardLevelOpens h φ ψ m k)
    (fineCondition_opens_le_baseCondition_opens h φ ψ m (k + 1))

/-- **`Pic^{φ,ψ}_m` is the union of the chart images of the ranks `k + 1`.** -/
theorem iSup_fineCondition_opens_eq_picardBaseLevelOpens (φ ψ : Polynomial ℚ) (m : ℤ) :
    ⨆ k : ℕ, (fineCondition i N e φ ψ m (k + 1)).opens (picardUniversalSection h) =
      picardBaseLevelOpens h φ ψ m := by
  apply le_antisymm
  · exact iSup_le fun k => fineCondition_opens_le_picardBaseLevelOpens h φ ψ m k
  · rintro y ⟨hyc, hyb⟩
    have hy : y ∈ ⨆ x : Polynomial ℚ × ℕ,
        (fineCondition i N e φ x.1 m (x.2 + 1)).opens (picardUniversalSection h) := by
      rw [iSup_opens_fineCondition_eq_coarseCondition]
      exact hyc
    obtain ⟨⟨ψ', k⟩, hk⟩ := TopologicalSpace.Opens.mem_iSup.mp hy
    obtain rfl : ψ' = ψ := by
      by_contra hne
      have hb' := fineCondition_opens_le_baseCondition_opens h φ ψ' m (k + 1) hk
      simpa using (disjoint_opens_baseCondition (picardUniversalSection h) hne).le_bot ⟨hb', hyb⟩
    exact TopologicalSpace.Opens.mem_iSup.mpr ⟨k, hk⟩

/-- For fixed `(φ, m)`, the chart images of distinct `(ψ, k)` are disjoint. -/
theorem disjoint_fineCondition_opens (φ : Polynomial ℚ) (m : ℤ) {x y : Polynomial ℚ × ℕ}
    (hxy : x ≠ y) :
    Disjoint ((fineCondition i N e φ x.1 m (x.2 + 1)).opens (picardUniversalSection h))
      ((fineCondition i N e φ y.1 m (y.2 + 1)).opens (picardUniversalSection h)) := by
  refine disjoint_opens_fineCondition (picardUniversalSection h) fun heq => hxy ?_
  simp only [Prod.mk.injEq, add_left_inj, true_and] at heq
  exact Prod.ext heq.1 heq.2

/-- For fixed `(φ, ψ, m)`, the chart images of distinct ranks are disjoint. -/
theorem pairwise_disjoint_fineCondition_opens (φ ψ : Polynomial ℚ) (m : ℤ) :
    Pairwise (Function.onFun Disjoint fun k : ℕ =>
      (fineCondition i N e φ ψ m (k + 1)).opens (picardUniversalSection h)) :=
  fun k l hkl => disjoint_fineCondition_opens h φ m (x := (ψ, k)) (y := (ψ, l))
    fun heq => hkl (congrArg Prod.snd heq)

/-! ### Finiteness and H-quasi-projectivity of `Pic^φ_m` -/

omit [GeometricallyIntegral (i ≫ toSpec A ι)] in
/-- **Finitely many fine strata in `Pic^φ_m`**: over a Noetherian `A`, under
`FiniteFineStrataRanks`, only finitely many `(ψ, k)` admit a point of a family satisfying
`fineCondition φ ψ m (k + 1)`. The base polynomials form a finite set on the Noetherian base
(`finite_setOf_exists_hasFiberStructureEulerPolynomial`), and the twist carries the level `m` to
the level `0` (`fineCondition_zero_holds_add_twistClass_iff`). -/
theorem finite_setOf_fineCondition_holds_of_finiteFineStrataRanks [IsNoetherianRing A]
    (hrank : FiniteFineStrataRanks i N e) (φ : Polynomial ℚ) (m : ℤ) :
    {x : Polynomial ℚ × ℕ | ∃ (T : Over (Spec (.of A)))
      (a : (familyPicardFunctor (i ≫ toSpec A ι)).obj (op T)) (t : T.left),
        (fineCondition i N e φ x.1 m (x.2 + 1)).Holds T a t}.Finite := by
  refine ((finite_setOf_exists_hasFiberStructureEulerPolynomial i N e).biUnion fun ψ _ =>
    (Set.finite_singleton ψ).prod
      (hrank (φ.comp (Polynomial.X - Polynomial.C (m : ℚ))) ψ)).subset ?_
  rintro ⟨ψ, k⟩ ⟨T, a, t, hfine⟩
  exact Set.mem_iUnion₂.mpr ⟨ψ, ⟨T.hom t, (baseCondition_holds_iff_base ψ T a t).mp hfine.2.1⟩,
    Set.mk_mem_prod (Set.mem_singleton ψ)
      ⟨T, a + twistClass i m T, t,
        (fineCondition_zero_holds_add_twistClass_iff φ ψ m (k + 1) T a t).mpr hfine⟩⟩

/-- **`Pic^φ_m` is H-quasi-projective** (Kleiman, arXiv:math/0504020v1, Thm 4.8 (2) and its
proof, p. 29: "it suffices to represent each `P^φ_m` by a quasi-projective `S`-scheme"): over a
Noetherian `A`, under `FiniteFineStrataRanks`, the open `picardLevelOpens h φ m` is the finite
disjoint union of the nonempty chart images of the `(φ, ψ, m, k)`, each isomorphic to an
H-quasi-projective chart. -/
theorem isHQuasiProjective_picardLevelOpens_of_finiteFineStrataRanks [IsNoetherianRing A]
    (hrank : FiniteFineStrataRanks i N e) (φ : Polynomial ℚ) (m : ℤ) :
    IsHQuasiProjective ((picardLevelOpens h φ m).ι ≫ (picardScheme h).obj.hom) := by
  have hJ := finite_setOf_fineCondition_holds_of_finiteFineStrataRanks hrank φ m
  have : Finite {x : Polynomial ℚ × ℕ | ∃ (T : Over (Spec (.of A)))
      (a : (familyPicardFunctor (i ≫ toSpec A ι)).obj (op T)) (t : T.left),
        (fineCondition i N e φ x.1 m (x.2 + 1)).Holds T a t} := hJ.to_subtype
  refine IsHQuasiProjective.of_iSup_eq_top_of_pairwise_disjoint
    (fun x : {x : Polynomial ℚ × ℕ | ∃ (T : Over (Spec (.of A)))
      (a : (familyPicardFunctor (i ≫ toSpec A ι)).obj (op T)) (t : T.left),
        (fineCondition i N e φ x.1 m (x.2 + 1)).Holds T a t} =>
      (picardLevelOpens h φ m).ι ⁻¹ᵁ
        (fineCondition i N e φ x.1.1 m (x.1.2 + 1)).opens (picardUniversalSection h)) ?_ ?_ _ ?_
  · rw [eq_top_iff]
    intro w _
    have hwW : (picardLevelOpens h φ m).ι w ∈ ⨆ x : Polynomial ℚ × ℕ,
        (fineCondition i N e φ x.1 m (x.2 + 1)).opens (picardUniversalSection h) := by
      rw [iSup_opens_fineCondition_eq_coarseCondition]
      have hmem : (picardLevelOpens h φ m).ι w ∈ Set.range (picardLevelOpens h φ m).ι := ⟨w, rfl⟩
      rw [Scheme.Opens.range_ι] at hmem
      exact hmem
    obtain ⟨x, hx⟩ := TopologicalSpace.Opens.mem_iSup.mp hwW
    obtain ⟨V, g, v, a, -, -, hC⟩ := (FiberCondition.mem_opens_iff _ _ _).mp hx
    exact TopologicalSpace.Opens.mem_iSup.mpr ⟨⟨x, V, a, v, hC⟩, hx⟩
  · intro x y hxy
    change Disjoint ((picardLevelOpens h φ m).ι ⁻¹ᵁ _) ((picardLevelOpens h φ m).ι ⁻¹ᵁ _)
    rw [disjoint_iff, ← Scheme.Hom.preimage_inf,
      disjoint_iff.mp (disjoint_fineCondition_opens h φ m fun heq => hxy (Subtype.ext heq)),
      Scheme.Hom.preimage_bot]
  · intro x
    change IsHQuasiProjective (((picardLevelOpens h φ m).ι ⁻¹ᵁ
      (fineCondition i N e φ x.1.1 m (x.1.2 + 1)).opens (picardUniversalSection h)).ι ≫
        (picardLevelOpens h φ m).ι ≫ (picardScheme h).obj.hom)
    have hr : Set.range (((picardLevelOpens h φ m).ι ⁻¹ᵁ
        (fineCondition i N e φ x.1.1 m (x.1.2 + 1)).opens (picardUniversalSection h)).ι ≫
          (picardLevelOpens h φ m).ι) =
        Set.range ((picardSubfunctorCover h).ιp (ULift.up (φ, x.1.1, m, x.1.2))).hom.left := by
      rw [range_picardChart_mk, Scheme.Opens.range_ι_comp_ι_of_le
        (fineCondition_opens_le_picardLevelOpens h φ x.1.1 m x.1.2)]
    rw [← Category.assoc, ← IsOpenImmersion.isoOfRangeEq_hom_fac _ _ hr, Category.assoc]
    infer_instance

end AlgebraicGeometry.Scheme.RelativePicard
