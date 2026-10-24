/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Picard.Representability
public import Aglib.AlgebraicGeometry.Picard.Strata.Representability

/-!
# Representability of the fppf Picard functor, with the fine strata constructed

Let `A` be a Noetherian ring, `i : X ⟶ P^N_A = ProjectiveSpace A ι` a closed immersion with
`ι ≃ Fin (N + 1)`, such that `p = i ≫ toSpec A ι` is flat with geometrically integral fibres. This
file discharges the two premises of `exists_representableBy_fppfPicardSheaf_of_fineStrata`
([Representability](../Representability.lean)) by the construction of the fine strata in
`Aglib.AlgebraicGeometry.Picard.Strata.Representability`, and states Kleiman's Theorem 4.8
(*The Picard scheme*, arXiv:math/0504020v1, pp. 27–31, fppf form on locally Noetherian test
schemes) with no further hypothesis (`exists_representableBy_fppfPicardSheaf`).

* `Strata.fineStrataRepresentableByHQuasiProjective i e`: each fine stratum `Pic^{φ₀,ψ,k+1}_0` is
  represented by an H-quasi-projective scheme (`Strata.exists_fineCondition_representableBy`, with
  the representation of `Div^{ψ - φ₀}_X` by an H-quasi-projective Noetherian scheme `D` from
  `ProjectiveSpace.exists_locallyNoetherianRelativeDivisorFunctor_representableBy`; Kleiman,
  proof of Thm 4.8, p. 30, and Lemma 4.9).
* `Strata.finiteFineStrataRanks i e`: for fixed `(φ₀, ψ)` only finitely many ranks `k + 1` occur
  on the fine strata at level `0`. With one `D` for `θ = ψ - φ₀`, the opens
  `Z_k = Pic^{φ₀,ψ,k+1}_0 ×_P Div^θ_X` of `D` (`FiberCondition.abelPreimageOver`) are pairwise
  disjoint (`Strata.disjoint_opens_fineCondition`), and `D` is a Noetherian space, so only
  finitely many are nonempty; a point where the fine condition holds gives a point of the
  representing scheme `Q_k` (`FiberCondition.nonempty_of_holds_of_representableBy`, through the
  residue field), hence of `Z_k`, since `q : Z_k ⟶ Q_k` is surjective. This is the finiteness
  behind Kleiman's single quasi-projective representing scheme of `P^{φ₀}_0`, p. 30, where the
  rank is not fixed.
-/

@[expose] public section

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
open AlgebraicGeometry.ProjectiveSpace TopologicalSpace

namespace AlgebraicGeometry.Scheme.RelativePicard

namespace FiberCondition

variable {S X : Scheme.{u}} {p : X ⟶ S} (C : FiberCondition p)

/-- **A point where a fibre condition holds gives a point of a representing scheme of `Pic^C`**:
if `C` holds at `t ∈ T` for a class on `X ×_S T`, then every representing scheme of `Pic^C` on
locally Noetherian test schemes is nonempty. The restriction of the class to the residue field of
`t` satisfies `C` at the unique point of `Spec κ(t)` (`holds_iff_holds_residuePoint`), so its
section lies in `Pic^C(Spec κ(t))` (`app_mem_subfunctor_iff`), and `Spec κ(t)` is Noetherian. -/
theorem nonempty_of_holds_of_representableBy {Q : Scheme.LocallyNoetherianOver S}
    (rep : C.locallyNoetherianSubfunctor.toFunctor.RepresentableBy Q) {T : Over S}
    {a : (familyPicardFunctor p).obj (op T)} {t : T.left} (h : C.Holds T a t) :
    Nonempty Q.obj.left := by
  let T' : Scheme.LocallyNoetherianOver S :=
    ⟨Over.mk (T.left.fromSpecResidueField t ≫ T.hom),
      (inferInstance : IsLocallyNoetherian (Spec (T.left.residueField t)))⟩
  have hmem : (quotientProjection p ≫ toFppfPicardSheaf p).app (op T'.obj)
      ((familyPicardFunctor p).map (residuePoint T t).op a) ∈ C.subfunctor.obj (op T'.obj) :=
    (C.app_mem_subfunctor_iff _).mpr fun s => (C.holds_iff_holds_residuePoint a t s).mp h
  obtain ⟨s⟩ : Nonempty (PrimeSpectrum (T.left.residueField t)) := inferInstance
  exact ⟨((rep.homEquiv (X := T')).symm ⟨_, hmem⟩).hom.left s⟩

end FiberCondition

namespace Strata

variable {A : Type u} [CommRing A] [IsNoetherianRing A] {ι : Type u} {X : Scheme.{u}}
  (i : X ⟶ ProjectiveSpace A ι) [IsClosedImmersion i] [Flat (i ≫ toSpec A ι)]
  [GeometricallyIntegral (i ≫ toSpec A ι)] {N : ℕ} (e : ι ≃ Fin (N + 1))

/-- **The fine strata at level `0` are represented by H-quasi-projective schemes**
(Kleiman, arXiv:math/0504020v1, proof of Thm 4.8, p. 30, and Lemma 4.9, pp. 30–31, fppf form):
the premise `FineStrataRepresentableByHQuasiProjective` holds, by
`exists_fineCondition_representableBy` for the representation of `Div^{ψ - φ₀}_X` by an
H-quasi-projective scheme. -/
theorem fineStrataRepresentableByHQuasiProjective :
    FineStrataRepresentableByHQuasiProjective i N e := by
  intro φ₀ ψ k
  obtain ⟨D, hD, -, ⟨E⟩⟩ :=
    exists_locallyNoetherianRelativeDivisorFunctor_representableBy ι N e A i rfl (ψ - φ₀)
  obtain ⟨Q, -, -, rep, hQ, -⟩ := exists_fineCondition_representableBy (φ₀ := φ₀) (ψ := ψ) e k E
  exact ⟨Q, hQ, ⟨rep⟩⟩

/-- **Finitely many ranks on the fine strata at level `0`**: the premise `FiniteFineStrataRanks`
holds. For fixed `(φ₀, ψ)` the opens `Z_k` of the Noetherian representing scheme `D` of
`Div^{ψ - φ₀}_X` are pairwise disjoint, so only finitely many are nonempty, and a point where
`fineCondition φ₀ ψ 0 (k + 1)` holds gives a point of `Z_k` through the representing scheme `Q_k`
and the surjection `Z_k ⟶ Q_k` (Kleiman, arXiv:math/0504020v1, proof of Thm 4.8, p. 30). -/
theorem finiteFineStrataRanks : FiniteFineStrataRanks i N e := by
  intro φ₀ ψ
  obtain ⟨D, hD, hDn, ⟨E⟩⟩ :=
    exists_locallyNoetherianRelativeDivisorFunctor_representableBy ι N e A i rfl (ψ - φ₀)
  have hfin : {k : ℕ | ((fineCondition i N e φ₀ ψ 0 (k + 1)).opens
      (universalFppfAbelClass E) : Set D.obj.left).Nonempty}.Finite := by
    obtain ⟨F, hF⟩ := (NoetherianSpace.isCompact (⋃ k : ℕ, ((fineCondition i N e φ₀ ψ 0
      (k + 1)).opens (universalFppfAbelClass E) : Set D.obj.left))).elim_finite_subcover
      (fun k : ℕ => ((fineCondition i N e φ₀ ψ 0 (k + 1)).opens
        (universalFppfAbelClass E) : Set D.obj.left))
      (fun k => ((fineCondition i N e φ₀ ψ 0 (k + 1)).opens
        (universalFppfAbelClass E)).isOpen) subset_rfl
    refine F.finite_toSet.subset ?_
    rintro k ⟨x, hx⟩
    obtain ⟨k', hk', hxk'⟩ := Set.mem_iUnion₂.mp (hF (Set.mem_iUnion.mpr ⟨k, hx⟩))
    by_contra hk
    have hne : (φ₀, ψ, k' + 1) ≠ (φ₀, ψ, k + 1) := fun heq => hk (by
      simp only [Prod.mk.injEq, add_left_inj, true_and] at heq
      rw [← heq]
      exact hk')
    simpa using (disjoint_opens_fineCondition (i := i) (N := N) (e := e)
      (universalFppfAbelClass E) hne).le_bot ⟨hxk', hx⟩
  refine hfin.subset ?_
  rintro k ⟨T, a, t, hk⟩
  obtain ⟨Q, q, -, rep, -, -, hsurj, -⟩ :=
    exists_fineCondition_representableBy (φ₀ := φ₀) (ψ := ψ) e k E
  obtain ⟨y⟩ := (fineCondition i N e φ₀ ψ 0 (k + 1)).nonempty_of_holds_of_representableBy rep hk
  obtain ⟨z, -⟩ := hsurj.surj y
  have hz : ((fineCondition i N e φ₀ ψ 0 (k + 1)).abelPreimageι E).hom.left z ∈
      Set.range ((fineCondition i N e φ₀ ψ 0 (k + 1)).opens
        (universalFppfAbelClass E)).ι := ⟨z, rfl⟩
  rw [Scheme.Opens.range_ι] at hz
  exact ⟨_, hz⟩

end Strata

open Strata

variable {A : Type u} [CommRing A] [IsNoetherianRing A] {ι : Type u} {X : Scheme.{u}}
  (i : X ⟶ ProjectiveSpace A ι) [IsClosedImmersion i] [Flat (i ≫ toSpec A ι)]
  [GeometricallyIntegral (i ≫ toSpec A ι)] {N : ℕ} (e : ι ≃ Fin (N + 1))

/-- **Representability of `Pic_{X/S,(fppf)}`** (Kleiman, arXiv:math/0504020v1, Thm 4.8,
pp. 27–31, for a Noetherian affine base and the fppf topology, on locally Noetherian test schemes):
for a closed `X ⊆ P^N_A`, `A` Noetherian, flat over `A` with geometrically integral fibres, the fppf
Picard functor is represented by a locally Noetherian scheme over `Spec A` that is separated and
locally of finite type, with open and closed strata `Pic^φ` covering it, each the increasing union
of the H-quasi-projective opens `Pic^φ_m`, which are the loci of the subsheaves `Pic^φ` and
`Pic^φ_m`. This is `exists_representableBy_fppfPicardSheaf_of_fineStrata` with its premises
discharged by `fineStrataRepresentableByHQuasiProjective` and `finiteFineStrataRanks`. -/
theorem exists_representableBy_fppfPicardSheaf :
    ∃ (P : Scheme.LocallyNoetherianOver (Spec (.of A)))
      (R : ((Scheme.locallyNoetherianOverInclusion (Spec (.of A))).op ⋙
        (fppfPicardSheaf (i ≫ toSpec A ι)).obj ⋙
          CategoryTheory.forget AddCommGrpCat.{u + 1}).RepresentableBy P)
      (stratum : Polynomial ℚ → P.obj.left.Opens) (level : Polynomial ℚ → ℤ → P.obj.left.Opens),
      IsSeparated P.obj.hom ∧ LocallyOfFiniteType P.obj.hom ∧
        (∀ φ, IsClopen (stratum φ : Set P.obj.left)) ∧ Pairwise (Function.onFun Disjoint stratum) ∧
        ⨆ φ, stratum φ = ⊤ ∧ (∀ φ, Monotone (level φ)) ∧ (∀ φ, ⨆ m, level φ m = stratum φ) ∧
        (∀ φ m, IsHQuasiProjective ((level φ m).ι ≫ P.obj.hom)) ∧
        ∀ {T : Scheme.LocallyNoetherianOver (Spec (.of A))} (a : T ⟶ P) (φ : Polynomial ℚ),
          (R.homEquiv a ∈ (eulerCondition i N e φ).subfunctor.obj (op T.obj) ↔
            a.hom.left ⁻¹ᵁ stratum φ = ⊤) ∧
          ∀ m, (R.homEquiv a ∈ (coarseCondition i N e φ m).subfunctor.obj (op T.obj) ↔
            a.hom.left ⁻¹ᵁ level φ m = ⊤) :=
  exists_representableBy_fppfPicardSheaf_of_fineStrata
    (fineStrataRepresentableByHQuasiProjective i e) (finiteFineStrataRanks i e)

end AlgebraicGeometry.Scheme.RelativePicard
