/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Picard.Strata.Twist
public import Aglib.AlgebraicGeometry.Picard.ZariskiSheaf
public import Aglib.AlgebraicGeometry.ProjectiveSpace.QuasiProjective

/-!
# The Picard scheme glued from the fine strata

Let `A` be a commutative ring, `i : X ⟶ P^N_A = ProjectiveSpace A ι` a closed immersion with
`ι ≃ Fin (N + 1)`, such that `p = i ≫ toSpec A ι` is flat with geometrically integral fibres, and
let `F` be the underlying presheaf of sets of `Pic_{X/S,(fppf)}`, `S = Spec A`, restricted to
locally Noetherian test schemes. This file assembles the representing scheme of `F` from
representations of the fine strata, following the gluing step of Kleiman, *The Picard scheme*,
arXiv:math/0504020v1, proof of Thm 4.8, p. 29 ("by a general result [EGA G, (0, 4.5.4), p. 103],
if the `P^φ` are (representable by) schemes, then `P` is their disjoint union", and the same for
the `P^φ_m`), in the form of Stacks, Tag 01JJ (Lemma 26.15.4), relative to `S`.

The premise is `Strata.FineStrataRepresentableByHQuasiProjective i N e`: for all `φ₀, ψ ∈ ℚ[X]`
and `k ∈ ℕ`, the fine stratum `Pic^{φ₀,ψ,k+1}_0` (the subsheaf of `fineCondition φ₀ ψ 0 (k + 1)`)
is represented on locally Noetherian test schemes by an H-quasi-projective scheme over `Spec A`
(Kleiman p. 30, "it suffices to represent `P^{φ₀}_0` by a quasi-projective `S`-scheme", refined
by the base polynomial `ψ` and the rank `k + 1` of `H^0`). Under it:

* `picardSubfunctorCover h` is the cover of `F` by the open subfunctors of the fine conditions
  `fineCondition φ ψ m (k + 1)`, indexed by `⟨φ, ψ, m, k⟩ ∈ ULift (ℚ[X] × ℚ[X] × ℤ × ℕ)`, with the
  representing scheme of `Pic^{φ₀,ψ,k+1}_0`, `φ₀ = φ.comp (X - C m)`, transported along the twist
  `Pic^{φ,ψ,k+1}_m ≅ Pic^{φ₀,ψ,k+1}_0` (`Strata.fineRepresentableByOfTwist`); the fine strata
  cover `F` Zariski-locally (`Strata.iSup_opens_fineCondition_eq_top`, geometrically integral
  fibres);
* `picardScheme h` is the glued locally Noetherian scheme over `Spec A`, and
  `picardSchemeRepresentableBy h` represents `F` (`SubfunctorCover.representableByGlued`, with the
  Zariski sheaf property `isZariskiSheaf_fppfPicardSheaf_forget`);
* `picardUniversalSection h` is the universal section of `Pic_{X/S,(fppf)}` over `picardScheme h`
  (`picardSchemeRepresentableBy_homEquiv_id`), and `picardSchemeRepresentableBy_homEquiv`
  identifies the section of a morphism with the pullback of the universal section;
* the chart of `⟨φ, ψ, m, k⟩` is an open immersion with image the open of
  `fineCondition φ ψ m (k + 1)` of the universal section (`range_picardChart`), and its structure
  morphism is H-quasi-projective (`isHQuasiProjective_picardChart_comp`);
* `picardScheme h` is locally of finite type over `Spec A`, since its charts are
  (`locallyOfFiniteType_picardScheme`).

No Noetherian hypothesis on `A` is used here.
-/

@[expose] public section

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
open AlgebraicGeometry.ProjectiveSpace
open AlgebraicGeometry.Scheme.LocalRepresentability

namespace AlgebraicGeometry.Scheme.RelativePicard

variable {A : Type u} [CommRing A] {ι : Type u} {X : Scheme.{u}}
  (i : X ⟶ ProjectiveSpace A ι) [IsClosedImmersion i] [Flat (i ≫ toSpec A ι)]
  (N : ℕ) (e : ι ≃ Fin (N + 1))

namespace Strata

/-- **Representability of the fine strata at level `0` by H-quasi-projective schemes**: for all
`φ₀, ψ ∈ ℚ[X]` and `k ∈ ℕ`, the fine stratum `Pic^{φ₀,ψ,k+1}_0` (the subsheaf of
`fineCondition φ₀ ψ 0 (k + 1)`) is represented on locally Noetherian test schemes by a scheme
that is H-quasi-projective over `Spec A` (Kleiman, arXiv:math/0504020v1, proof of Thm 4.8,
p. 30: "it suffices to represent `P^{φ₀}_0` by a quasi-projective `S`-scheme"). -/
def FineStrataRepresentableByHQuasiProjective : Prop :=
  ∀ (φ₀ ψ : Polynomial ℚ) (k : ℕ), ∃ Q : Scheme.LocallyNoetherianOver (Spec (.of A)),
    IsHQuasiProjective Q.obj.hom ∧
      Nonempty ((fineCondition i N e φ₀ ψ 0
        (k + 1)).locallyNoetherianSubfunctor.toFunctor.RepresentableBy Q)

variable {i N e} (h : FineStrataRepresentableByHQuasiProjective i N e)

/-- The chosen representing scheme of `Pic^{φ₀,ψ,k+1}_0`. -/
def fineStratumScheme (φ₀ ψ : Polynomial ℚ) (k : ℕ) :
    Scheme.LocallyNoetherianOver (Spec (.of A)) :=
  (h φ₀ ψ k).choose

instance isHQuasiProjective_fineStratumScheme (φ₀ ψ : Polynomial ℚ) (k : ℕ) :
    IsHQuasiProjective (fineStratumScheme h φ₀ ψ k).obj.hom :=
  (h φ₀ ψ k).choose_spec.1

/-- The chosen representation of `Pic^{φ₀,ψ,k+1}_0` by `fineStratumScheme h φ₀ ψ k`. -/
def fineStratumRepresentableBy (φ₀ ψ : Polynomial ℚ) (k : ℕ) :
    (fineCondition i N e φ₀ ψ 0 (k + 1)).locallyNoetherianSubfunctor.toFunctor.RepresentableBy
      (fineStratumScheme h φ₀ ψ k) :=
  (h φ₀ ψ k).choose_spec.2.some

end Strata

open Strata

/-- The fine condition of the index `⟨φ, ψ, m, k⟩` of the Picard cover:
`fineCondition φ ψ m (k + 1)`, the condition of the stratum `Pic^{φ,ψ,k+1}_m`. -/
abbrev picardCoverCondition (x : ULift.{u} (Polynomial ℚ × Polynomial ℚ × ℤ × ℕ)) :
    FiberCondition (i ≫ toSpec A ι) :=
  fineCondition i N e x.down.1 x.down.2.1 x.down.2.2.1 (x.down.2.2.2 + 1)

variable {i N e} [GeometricallyIntegral (i ≫ toSpec A ι)]
  (h : FineStrataRepresentableByHQuasiProjective i N e)

/-- **The cover of `Pic_{X/S,(fppf)}` by the fine strata** on locally Noetherian test schemes: the
open subfunctors `Pic^{φ,ψ,k+1}_m` of `fineCondition φ ψ m (k + 1)`, indexed by
`⟨φ, ψ, m, k⟩`, each represented by the representing scheme of `Pic^{φ₀,ψ,k+1}_0`,
`φ₀ = φ.comp (X - C m)`, through the twist (Kleiman, arXiv:math/0504020v1, proof of Thm 4.8,
pp. 29–30). -/
abbrev picardSubfunctorCover :
    SubfunctorCover ((Scheme.locallyNoetherianOverInclusion (Spec (.of A))).op ⋙
      (fppfPicardSheaf (i ≫ toSpec A ι)).obj ⋙ CategoryTheory.forget AddCommGrpCat.{u + 1}) where
  I := ULift.{u} (Polynomial ℚ × Polynomial ℚ × ℤ × ℕ)
  sub x := (picardCoverCondition i N e x).locallyNoetherianSubfunctor
  isOpen x := (picardCoverCondition i N e x).isOpenSubfunctor
  X x := fineStratumScheme h (x.down.1.comp (Polynomial.X - Polynomial.C (x.down.2.2.1 : ℚ)))
    x.down.2.1 x.down.2.2.2
  representableBy x := fineRepresentableByOfTwist
    (fineStratumRepresentableBy h (x.down.1.comp (Polynomial.X - Polynomial.C (x.down.2.2.1 : ℚ)))
      x.down.2.1 x.down.2.2.2)
  covers := by
    intro T ξ t
    have : IsLocallyNoetherian
        ((Scheme.locallyNoetherianOverInclusion (Spec (.of A))).obj T).left := T.property
    have ht : t ∈ ⨆ y : Polynomial ℚ × Polynomial ℚ × ℤ × ℕ,
        (fineCondition i N e y.1 y.2.1 y.2.2.1 (y.2.2.2 + 1)).opens
          (ξ : (fppfPicardSheaf (i ≫ toSpec A ι)).obj.obj (op T.obj)) := by
      rw [iSup_opens_fineCondition_eq_top]
      trivial
    obtain ⟨y, hy⟩ := TopologicalSpace.Opens.mem_iSup.mp ht
    refine ⟨ULift.up y, restrictOpens T ((picardCoverCondition i N e (ULift.up y)).opens
        (ξ : (fppfPicardSheaf (i ≫ toSpec A ι)).obj.obj (op T.obj))),
      restrictOpensι T ((picardCoverCondition i N e (ULift.up y)).opens
        (ξ : (fppfPicardSheaf (i ≫ toSpec A ι)).obj.obj (op T.obj))), ?_,
      ((picardCoverCondition i N e (ULift.up y)).map_mem_subfunctor_iff ξ
        (restrictOpensι T _).hom).2 (Scheme.Opens.ι_preimage_self _)⟩
    change t ∈ Set.range (Scheme.Opens.ι _)
    rw [Scheme.Opens.range_ι]
    exact hy

/-- **The Picard scheme** (Kleiman, arXiv:math/0504020v1, Thm 4.8): the locally Noetherian scheme
over `Spec A` glued from the representing schemes of the fine strata. -/
abbrev picardScheme : Scheme.LocallyNoetherianOver (Spec (.of A)) :=
  (picardSubfunctorCover h).glued

/-- The Picard scheme is locally Noetherian. -/
instance isLocallyNoetherian_picardScheme : IsLocallyNoetherian (picardScheme h).obj.left :=
  (picardScheme h).property

/-- **The Picard scheme represents `Pic_{X/S,(fppf)}` on locally Noetherian test schemes**
(Kleiman, arXiv:math/0504020v1, Thm 4.8 (1), with fppf in place of étale; Stacks, Tag 01JJ). -/
def picardSchemeRepresentableBy :
    ((Scheme.locallyNoetherianOverInclusion (Spec (.of A))).op ⋙
      (fppfPicardSheaf (i ≫ toSpec A ι)).obj ⋙
        CategoryTheory.forget AddCommGrpCat.{u + 1}).RepresentableBy (picardScheme h) :=
  (picardSubfunctorCover h).representableByGlued (isZariskiSheaf_fppfPicardSheaf_forget _)

/-- The universal section of `Pic_{X/S,(fppf)}` over the Picard scheme, glued from the universal
sections of the charts. -/
def picardUniversalSection :
    (fppfPicardSheaf (i ≫ toSpec A ι)).obj.obj (op (picardScheme h).obj) :=
  (picardSubfunctorCover h).univ (isZariskiSheaf_fppfPicardSheaf_forget _)

/-- The section of `Pic_{X/S,(fppf)}` attached to a morphism to the Picard scheme is the pullback
of the universal section. -/
theorem picardSchemeRepresentableBy_homEquiv {T : Scheme.LocallyNoetherianOver (Spec (.of A))}
    (a : T ⟶ picardScheme h) :
    (picardSchemeRepresentableBy h).homEquiv a =
      (fppfPicardSheaf (i ≫ toSpec A ι)).obj.map a.hom.op (picardUniversalSection h) :=
  rfl

/-- The universal section is the section attached to the identity of the Picard scheme. -/
theorem picardSchemeRepresentableBy_homEquiv_id :
    (picardSchemeRepresentableBy h).homEquiv (𝟙 _) = picardUniversalSection h := by
  rw [picardSchemeRepresentableBy_homEquiv]
  change ((Scheme.locallyNoetherianOverInclusion (Spec (.of A))).op ⋙
      (fppfPicardSheaf (i ≫ toSpec A ι)).obj ⋙
        CategoryTheory.forget AddCommGrpCat.{u + 1}).map (𝟙 (picardScheme h)).op _ = _
  rw [op_id, Functor.map_id_apply]

/-- **The charts as open subfunctors**: a morphism to the Picard scheme pulls the universal section
back into `Pic^{φ,ψ,k+1}_m` if and only if it lands in the chart of `⟨φ, ψ, m, k⟩`. -/
theorem map_picardUniversalSection_mem_iff (x : ULift.{u} (Polynomial ℚ × Polynomial ℚ × ℤ × ℕ))
    {Z : Scheme.LocallyNoetherianOver (Spec (.of A))} (g : Z ⟶ picardScheme h) :
    (fppfPicardSheaf (i ≫ toSpec A ι)).obj.map g.hom.op (picardUniversalSection h) ∈
        (picardCoverCondition i N e x).subfunctor.obj (op Z.obj) ↔
      Set.range g.hom.left ⊆ Set.range ((picardSubfunctorCover h).ιp x).hom.left :=
  (picardSubfunctorCover h).map_univ_mem_iff (isZariskiSheaf_fppfPicardSheaf_forget _) x g

/-- **The charts of the Picard scheme**: the chart of `⟨φ, ψ, m, k⟩` is an open immersion whose
image is the open of `fineCondition φ ψ m (k + 1)` of the universal section, the locus where the
universal section lies in `Pic^{φ,ψ,k+1}_m`. -/
theorem range_picardChart (x : ULift.{u} (Polynomial ℚ × Polynomial ℚ × ℤ × ℕ)) :
    Set.range ((picardSubfunctorCover h).ιp x).hom.left =
      SetLike.coe ((picardCoverCondition i N e x).opens (picardUniversalSection h)) := by
  apply subset_antisymm
  · have htop := ((picardCoverCondition i N e x).map_mem_subfunctor_iff
      (picardUniversalSection h) ((picardSubfunctorCover h).ιp x).hom).1
      ((map_picardUniversalSection_mem_iff h x ((picardSubfunctorCover h).ιp x)).2 subset_rfl)
    rintro _ ⟨q, rfl⟩
    have hq : q ∈ ((picardSubfunctorCover h).ιp x).hom.left ⁻¹ᵁ
        (picardCoverCondition i N e x).opens (picardUniversalSection h) := by
      rw [htop]
      trivial
    exact hq
  · intro y hy
    have hmem := ((picardCoverCondition i N e x).map_mem_subfunctor_iff
      (picardUniversalSection h) (restrictOpensι (picardScheme h)
        ((picardCoverCondition i N e x).opens (picardUniversalSection h))).hom).2
      (Scheme.Opens.ι_preimage_self _)
    exact (map_picardUniversalSection_mem_iff h x (restrictOpensι (picardScheme h)
      ((picardCoverCondition i N e x).opens (picardUniversalSection h)))).1 hmem ⟨⟨y, hy⟩, rfl⟩

/-- The structure morphism of the chart of `⟨φ, ψ, m, k⟩` is that of the representing scheme of
`Pic^{φ₀,ψ,k+1}_0`. -/
theorem picardChart_comp_hom (x : ULift.{u} (Polynomial ℚ × Polynomial ℚ × ℤ × ℕ)) :
    ((picardSubfunctorCover h).ιp x).hom.left ≫ (picardScheme h).obj.hom =
      ((picardSubfunctorCover h).X x).obj.hom :=
  Over.w ((picardSubfunctorCover h).ιp x).hom

/-- The charts of the Picard scheme are H-quasi-projective over `Spec A`. -/
instance isHQuasiProjective_picardChart_comp
    (x : ULift.{u} (Polynomial ℚ × Polynomial ℚ × ℤ × ℕ)) :
    IsHQuasiProjective (((picardSubfunctorCover h).ιp x).hom.left ≫ (picardScheme h).obj.hom) := by
  rw [picardChart_comp_hom]
  exact isHQuasiProjective_fineStratumScheme h
    (x.down.1.comp (Polynomial.X - Polynomial.C (x.down.2.2.1 : ℚ))) x.down.2.1 x.down.2.2.2

-- Instance search for `IsZariskiLocalAtSource @LocallyOfFiniteType` (through `HasRingHomProperty`)
-- fails at instance transparency under the default `respectTransparency` setting.
set_option backward.isDefEq.respectTransparency false in
/-- **The Picard scheme is locally of finite type over `Spec A`** (Kleiman, arXiv:math/0504020v1,
Thm 4.8 (1)): it is covered by the charts, which are H-quasi-projective, hence locally of finite
type. -/
instance locallyOfFiniteType_picardScheme : LocallyOfFiniteType (picardScheme h).obj.hom :=
  IsZariskiLocalAtSource.of_openCover (picardSubfunctorCover h).schemeGlueData.openCover
    fun x => by
      change LocallyOfFiniteType (((picardSubfunctorCover h).ιp x).hom.left ≫
        (picardScheme h).obj.hom)
      infer_instance

end AlgebraicGeometry.Scheme.RelativePicard
