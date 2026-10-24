/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Aglib.AlgebraicGeometry.HilbertScheme.Quotient.Effective

/-!
# Quotients by flat proper equivalence relations from a Hilbert datum

The declarations below restate the core of Nitsure's Theorem 6.8 (arXiv:math/0504590v1,
pp. 33–35) against an abstract Hilbert datum: the two equivalences of `(***)`, the graph
`Γ_φ ⊂ D` with `p₁⁻¹ Γ_φ = p₂⁻¹ Γ_φ`, the cartesian descent square, effectivity, and the packaged
`FlatProperQuotient` for a relation `(p₁, p₂)` over a Noetherian ring with H-quasi-projective `Z`
and `H`, and guard their axioms.
-/

@[expose] public section

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u

namespace AglibTest.QuotientHilbertDatum

variable {S Z R : Scheme.{u}} {πZ : Z ⟶ S} {j : R ⟶ pullback πZ πZ}

/-- The first equivalence of `(***)`, for every test scheme: `(x, y) ∈ R(T)` if and only if
`(x, φ ∘ y)` is a point of `D`. -/
theorem exists_lift_iff (𝔥 : QuotientHilbertDatum πZ j) [IsClosedImmersion j] {T : Scheme.{u}}
    (x y : T ⟶ Z) (h : x ≫ πZ = (y ≫ 𝔥.φ) ≫ 𝔥.πH) :
    (∃ d : T ⟶ 𝔥.D.subscheme, d ≫ 𝔥.D.subschemeι = pullback.lift x (y ≫ 𝔥.φ) h) ↔
      pointsRelation (j ≫ pullback.fst πZ πZ) (j ≫ pullback.snd πZ πZ) T x y :=
  𝔥.exists_lift_subschemeι_iff_pointsRelation x y h

/-- Nitsure's form of the first equivalence: `(x, y) ∈ R(T)` if and only if `(x, 𝟙_T)` factors
through `φ(y) ⊆ Z ×_S T`; and `y^* R = φ(y)`. -/
theorem nitsure_first_equivalence (𝔥 : QuotientHilbertDatum πZ j) [IsClosedImmersion j]
    {T : Scheme.{u}} (g : T ⟶ S) (x y : T ⟶ Z) (hx : x ≫ πZ = 𝟙 T ≫ g) (hy : y ≫ πZ = g) :
    (pointsRelation (j ≫ pullback.fst πZ πZ) (j ≫ pullback.snd πZ πZ) T x y ↔
      ∃ a : T ⟶ (𝔥.D.comap (pullback.map πZ g πZ 𝔥.πH (𝟙 Z) (y ≫ 𝔥.φ) (𝟙 S) (by simp)
          (by simp [𝔥.w, hy]))).subscheme,
        a ≫ (𝔥.D.comap (pullback.map πZ g πZ 𝔥.πH (𝟙 Z) (y ≫ 𝔥.φ) (𝟙 S) (by simp)
          (by simp [𝔥.w, hy]))).subschemeι = pullback.lift x (𝟙 T) hx) ∧
      j.ker.comap (pullback.map πZ g πZ πZ (𝟙 Z) y (𝟙 S) (by simp) (by simp [hy])) =
        𝔥.D.comap (pullback.map πZ g πZ 𝔥.πH (𝟙 Z) (y ≫ 𝔥.φ) (𝟙 S) (by simp)
          (by simp [𝔥.w, hy])) :=
  ⟨𝔥.pointsRelation_iff_exists_lift_comap g x y hx _ _, 𝔥.ker_comap_eq_comap g y _ _ _⟩

/-- `(***)` on locally Noetherian points: `(x, y) ∈ R(T)` if and only if `φ(x) = φ(y)`. -/
theorem pointsRelation_iff (𝔥 : QuotientHilbertDatum πZ j) [IsClosedImmersion j]
    [LocallyOfFiniteType πZ]
    (hequiv : ∀ (T : Scheme.{u}) [IsLocallyNoetherian T],
      _root_.Equivalence (pointsRelation (j ≫ pullback.fst πZ πZ) (j ≫ pullback.snd πZ πZ) T))
    {T : Scheme.{u}} [IsLocallyNoetherian T] (x y : T ⟶ Z) :
    pointsRelation (j ≫ pullback.fst πZ πZ) (j ≫ pullback.snd πZ πZ) T x y ↔
      x ≫ 𝔥.φ = y ≫ 𝔥.φ :=
  𝔥.pointsRelation_iff_comp_eq hequiv x y

/-- The graph of `φ` factors through `D` as a closed immersion `Γ` mapping to `φ` in `H`, and the
two pullbacks of `Γ_φ` to `D ×_H D` agree. -/
theorem exists_graph (𝔥 : QuotientHilbertDatum πZ j) [IsClosedImmersion j]
    [IsLocallyNoetherian Z] [LocallyOfFiniteType πZ] [IsSeparated 𝔥.πH] [IsLocallyNoetherian 𝔥.H]
    (hequiv : ∀ (T : Scheme.{u}) [IsLocallyNoetherian T],
      _root_.Equivalence (pointsRelation (j ≫ pullback.fst πZ πZ) (j ≫ pullback.snd πZ πZ) T)) :
    ∃ Γ : Z ⟶ 𝔥.D.subscheme, Γ ≫ 𝔥.D.subschemeι = 𝔥.graph ∧ IsClosedImmersion Γ ∧
      Γ ≫ 𝔥.familyProj = 𝔥.φ ∧
      Γ.ker.comap (pullback.fst 𝔥.familyProj 𝔥.familyProj) =
        Γ.ker.comap (pullback.snd 𝔥.familyProj 𝔥.familyProj) := by
  obtain ⟨Γ, hΓ⟩ := 𝔥.exists_comp_subschemeι_eq_graph ((hequiv Z).refl (𝟙 Z))
  exact ⟨Γ, hΓ, QuotientHilbertDatum.isClosedImmersion_of_comp_subschemeι_eq_graph hΓ,
    QuotientHilbertDatum.comp_familyProj_of_comp_subschemeι_eq_graph hΓ,
    QuotientHilbertDatum.ker_comap_fst_eq_ker_comap_snd_of_comp_subschemeι_eq_graph hΓ hequiv⟩

/-- The quotient morphism `q = φ.toImage` is flat, surjective and proper, and `R` is its kernel
pair. -/
theorem toImage_properties (𝔥 : QuotientHilbertDatum πZ j) [IsClosedImmersion j]
    [IsLocallyNoetherian Z] [LocallyOfFiniteType πZ] [IsSeparated 𝔥.πH] [IsLocallyNoetherian 𝔥.H]
    (hequiv : ∀ (T : Scheme.{u}) [IsLocallyNoetherian T],
      _root_.Equivalence (pointsRelation (j ≫ pullback.fst πZ πZ) (j ≫ pullback.snd πZ πZ) T)) :
    Flat 𝔥.φ.toImage ∧ Surjective 𝔥.φ.toImage ∧ IsProper 𝔥.φ.toImage ∧
      IsPullback (j ≫ pullback.fst πZ πZ) (j ≫ pullback.snd πZ πZ) 𝔥.φ.toImage 𝔥.φ.toImage :=
  ⟨𝔥.flat_toImage hequiv, 𝔥.surjective_toImage hequiv, 𝔥.isProper_toImage hequiv,
    𝔥.isPullback_toImage hequiv⟩

/-- **The shape used for a schematic equivalence relation `(p₁, p₂)`**: over a Noetherian ring,
with `Z` and `H` H-quasi-projective and `j = (p₁, p₂)` a closed immersion, the quotient exists; its
quotient morphism is an effective epimorphism and an fppf covering, and the quotient is locally
Noetherian and separated over `Spec A`. -/
theorem exists_flatProperQuotient {A : Type u} [CommRing A] [IsNoetherianRing A] {Z R : Scheme.{u}}
    {πZ : Z ⟶ Spec (.of A)} [IsHQuasiProjective πZ] (p₁ p₂ : R ⟶ Z) (hp : p₁ ≫ πZ = p₂ ≫ πZ)
    [IsClosedImmersion (pullback.lift p₁ p₂ hp)]
    (𝔥 : QuotientHilbertDatum πZ (pullback.lift p₁ p₂ hp)) [IsHQuasiProjective 𝔥.πH]
    (hequiv : ∀ (T : Scheme.{u}) [IsLocallyNoetherian T],
      _root_.Equivalence (pointsRelation p₁ p₂ T)) :
    ∃ 𝔮 : FlatProperQuotient πZ p₁ p₂, EffectiveEpi 𝔮.q ∧
      Presieve.singleton 𝔮.q ∈ Scheme.fppfPrecoverage 𝔮.Q ∧ IsLocallyNoetherian 𝔮.Q ∧
        IsSeparated 𝔮.πQ ∧ Nonempty (IsColimit (Cofork.ofπ 𝔮.q 𝔮.isPullback.w)) := by
  have := IsHQuasiProjective.isLocallyNoetherian πZ
  have := IsHQuasiProjective.isLocallyNoetherian 𝔥.πH
  obtain ⟨𝔮⟩ := 𝔥.nonempty_flatProperQuotient_of_comp_eq (pullback.lift_fst _ _ _)
    (pullback.lift_snd _ _ _) hequiv
  exact ⟨𝔮, 𝔮.effectiveEpi, 𝔮.singleton_mem_fppfPrecoverage, inferInstance, 𝔮.isSeparated,
    ⟨𝔮.isColimitCofork⟩⟩

/-- The packaged quotient of a datum is the scheme-theoretic image of `φ`, and `q ≫ ι_Q = φ`. -/
theorem flatProperQuotient_q {A : Type u} [CommRing A] {Z R : Scheme.{u}}
    {πZ : Z ⟶ Spec (.of A)} {j : R ⟶ pullback πZ πZ} (𝔥 : QuotientHilbertDatum πZ j)
    [IsClosedImmersion j] [IsLocallyNoetherian Z] [LocallyOfFiniteType πZ]
    [IsHQuasiProjective 𝔥.πH] [IsLocallyNoetherian 𝔥.H]
    (hequiv : ∀ (T : Scheme.{u}) [IsLocallyNoetherian T],
      _root_.Equivalence (pointsRelation (j ≫ pullback.fst πZ πZ) (j ≫ pullback.snd πZ πZ) T)) :
    (𝔥.flatProperQuotient hequiv).q = 𝔥.φ.toImage ∧
      (𝔥.flatProperQuotient hequiv).q ≫ 𝔥.φ.imageι = 𝔥.φ :=
  ⟨𝔥.flatProperQuotient_q hequiv, 𝔥.flatProperQuotient_q_imageι hequiv⟩

/-- info: 'AglibTest.QuotientHilbertDatum.exists_lift_iff' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms AglibTest.QuotientHilbertDatum.exists_lift_iff

/-- info: 'AglibTest.QuotientHilbertDatum.nitsure_first_equivalence' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms AglibTest.QuotientHilbertDatum.nitsure_first_equivalence

/-- info: 'AglibTest.QuotientHilbertDatum.pointsRelation_iff' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms AglibTest.QuotientHilbertDatum.pointsRelation_iff

/-- info: 'AglibTest.QuotientHilbertDatum.exists_graph' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms AglibTest.QuotientHilbertDatum.exists_graph

/-- info: 'AglibTest.QuotientHilbertDatum.toImage_properties' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms AglibTest.QuotientHilbertDatum.toImage_properties

/-- info: 'AglibTest.QuotientHilbertDatum.exists_flatProperQuotient' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms AglibTest.QuotientHilbertDatum.exists_flatProperQuotient

/-- info: 'AglibTest.QuotientHilbertDatum.flatProperQuotient_q' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms AglibTest.QuotientHilbertDatum.flatProperQuotient_q

end AglibTest.QuotientHilbertDatum
