/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.HilbertScheme.Coproduct.QuasiProjective
public import Aglib.AlgebraicGeometry.HilbertScheme.Quotient.Effective
public import Aglib.AlgebraicGeometry.ProjectiveSpace.QuasiProjective.EquivFin

/-!
# Existence of quotients by flat proper equivalence relations

Let `A` be a Noetherian ring, `πZ : Z ⟶ Spec A` H-quasi-projective (`IsHQuasiProjective`: a
quasi-compact immersion into some `P(ι)_A` over `Spec A`, `ι` finite; over a Noetherian ring, any
immersion) and `p₁, p₂ : R ⟶ Z` with `p₁ ≫ πZ = p₂ ≫ πZ`, such that `p₂` is proper and flat and, for
every locally Noetherian scheme `T`, the map `R(T) ⟶ Z(T) × Z(T)` is injective and its image is an
equivalence relation on `Z(T)`. Then `Z` has a **flat proper quotient** by `(p₁, p₂)`
(`AlgebraicGeometry.nonempty_flatProperQuotient`): an H-quasi-projective `πQ : Q ⟶ Spec A` and a
flat, surjective and proper `q : Z ⟶ Q` over `Spec A` with `R = Z ×_Q Z` through `(p₁, p₂)` (the
structure `FlatProperQuotient`, `Aglib.AlgebraicGeometry.HilbertScheme.Quotient.FlatProper`). Its
consequences are proved there: `q` is quasi-compact and locally of finite presentation, an effective
epimorphism, a coequalizer of `p₁, p₂`, and `{q}` is an fppf covering; `Q` is locally Noetherian,
and `πQ` is separated and locally of finite type. If instead `p₁` is proper and flat, the same holds
(`nonempty_flatProperQuotient_of_isProper_fst_of_flat_fst`, through `FlatProperQuotient.flip`).

Source: Nitsure, *Construction of Hilbert and Quot schemes*, arXiv:math/0504590v1, Theorem 6.9
(p. 36), by the proof of Theorem 6.8 (pp. 33–35), over the affine base `S = Spec A`. Differences
from the source:

* The relation is tested on locally Noetherian points: Nitsure's schematic equivalence relation
  (p. 31) asks for injectivity and an equivalence relation on `T`-points for every `S`-scheme `T`.
  The Hilbert functors are defined on the category `Sch_S` of locally Noetherian `S`-schemes
  (§1, pp. 3–4), and every scheme tested in the proof is locally Noetherian.
* Only `p₂` is assumed proper and flat; Nitsure assumes both projections are, but the proof
  (p. 33) uses only `f₂`, through which `R` is a family over `X`.
* Quasi-projectivity is `IsHQuasiProjective`, a quasi-compact immersion (over a Noetherian ring, any
  immersion) into projective space over `Spec A` (Stacks, Definition 29.41.1, Tag 01VW):
  quasi-projectivity "in the strongest sense" (p. 23), that is, the strong quasi-projectivity of
  Theorem 6.9 (a locally closed embedding into `P(E)`, p. 23) for a trivial vector bundle `E`. The
  quotient `Q` is quasi-projective in this sense; `q` is proved proper, where Theorem 6.9 states
  "strongly projective".

Proof (Nitsure, p. 33).

1. `j = (p₁, p₂) : R ⟶ Z ×_A Z` is proper, since `j ≫ pr₂ = p₂` is proper and `pr₂` is separated,
   and injective on locally Noetherian points, so it is a closed immersion
   (`isClosedImmersion_pullback_lift_of_isProper_snd_of_locallyNoetherian_injective`;
   the Exercise on p. 33,
   `Scheme.isClosedImmersion_of_isProper_of_locallyNoetherian_yoneda_map_injective`).
2. The closed subscheme `R ⊆ Z ×_A Z` is proper and flat over the second factor `Z`, as `p₂` is,
   and surjective: reflexivity of the relation at `T = Z` gives a section `Z ⟶ R` of `p₂` ("each
   fiber of `f₂ : R → X` is also non-empty as the diagonal `Δ_X` is contained in `R`").
3. `Z` has an immersion into `P(ι)_A` with `ι ≃ Fin (n + 1)`, as the Hilbert schemes of an
   immersed scheme require, also for `Z` empty (`IsHQuasiProjective.exists_isImmersion_equivFin`,
   `Aglib.AlgebraicGeometry.ProjectiveSpace.QuasiProjective.EquivFin`).
4. The fibre Hilbert polynomials of `R` over `Z` form a finite set `F` ("as the parameter scheme
   `X` is noetherian and as the Hilbert polynomial is locally constant, only finitely many
   polynomials `Φ` occur"), and `0 ∉ F` since `R ⟶ Z` is surjective ("therefore the Hilbert
   polynomial of each fiber is non-zero").
5. The finite union `H_F = ∐_{Φ ∈ F} Hilb^Φ_Z` with its universal family `D_F`
   (`Aglib.AlgebraicGeometry.HilbertScheme.Coproduct.Representability`) is H-quasi-projective
   (`Aglib.AlgebraicGeometry.HilbertScheme.Coproduct.QuasiProjective`), `D_F ⟶ H_F` is flat,
   proper and surjective ("Hence `p : D → H` is surjective"), and the classifying morphism
   `φ : Z ⟶ H_F` of `R` satisfies `φ^* D_F = R`. This is a Hilbert datum
   (`QuotientHilbertDatum.exists_isHQuasiProjective`), to which the core of the proof applies
   (`QuotientHilbertDatum.nonempty_flatProperQuotient_of_comp_eq`,
   `Aglib.AlgebraicGeometry.HilbertScheme.Quotient.Effective`).
-/

@[expose] public section

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits
open scoped Polynomial

namespace CategoryTheory

variable {C : Type*} [Category C] {R X : C}

/-- **Swapping the two morphisms of a relation swaps the related points**: `a, b : T ⟶ X` are
related by `(p₂, p₁)` if and only if `b, a` are related by `(p₁, p₂)`. -/
theorem pointsRelation_swap_iff (p₁ p₂ : R ⟶ X) (T : C) (a b : T ⟶ X) :
    pointsRelation p₂ p₁ T a b ↔ pointsRelation p₁ p₂ T b a :=
  ⟨fun ⟨r, h₂, h₁⟩ => ⟨r, h₁, h₂⟩, fun ⟨r, h₁, h₂⟩ => ⟨r, h₂, h₁⟩⟩

/-- **Swapping the two morphisms of a relation preserves equivalence relations on points.** -/
theorem equivalence_pointsRelation_swap {p₁ p₂ : R ⟶ X} {T : C}
    (h : _root_.Equivalence (pointsRelation p₁ p₂ T)) :
    _root_.Equivalence (pointsRelation p₂ p₁ T) where
  refl a := (pointsRelation_swap_iff p₁ p₂ T a a).mpr (h.refl a)
  symm hab := (pointsRelation_swap_iff p₁ p₂ T _ _).mpr
    (h.symm ((pointsRelation_swap_iff p₁ p₂ T _ _).mp hab))
  trans hab hbc := (pointsRelation_swap_iff p₁ p₂ T _ _).mpr
    (h.trans ((pointsRelation_swap_iff p₁ p₂ T _ _).mp hbc)
      ((pointsRelation_swap_iff p₁ p₂ T _ _).mp hab))

end CategoryTheory

namespace AlgebraicGeometry

/-- **A relation proper over its second factor and injective on locally Noetherian points is a
closed subscheme** (Nitsure, arXiv:math/0504590v1, proof of Thm 6.8, p. 33, with the Exercise
there): for a separated `πZ : Z ⟶ S` with `Z ×_S Z` locally Noetherian and `p₁, p₂ : R ⟶ Z` over
`S` with `p₂` proper, if `(p₁, p₂) : R(T) ⟶ Z(T) × Z(T)` is injective for every locally Noetherian
`T`, then `(p₁, p₂) : R ⟶ Z ×_S Z` is a closed immersion. It is proper, as
`(p₁, p₂) ≫ pr₂ = p₂` is proper and `pr₂` is separated
(`Scheme.isClosedImmersion_of_isProper_of_locallyNoetherian_yoneda_map_injective`). -/
theorem isClosedImmersion_pullback_lift_of_isProper_snd_of_locallyNoetherian_injective
    {S Z R : Scheme.{u}} (πZ : Z ⟶ S) [IsSeparated πZ] [IsLocallyNoetherian (pullback πZ πZ)]
    (p₁ p₂ : R ⟶ Z)
    (hp : p₁ ≫ πZ = p₂ ≫ πZ) [IsProper p₂]
    (hinj : ∀ (T : Scheme.{u}) [IsLocallyNoetherian T] (r r' : T ⟶ R),
      r ≫ p₁ = r' ≫ p₁ → r ≫ p₂ = r' ≫ p₂ → r = r') :
    IsClosedImmersion (pullback.lift p₁ p₂ hp) := by
  have : IsProper (pullback.lift p₁ p₂ hp ≫ pullback.snd πZ πZ) := by
    rw [pullback.lift_snd]
    infer_instance
  have : IsProper (pullback.lift p₁ p₂ hp) := IsProper.of_comp _ (pullback.snd πZ πZ)
  refine Scheme.isClosedImmersion_of_isProper_of_locallyNoetherian_yoneda_map_injective _
    fun T _ r r' h => hinj T r r' ?_ ?_
  · simpa only [Category.assoc, pullback.lift_fst] using congrArg (· ≫ pullback.fst πZ πZ) h
  · simpa only [Category.assoc, pullback.lift_snd] using congrArg (· ≫ pullback.snd πZ πZ) h

/-- **The Hilbert datum of a flat proper relation** (Nitsure, arXiv:math/0504590v1, proof of
Thm 6.8, p. 33): over a Noetherian ring `A`, let `πZ : Z ⟶ Spec A` be H-quasi-projective and
`j : R ⟶ Z ×_A Z` a closed immersion whose second projection `j ≫ pr₂` is proper, flat and
surjective. Then there is a Hilbert datum `(H, D, φ)` for `j` with `H` H-quasi-projective over
`Spec A`: for an immersion `Z ⟶ P^n_A` and the finite set `F` of fibre Hilbert polynomials of `R`
over `Z`, which omits `0`, `H = ∐_{Φ ∈ F} Hilb^Φ_Z` with its universal family, and `φ : Z ⟶ H` the
classifying morphism of `R`, regarded as a family over `Z` through `pr₂`. -/
theorem QuotientHilbertDatum.exists_isHQuasiProjective {A : Type u} [CommRing A]
    [IsNoetherianRing A] {Z R : Scheme.{u}} (πZ : Z ⟶ Spec (CommRingCat.of A))
    [IsHQuasiProjective πZ] (j : R ⟶ pullback πZ πZ) [IsClosedImmersion j]
    [IsProper (j ≫ pullback.snd πZ πZ)] [Flat (j ≫ pullback.snd πZ πZ)]
    [Surjective (j ≫ pullback.snd πZ πZ)] :
    ∃ 𝔥 : QuotientHilbertDatum πZ j, IsHQuasiProjective 𝔥.πH := by
  have := IsHQuasiProjective.isNoetherian πZ
  obtain ⟨ι, n, e, i, _, -, hi⟩ : ∃ (ι : Type u) (n : ℕ) (_ : ι ≃ Fin (n + 1))
      (i : Z ⟶ ProjectiveSpace A ι), IsImmersion i ∧ QuasiCompact i ∧
        i ≫ ProjectiveSpace.toSpec A ι = πZ :=
    IsHQuasiProjective.exists_isImmersion_equivFin πZ
  have : Finite ι := Finite.of_equiv _ e.symm
  -- `R ⊆ Z ×_A Z` over the second factor is `p₂ = j ≫ pr₂` up to the isomorphism `R ≅ j.image`.
  have hV : j.ker.subschemeι ≫ pullback.snd πZ πZ = inv j.toImage ≫ j ≫ pullback.snd πZ πZ := by
    rw [IsIso.eq_inv_comp]
    exact Scheme.Hom.toImage_imageι_assoc j _
  have hpV : IsProper (j.ker.subschemeι ≫ pullback.snd πZ πZ) := by
    rw [hV]
    infer_instance
  have hfV : Flat (j.ker.subschemeι ≫ pullback.snd πZ πZ) := by
    rw [hV]
    infer_instance
  have hsV : Surjective (j.ker.subschemeι ≫ pullback.snd πZ πZ) := by
    rw [hV]
    infer_instance
  -- The fibre Hilbert polynomials of `R` over `Z` that occur: finitely many, none zero.
  have hR := ProjectiveSpace.isImmersedHilbertFamilyIn_range_fiberHilbertPolynomialAt i hi πZ
    j.ker hpV hfV
  have := hR.isClosedImmersion
  obtain ⟨F, hR, hF, h0⟩ : ∃ F : Set ℚ[X], ProjectiveSpace.IsImmersedHilbertFamilyIn i hi F πZ
      j.ker ∧ F.Finite ∧ (0 : ℚ[X]) ∉ F :=
    ⟨_, hR, ProjectiveSpace.finite_range_fiberHilbertPolynomialAt_map_immersionBaseChange i hi πZ
        j.ker n e,
      (ProjectiveSpace.zero_notMem_range_fiberHilbertPolynomialAt_map_immersionBaseChange_iff i hi
        πZ j.ker n e).mpr hsV⟩
  have : Finite F := hF.to_subtype
  -- The finite union `H_F` of Hilbert schemes and the classifying morphism of `R`.
  obtain ⟨r, hr, J, s, hC, -⟩ :=
    ProjectiveSpace.exists_sigmaImmersedHilbertScheme_representableBy ι n e A i hi F
  obtain ⟨a, ha, haR⟩ := ProjectiveSpace.exists_comap_universalSigmaImmersedHilbertFamily_eq ι n
    e A r hr s i hi hC πZ j.ker hR
  exact ⟨{ H := ProjectiveSpace.sigmaImmersedHilbertScheme ι n e A r hr s i
           πH := (ProjectiveSpace.sigmaImmersedHilbertSchemeOver ι n e A r hr s i).obj.hom
           D := ProjectiveSpace.universalSigmaImmersedHilbertFamily ι n e A r hr s i hi
           flat := ProjectiveSpace.flat_universalSigmaImmersedHilbertFamily ι n e A r hr s i hi hC
           isProper :=
             ProjectiveSpace.isProper_universalSigmaImmersedHilbertFamily ι n e A r hr s i hi hC
           surjective :=
             ProjectiveSpace.surjective_universalSigmaImmersedHilbertFamily_of_zero_notMem ι n e A
               r hr s i hi hC h0
           φ := a
           w := ha
           comap_eq := haR
           injective := fun T _ g b b' hb hb' h =>
             ProjectiveSpace.eq_of_comap_universalSigmaImmersedHilbertFamily_eq ι n e A r hr s i
               hi hC T g b b' hb hb' h },
    ProjectiveSpace.isHQuasiProjective_sigmaImmersedHilbertSchemeOver_hom ι n e A r hr s i⟩

variable {A : Type u} [CommRing A] {Z R : Scheme.{u}}

/-- **Existence of the quotient by a flat proper equivalence relation** (Nitsure,
arXiv:math/0504590v1, Theorem 6.9, p. 36, by the proof of Theorem 6.8, pp. 33–35, over
`S = Spec A`, on locally Noetherian points): let `A` be a Noetherian ring, `πZ : Z ⟶ Spec A`
H-quasi-projective and `p₁, p₂ : R ⟶ Z` with `p₁ ≫ πZ = p₂ ≫ πZ`, `p₂` proper and flat, such that
for every locally Noetherian scheme `T` the map `R(T) ⟶ Z(T) × Z(T)` is injective and its image is
an equivalence relation on `Z(T)`. Then `Z` has a flat proper quotient by `(p₁, p₂)`: an
H-quasi-projective `Q` over `Spec A` and a flat, surjective, proper `q : Z ⟶ Q` over `Spec A` with
`R = Z ×_Q Z` through `(p₁, p₂)`. -/
theorem nonempty_flatProperQuotient [IsNoetherianRing A] (πZ : Z ⟶ Spec (.of A))
    [IsHQuasiProjective πZ] (p₁ p₂ : R ⟶ Z) (hp : p₁ ≫ πZ = p₂ ≫ πZ) [IsProper p₂] [Flat p₂]
    (hinj : ∀ (T : Scheme.{u}) [IsLocallyNoetherian T] (r r' : T ⟶ R),
      r ≫ p₁ = r' ≫ p₁ → r ≫ p₂ = r' ≫ p₂ → r = r')
    (hequiv : ∀ (T : Scheme.{u}) [IsLocallyNoetherian T],
      _root_.Equivalence (pointsRelation p₁ p₂ T)) :
    Nonempty (FlatProperQuotient πZ p₁ p₂) := by
  have := IsHQuasiProjective.isLocallyNoetherian πZ
  have := isClosedImmersion_pullback_lift_of_isProper_snd_of_locallyNoetherian_injective πZ p₁ p₂ hp
    hinj
  -- The diagonal is a section of `p₂` (reflexivity at `T = Z`), so `p₂` is surjective.
  have : Surjective p₂ := by
    obtain ⟨d, -, hd⟩ := (hequiv Z).refl (𝟙 Z)
    have : Surjective (d ≫ p₂) := by
      rw [hd]
      infer_instance
    exact Surjective.of_comp d p₂
  have : IsProper (pullback.lift p₁ p₂ hp ≫ pullback.snd πZ πZ) := by
    rw [pullback.lift_snd]
    infer_instance
  have : Flat (pullback.lift p₁ p₂ hp ≫ pullback.snd πZ πZ) := by
    rw [pullback.lift_snd]
    infer_instance
  have : Surjective (pullback.lift p₁ p₂ hp ≫ pullback.snd πZ πZ) := by
    rw [pullback.lift_snd]
    infer_instance
  obtain ⟨𝔥, _⟩ := QuotientHilbertDatum.exists_isHQuasiProjective πZ (pullback.lift p₁ p₂ hp)
  have := IsHQuasiProjective.isLocallyNoetherian 𝔥.πH
  exact 𝔥.nonempty_flatProperQuotient_of_comp_eq (pullback.lift_fst _ _ _)
    (pullback.lift_snd _ _ _) hequiv

namespace FlatProperQuotient

variable {πZ : Z ⟶ Spec (.of A)} {p₁ p₂ : R ⟶ Z}

/-- **The flipped quotient**: a flat proper quotient of `Z` by `(p₂, p₁)` is a flat proper quotient
by `(p₁, p₂)`, with the same quotient morphism and the flipped cartesian square. -/
def flip (𝔮 : FlatProperQuotient πZ p₂ p₁) : FlatProperQuotient πZ p₁ p₂ where
  Q := 𝔮.Q
  πQ := 𝔮.πQ
  q := 𝔮.q
  fac := 𝔮.fac
  isHQuasiProjective := 𝔮.isHQuasiProjective
  flat := 𝔮.flat
  surjective := 𝔮.surjective
  isProper := 𝔮.isProper
  isPullback := 𝔮.isPullback.flip

@[simp]
theorem flip_q (𝔮 : FlatProperQuotient πZ p₂ p₁) : 𝔮.flip.q = 𝔮.q :=
  rfl

@[simp]
theorem flip_πQ (𝔮 : FlatProperQuotient πZ p₂ p₁) : 𝔮.flip.πQ = 𝔮.πQ :=
  rfl

end FlatProperQuotient

/-- **Existence of the quotient, first projection proper and flat** (Nitsure,
arXiv:math/0504590v1, Theorem 6.9, p. 36): `nonempty_flatProperQuotient` applied to the relation
`(p₂, p₁)`, which is again injective and an equivalence relation on locally Noetherian points, and
then flipped (`FlatProperQuotient.flip`). -/
theorem nonempty_flatProperQuotient_of_isProper_fst_of_flat_fst [IsNoetherianRing A]
    (πZ : Z ⟶ Spec (.of A)) [IsHQuasiProjective πZ] (p₁ p₂ : R ⟶ Z) (hp : p₁ ≫ πZ = p₂ ≫ πZ)
    [IsProper p₁] [Flat p₁]
    (hinj : ∀ (T : Scheme.{u}) [IsLocallyNoetherian T] (r r' : T ⟶ R),
      r ≫ p₁ = r' ≫ p₁ → r ≫ p₂ = r' ≫ p₂ → r = r')
    (hequiv : ∀ (T : Scheme.{u}) [IsLocallyNoetherian T],
      _root_.Equivalence (pointsRelation p₁ p₂ T)) :
    Nonempty (FlatProperQuotient πZ p₁ p₂) := by
  obtain ⟨𝔮⟩ := nonempty_flatProperQuotient πZ p₂ p₁ hp.symm
    (fun T _ r r' h₂ h₁ => hinj T r r' h₁ h₂) fun T _ => equivalence_pointsRelation_swap (hequiv T)
  exact ⟨𝔮.flip⟩

end AlgebraicGeometry
