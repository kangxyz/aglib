/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.HilbertScheme.Quotient.Existence
public import Aglib.AlgebraicGeometry.HilbertScheme.Quotient.LocallyNoetherianOver
public import Aglib.AlgebraicGeometry.Picard.FiberCondition.Surjective
public import Aglib.AlgebraicGeometry.Picard.FppfSections
public import Aglib.AlgebraicGeometry.Picard.Strata.Relation.Properties
public import Aglib.AlgebraicGeometry.Sites.FppfQuotient

/-!
# The quotient `Q = Z / R` represents the fine stratum `Pic^{φ₀,ψ,k+1}_0`

Let `A` be a Noetherian ring, `S = Spec A`, `i : X ⟶ P^N_A = ProjectiveSpace A ι` a closed
immersion with `ι ≃ Fin (N + 1)` such that `πX = i ≫ toSpec A ι` (proper, as `ι` is finite) is
flat and geometrically integral, `φ₀, ψ ∈ ℚ[X]`, `r = k + 1 ≥ 1`,
`C = fineCondition i N e φ₀ ψ 0 (k + 1)` the fibre condition of the stratum `Pic^{φ₀,ψ,r}_0` of
`P = Pic_{X/S,(fppf)}`, and `E` a representation of `Div^{ψ − φ₀}_X` on locally Noetherian test
schemes by an H-quasi-projective `D`. Let `Z = C.abelPreimageOver E`
(`Z = Pic^{φ₀,ψ,r}_0 ×_P Div^{ψ − φ₀}_X`, an H-quasi-projective Noetherian open subscheme of `D`)
with universal class `α_Z = C.abelPreimageFppfAbelClass E`, and `R = abelRelationOver e k E` with
projections `pr₁, pr₂ : R ⟶ Z`, which represents `Z ×_P Z`
(`Picard/Strata/Relation/Representability`).

* `Strata.abelRelation_w`: `pr₁` and `pr₂` agree over `S`.
* `Strata.abelQuotient e k E`: a flat proper quotient of `Z` by `R` (`FlatProperQuotient`), chosen
  by `nonempty_flatProperQuotient` (Nitsure, *Construction of Hilbert and Quot schemes*,
  arXiv:math/0504590v1, Theorem 6.9, p. 36). Its quotient `Q` is H-quasi-projective over `S`, its
  quotient morphism `q : Z ⟶ Q` is flat, surjective and proper, and `R = Z ×_Q Z`. As locally
  Noetherian test schemes: `(abelQuotient e k E).quotientOver` and
  `(abelQuotient e k E).quotientπ`.
* `Strata.comp_abelQuotientπ_eq_iff`: for `a, b : T ⟶ Z` with `T` locally Noetherian,
  `a ≫ q = b ≫ q` if and only if `a^* α_Z = b^* α_Z`, that is, `Z ×_Q Z = Z ×_P Z` on locally
  Noetherian points.
* `Strata.abelQuotientFppfClass e k E`: the section `λ ∈ P(Q)` with `q^* λ = α_Z`, unique
  (`fppfPicardSheaf_map_abelQuotientFppfClass`, `eq_abelQuotientFppfClass_of_map_eq`); it lies in
  `Pic^{φ₀,ψ,r}_0(Q)` (`abelQuotientFppfClass_mem_subfunctor`).
* `Strata.abelQuotientRepresentableByOfExistsLift e k E hloc`: **`Q` represents
  `Pic^{φ₀,ψ,r}_0` on locally Noetherian test schemes**, through `f ↦ f^* λ`
  (`abelQuotientRepresentableByOfExistsLift_homEquiv_coe`); `q` corresponds to `α_Z`
  (`abelQuotientRepresentableByOfExistsLift_homEquiv_quotientπ`).
* `Strata.exists_fineCondition_representableBy_of_exists_lift`: the same as an existence
  statement: there are an H-quasi-projective `Q` over `S`, a flat surjective proper `q : Z ⟶ Q` and
  `λ ∈ P(Q)` with `q^* λ = α_Z` such that `f ↦ f^* λ` is a representation of `Pic^{φ₀,ψ,r}_0` by
  `Q`.

The hypothesis `hloc` of the last two items is the local lifting property: for a locally Noetherian
test scheme `T`, every `ξ ∈ Pic^{φ₀,ψ,r}_0(T)` and every `t ∈ T`, there are a locally Noetherian
`U`, a flat morphism `f : U ⟶ T` locally of finite presentation with `t` in its image, and
`a : U ⟶ Z` with `a^* α_Z = f^* ξ`. It is hypothesis (h₃) of `Scheme.representableByOfFppfQuotient`,
up to the name of the bound morphism, and it says that `α : Z ⟶ Pic^{φ₀,ψ,r}_0` is fppf-locally
surjective. This file takes it as a hypothesis; it is proved in
`Aglib.AlgebraicGeometry.Picard.Strata.LocalSections`, and the unconditional forms
(`Strata.abelQuotientRepresentableBy`, `Strata.exists_fineCondition_representableBy`) are in
`Aglib.AlgebraicGeometry.Picard.Strata.Representability`.

This is Kleiman, *The Picard scheme*, arXiv:math/0504020v1, the end of the proof of Thm 4.8,
p. 30 ("Therefore, the theorem now results from the following general lemma"), and Lemma 4.9
(statement p. 30, proof pp. 30–31) for `α : Z → P_0^{φ0}`, in the fppf topology and on locally
Noetherian test schemes, through its fppf form `Scheme.representableByOfFppfQuotient`
(`Aglib.AlgebraicGeometry.Sites.FppfQuotient`). The pair conditions (h₁), (h₂) of that lemma
are `comp_abelQuotientπ_eq_iff`, which follows from Kleiman's two descriptions of `R`: `R = Z ×_P Z`
(`R` represents the pairs with `a^* α_Z = b^* α_Z`) and `R = Z ×_Q Z` (the cartesian square of
the quotient). Its descent hypothesis holds because `Pic^{φ₀,ψ,r}_0` descends along the surjective
`q` (`FiberCondition.mem_subfunctor_of_map_mem`). Differences from the source:

* Kleiman's quotient is "a quasi-projective `S`-scheme `Q` and a faithfully flat and projective
  map `Z → Q` such that `R = Z ×_Q Z`" (p. 30); here `Q` is H-quasi-projective (a quasi-compact
  immersion into some `P(κ)_A`, `κ` finite) and `q` is flat, surjective and proper. The smoothness
  of `Z → Q` (p. 31) is neither proved nor used.
* Kleiman shows that `Q` represents `P_0^{φ0}` by identifying both with the coequalizer of
  `R ⇉ Z` among étale sheaves (Exercise 4.10, p. 31). Here the section `λ` is obtained from the
  sheaf condition of `P` for the fppf covering `q`, injectivity of `f ↦ f^* λ` from the
  epimorphism property of fppf surjections, and surjectivity from `hloc` and the fppf sheaf
  property of the functor of points of `Q`; no coequalizer statement and no effective descent of
  line bundles is used. `λ` is a section of `P`, not a class of a line bundle on `X ×_S Q`.
* The stratum is the fine stratum `Pic^{φ₀,ψ,r}_0` (`fineCondition`), the part of Kleiman's
  `P_0^{φ0}` where `χ(X_t, 𝒪_{X_t}(n)) = ψ(n)` for all `n` and `h^0(X_t, L_t) = r = k + 1 ≥ 1`;
  Kleiman instead makes `ψ` constant by replacing `S` by an open and closed subset (p. 30). Only
  locally Noetherian test schemes are used.
-/

@[expose] public section

noncomputable section

open CategoryTheory Limits Opposite

universe u

namespace AlgebraicGeometry.Scheme.RelativePicard.Strata

open ProjectiveSpace

variable {A : Type u} [CommRing A] {ι : Type u} {X : Scheme.{u}}
  {i : X ⟶ ProjectiveSpace A ι} [IsClosedImmersion i] [Flat (i ≫ toSpec A ι)]
  [GeometricallyIntegral (i ≫ toSpec A ι)]
  {N : ℕ} (e : ι ≃ Fin (N + 1)) {φ₀ ψ : Polynomial ℚ} (k : ℕ)
  {D : Scheme.LocallyNoetherianOver (Spec (CommRingCat.of A))}
  (E : (locallyNoetherianRelativeDivisorFunctor i rfl (ψ - φ₀)).RepresentableBy D)

/-- **The two projections of `R = Z ×_P Z` agree over `S = Spec A`**:
`pr₁ ≫ (Z ⟶ S) = pr₂ ≫ (Z ⟶ S)`, the hypothesis `hp` of the quotient theorem
`nonempty_flatProperQuotient`. -/
theorem abelRelation_w :
    (abelRelationFst e k E).hom.left ≫
        ((fineCondition i N e φ₀ ψ 0 (k + 1)).abelPreimageOver E).obj.hom =
      (abelRelationSnd e k E).hom.left ≫
        ((fineCondition i N e φ₀ ψ 0 (k + 1)).abelPreimageOver E).obj.hom :=
  (Over.w (abelRelationFst e k E).hom).trans (Over.w (abelRelationSnd e k E).hom).symm

variable [IsNoetherianRing A] [IsHQuasiProjective D.obj.hom]

/-- **The quotient `Q = Z / R`** (Kleiman, arXiv:math/0504020v1, proof of Lemma 4.9, p. 30: "there
exist a quasi-projective `S`-scheme `Q` and a faithfully flat and projective map `Z → Q` such that
`R = Z ×_Q Z`"): a flat proper quotient of `Z` by `R`, chosen by the quotient theorem
`nonempty_flatProperQuotient` (Nitsure, arXiv:math/0504590v1, Theorem 6.9, p. 36). Its hypotheses
hold because `Z` is H-quasi-projective, `pr₂` is proper and flat, and `R(T) ⟶ Z(T) × Z(T)` is
injective with image an equivalence relation for every locally Noetherian `T`. -/
def abelQuotient :
    FlatProperQuotient ((fineCondition i N e φ₀ ψ 0 (k + 1)).abelPreimageOver E).obj.hom
      (abelRelationFst e k E).hom.left (abelRelationSnd e k E).hom.left :=
  (nonempty_flatProperQuotient ((fineCondition i N e φ₀ ψ 0 (k + 1)).abelPreimageOver E).obj.hom
    (abelRelationFst e k E).hom.left (abelRelationSnd e k E).hom.left (abelRelation_w e k E)
    (abelRelation_left_injective e k E) (equivalence_pointsRelation_abelRelation e k E)).some

/-- **`Z ×_Q Z = Z ×_P Z` on locally Noetherian points**: two points `a, b : T ⟶ Z` of a locally
Noetherian test scheme have the same image in `Q` if and only if they pull the universal class
`α_Z` back to the same class. The forward direction uses `pr₁^* α_Z = pr₂^* α_Z` and the cartesian
square `R = Z ×_Q Z`; the converse, that a pair with equal classes factors through `R`. -/
theorem comp_abelQuotientπ_eq_iff {T : Scheme.LocallyNoetherianOver (Spec (CommRingCat.of A))}
    (a b : T ⟶ (fineCondition i N e φ₀ ψ 0 (k + 1)).abelPreimageOver E) :
    a ≫ (abelQuotient e k E).quotientπ = b ≫ (abelQuotient e k E).quotientπ ↔
      (fppfPicardSheaf (i ≫ toSpec A ι)).obj.map a.hom.op
          ((fineCondition i N e φ₀ ψ 0 (k + 1)).abelPreimageFppfAbelClass E) =
        (fppfPicardSheaf (i ≫ toSpec A ι)).obj.map b.hom.op
          ((fineCondition i N e φ₀ ψ 0 (k + 1)).abelPreimageFppfAbelClass E) :=
  ⟨fun h => Scheme.map_eq_map_of_comp_eq_of_isPullback
      (F := (fppfPicardSheaf (i ≫ toSpec A ι)).obj ⋙ CategoryTheory.forget AddCommGrpCat)
      (abelQuotient e k E).quotientπ
      ((fineCondition i N e φ₀ ψ 0 (k + 1)).abelPreimageFppfAbelClass E)
      (abelRelationFst e k E).hom (abelRelationSnd e k E).hom
      (abelQuotient e k E).isPullback_quotientπ
      (fppfPicardSheaf_map_abelRelationFst_eq_map_abelRelationSnd e k E) a b h,
    comp_eq_comp_of_fppfPicardSheaf_map_eq_of_abelRelationFst_comp_eq_abelRelationSnd_comp e k E
      (abelQuotient e k E).quotientπ (abelQuotient e k E).isPullback_quotientπ.w a b⟩

/-- **The descended class `λ ∈ Pic_{X/S,(fppf)}(Q)`**: the unique section with `q^* λ = α_Z`
(`fppfPicardSheaf_map_abelQuotientFppfClass`, `eq_abelQuotientFppfClass_of_map_eq`), from the
sheaf condition of `Pic_{X/S,(fppf)}` for the fppf covering `q`
(`Scheme.fppfQuotientSection`); `α_Z` has equal pullbacks to `Z ×_Q Z` by
`comp_abelQuotientπ_eq_iff`. It is a section of the sheaf, not the class of a line bundle on
`X ×_S Q`. -/
def abelQuotientFppfClass :
    (fppfPicardSheaf (i ≫ toSpec A ι)).obj.obj (op (abelQuotient e k E).quotientOver.obj) :=
  Scheme.fppfQuotientSection (isSheaf_fppfPicardSheaf_forget (i ≫ toSpec A ι))
    (abelQuotient e k E).quotientπ
    ((fineCondition i N e φ₀ ψ 0 (k + 1)).abelPreimageFppfAbelClass E)
    fun _ a b h => (comp_abelQuotientπ_eq_iff e k E a b).mp h

/-- **`q^* λ = α_Z`**: the descended class pulls back to the universal class of `Z`. -/
theorem fppfPicardSheaf_map_abelQuotientFppfClass :
    (fppfPicardSheaf (i ≫ toSpec A ι)).obj.map (abelQuotient e k E).quotientπ.hom.op
        (abelQuotientFppfClass e k E) =
      (fineCondition i N e φ₀ ψ 0 (k + 1)).abelPreimageFppfAbelClass E :=
  Scheme.map_fppfQuotientSection (isSheaf_fppfPicardSheaf_forget (i ≫ toSpec A ι))
    (abelQuotient e k E).quotientπ _ _

/-- **Uniqueness of `λ`**: every section of `Pic_{X/S,(fppf)}` over `Q` pulling back to `α_Z`
along `q` is `λ`. -/
theorem eq_abelQuotientFppfClass_of_map_eq
    {l : (fppfPicardSheaf (i ≫ toSpec A ι)).obj.obj (op (abelQuotient e k E).quotientOver.obj)}
    (hl : (fppfPicardSheaf (i ≫ toSpec A ι)).obj.map (abelQuotient e k E).quotientπ.hom.op l =
      (fineCondition i N e φ₀ ψ 0 (k + 1)).abelPreimageFppfAbelClass E) :
    l = abelQuotientFppfClass e k E :=
  Scheme.eq_fppfQuotientSection_of_map_eq (isSheaf_fppfPicardSheaf_forget (i ≫ toSpec A ι))
    (abelQuotient e k E).quotientπ _ _ hl

/-- **`λ` lies in the stratum** `Pic^{φ₀,ψ,k+1}_0(Q)`: its pullback `α_Z` along the surjective `q`
does (`FiberCondition.mem_subfunctor_of_map_mem`). -/
theorem abelQuotientFppfClass_mem_subfunctor :
    abelQuotientFppfClass e k E ∈
      (fineCondition i N e φ₀ ψ 0 (k + 1)).subfunctor.obj
        (op (abelQuotient e k E).quotientOver.obj) :=
  (fineCondition i N e φ₀ ψ 0 (k + 1)).mem_subfunctor_of_map_mem (abelQuotient e k E).quotientπ.hom
    (abelQuotient e k E).quotientπ.hom.left.surjective
    ((fppfPicardSheaf_map_abelQuotientFppfClass e k E).symm ▸
      (fineCondition i N e φ₀ ψ 0 (k + 1)).abelPreimageFppfAbelClass_mem_subfunctor E)

variable
  (hloc : ∀ ⦃T : Scheme.LocallyNoetherianOver (Spec (CommRingCat.of A))⦄
    (ξ : ((fppfPicardSheaf (i ≫ toSpec A ι)).obj ⋙ CategoryTheory.forget AddCommGrpCat).obj
      (op T.obj)),
    ξ ∈ (fineCondition i N e φ₀ ψ 0 (k + 1)).locallyNoetherianSubfunctor.obj (op T) →
      ∀ t : T.obj.left, ∃ (U : Scheme.LocallyNoetherianOver (Spec (CommRingCat.of A)))
        (f : U ⟶ T) (a : U ⟶ (fineCondition i N e φ₀ ψ 0 (k + 1)).abelPreimageOver E),
        Flat f.hom.left ∧ LocallyOfFinitePresentation f.hom.left ∧ t ∈ Set.range f.hom.left ∧
          ((fppfPicardSheaf (i ≫ toSpec A ι)).obj ⋙ CategoryTheory.forget AddCommGrpCat).map
              a.hom.op ((fineCondition i N e φ₀ ψ 0 (k + 1)).abelPreimageFppfAbelClass E) =
            ((fppfPicardSheaf (i ≫ toSpec A ι)).obj ⋙ CategoryTheory.forget AddCommGrpCat).map
              f.hom.op ξ)

/-- **`Q` represents the fine stratum `Pic^{φ₀,ψ,k+1}_0` on locally Noetherian test schemes**
(Kleiman, arXiv:math/0504020v1, Lemma 4.9, p. 30, for `α : Z → P_0^{φ0}` as in the proof of
Thm 4.8, p. 30; fppf form `Scheme.representableByOfFppfQuotient`), given the local lifting
property `hloc` of `α`: a morphism `f : T ⟶ Q` corresponds to `f^* λ`
(`abelQuotientRepresentableByOfExistsLift_homEquiv_coe`). -/
def abelQuotientRepresentableByOfExistsLift :
    (fineCondition i N e φ₀ ψ 0 (k + 1)).locallyNoetherianSubfunctor.toFunctor.RepresentableBy
      (abelQuotient e k E).quotientOver :=
  Scheme.representableByOfFppfQuotient (isSheaf_fppfPicardSheaf_forget (i ≫ toSpec A ι))
    (fineCondition i N e φ₀ ψ 0 (k + 1)).locallyNoetherianSubfunctor (abelQuotient e k E).quotientπ
    ((fineCondition i N e φ₀ ψ 0 (k + 1)).abelPreimageFppfAbelClass E)
    ((fineCondition i N e φ₀ ψ 0 (k + 1)).abelPreimageFppfAbelClass_mem_subfunctor E)
    (fun _ h => (fineCondition i N e φ₀ ψ 0 (k + 1)).mem_subfunctor_of_map_mem
      (abelQuotient e k E).quotientπ.hom (abelQuotient e k E).quotientπ.hom.left.surjective h)
    (fun _ a b h => (comp_abelQuotientπ_eq_iff e k E a b).mpr h)
    (fun _ a b h => (comp_abelQuotientπ_eq_iff e k E a b).mp h) hloc

/-- **The representation is `f ↦ f^* λ`.** -/
theorem abelQuotientRepresentableByOfExistsLift_homEquiv_coe
    {T : Scheme.LocallyNoetherianOver (Spec (CommRingCat.of A))}
    (f : T ⟶ (abelQuotient e k E).quotientOver) :
    ((abelQuotientRepresentableByOfExistsLift e k E hloc).homEquiv f).1 =
      (fppfPicardSheaf (i ≫ toSpec A ι)).obj.map f.hom.op (abelQuotientFppfClass e k E) :=
  rfl

/-- **The quotient morphism corresponds to the Abel map**: under the representation, `q : Z ⟶ Q`
corresponds to the universal class `α_Z`, so `α : Z → Pic^{φ₀,ψ,k+1}_0` is represented by `q`
(Kleiman, arXiv:math/0504020v1, Lemma 4.9, p. 30, where the representing map `Z → Q` is smooth;
here `q` is flat, surjective and proper). -/
theorem abelQuotientRepresentableByOfExistsLift_homEquiv_quotientπ :
    ((abelQuotientRepresentableByOfExistsLift e k E hloc).homEquiv
        (abelQuotient e k E).quotientπ).1 =
      (fineCondition i N e φ₀ ψ 0 (k + 1)).abelPreimageFppfAbelClass E :=
  fppfPicardSheaf_map_abelQuotientFppfClass e k E

include hloc in
/-- **The fine stratum `Pic^{φ₀,ψ,k+1}_0` is represented by an H-quasi-projective quotient of `Z`**
(Kleiman, arXiv:math/0504020v1, Lemma 4.9, p. 30, proof pp. 30–31, applied at the end of the proof
of Thm 4.8, p. 30; fppf form, on locally Noetherian test schemes), given the local lifting
property `hloc` of `α : Z → Pic^{φ₀,ψ,k+1}_0`: there are an H-quasi-projective `Q` over `S`, a
flat, surjective and proper `q : Z ⟶ Q` and `λ ∈ Pic_{X/S,(fppf)}(Q)` with `q^* λ = α_Z`, such that
`f ↦ f^* λ` is a representation of `Pic^{φ₀,ψ,k+1}_0` by `Q` on locally Noetherian test
schemes. -/
theorem exists_fineCondition_representableBy_of_exists_lift :
    ∃ (Q : Scheme.LocallyNoetherianOver (Spec (CommRingCat.of A)))
      (q : (fineCondition i N e φ₀ ψ 0 (k + 1)).abelPreimageOver E ⟶ Q)
      (l : (fppfPicardSheaf (i ≫ toSpec A ι)).obj.obj (op Q.obj))
      (rep :
        (fineCondition i N e φ₀ ψ 0 (k + 1)).locallyNoetherianSubfunctor.toFunctor.RepresentableBy
          Q),
      IsHQuasiProjective Q.obj.hom ∧ Flat q.hom.left ∧ Surjective q.hom.left ∧
        IsProper q.hom.left ∧
        (fppfPicardSheaf (i ≫ toSpec A ι)).obj.map q.hom.op l =
          (fineCondition i N e φ₀ ψ 0 (k + 1)).abelPreimageFppfAbelClass E ∧
        ∀ {T : Scheme.LocallyNoetherianOver (Spec (CommRingCat.of A))} (f : T ⟶ Q),
          (rep.homEquiv f).1 = (fppfPicardSheaf (i ≫ toSpec A ι)).obj.map f.hom.op l :=
  ⟨(abelQuotient e k E).quotientOver, (abelQuotient e k E).quotientπ, abelQuotientFppfClass e k E,
    abelQuotientRepresentableByOfExistsLift e k E hloc, inferInstance, inferInstance,
    inferInstance, inferInstance, fppfPicardSheaf_map_abelQuotientFppfClass e k E,
    fun f => abelQuotientRepresentableByOfExistsLift_homEquiv_coe e k E hloc f⟩

end AlgebraicGeometry.Scheme.RelativePicard.Strata
