/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Properties.Noetherian.LocallyNoetherianOver
public import Mathlib.AlgebraicGeometry.Sites.Fpqc
public import Mathlib.CategoryTheory.Sites.SubcanonicalOver
public import Mathlib.CategoryTheory.Subfunctor.Basic

/-!
# Representability by an fppf quotient (Kleiman's Lemma 4.9, fppf form)

Let `S` be a scheme, `F` a presheaf of sets on `Over S` that is a sheaf for
`Scheme.fppfTopology.over S`, and `G ⊆ F` a subfunctor on locally Noetherian test schemes, that
is, a subfunctor of the restriction of `F` to `Scheme.LocallyNoetherianOver S` (for a subfunctor
of `F` on all of `Over S`, take its restriction `LocalRepresentability.restrictSubfunctor`). Let
`Z` and `Q` be locally Noetherian schemes over `S`, `z ∈ G(Z)`, and `q : Z ⟶ Q` a morphism over
`S` that is flat, surjective and locally of finite presentation. Assume, for all locally
Noetherian test schemes `T` over `S`:

* (h₁) two morphisms `a b : T ⟶ Z` with `a^* z = b^* z` satisfy `a ≫ q = b ≫ q`;
* (h₂) two morphisms `a b : T ⟶ Z` with `a ≫ q = b ≫ q` satisfy `a^* z = b^* z`;
* (h₃) every `ξ ∈ G(T)` lifts to `Z` fppf-locally: through every point of `T` there are a flat
  morphism `k : U ⟶ T` locally of finite presentation, with `U` locally Noetherian, and
  `a : U ⟶ Z` with `a^* z = k^* ξ`;
* (descent along `q`) a section `ξ ∈ F(Q)` with `q^* ξ ∈ G(Z)` lies in `G(Q)`.

Then there is a unique `λ ∈ F(Q)` with `q^* λ = z` (`fppfQuotientSection`,
`map_fppfQuotientSection`, `eq_fppfQuotientSection_of_map_eq`), it lies in `G(Q)`
(`fppfQuotientSection_mem`), and `f ↦ f^* λ` is a bijection `Hom_S(T, Q) ≃ G(T)` for every
locally Noetherian `T`, natural in `T` (`representableByOfFppfQuotient`): `Q` represents `G` on
locally Noetherian test schemes.

This is Kleiman, *The Picard scheme*, arXiv:math/0504020v1, Lemma 4.9 (p. 30, proof pp. 30–31),
in the fppf topology, on locally Noetherian test schemes, and with the quotient given. In
Kleiman's notation `α : Z → P` is the map of sheaves defined by `z`, and `R = Z ×_P Z`; his proof
constructs a flat projective `q : Z → Q` with `R = Z ×_Q Z` (pp. 30–31). Here `Q` and `q` are
data. Conditions (h₁) and (h₂) together say `R = Z ×_Q Z` on locally Noetherian points. (h₂) is
stated for pairs of points; it follows from its universal form, equality of the two pullbacks of
`z` along a cartesian square `R ⇉ Z ⟶ Q` (`map_eq_map_of_comp_eq_of_isPullback`), and it gives
the same condition for pairs from all `S`-schemes, since `Z ×_Q Z` is locally Noetherian
(`map_eq_map_of_comp_eq_of_locallyNoetherian`). Condition (h₃) says that `α` is fppf-locally
surjective onto `G` ("α is a surjection", p. 30). Kleiman's last step (p. 31) identifies `Q`
and `P` with the coequalizer of `R ⇉ Z` through his Exercise 4.10. That step is replaced here by
* the sheaf condition of `F` for the single fppf covering `q`, which gives `λ`;
* the injectivity of `f ↦ f^* λ`, from (h₁) on a fibre product covering `T` and the epimorphism
  property of fppf surjections (Mathlib's `EffectiveEpi` instance for flat surjective morphisms
  locally of finite presentation; `hom_ext_of_fppfQuotient`);
* its surjectivity, from (h₃), (h₁) on the fibre products of the local lifts, and the fppf sheaf
  property of the functor of points of `Q` (the fppf topology is subcanonical;
  `exists_map_eq_of_fppfQuotient`).

No coequalizer statement and no effective descent of objects is used. The section `λ` is a
section of `F`, not an object to be descended. Descent of `G` is needed only along `q`; it holds,
for example, for a subfunctor cut out by a pointwise condition invariant under base change (for
the Picard strata, `RelativePicard.FiberCondition.mem_subfunctor_of_map_mem`). Kleiman's further
conclusions (`Q` quasi-projective, `α` smooth) are not part of this statement.

Covering families are handled by `ofArrows_mem_fppfTopology_over`: a jointly surjective family of
flat morphisms locally of finite presentation over `S` generates a covering sieve of
`Scheme.fppfTopology.over S`.
-/

@[expose] public section

noncomputable section

open CategoryTheory Limits Opposite

universe v u

namespace AlgebraicGeometry.Scheme

variable {S : Scheme.{u}}

/-- A jointly surjective family of morphisms of `S`-schemes, each flat and locally of finite
presentation, generates a covering sieve of `Scheme.fppfTopology.over S`. -/
theorem ofArrows_mem_fppfTopology_over {T : Over S} {ι : Type*} (U : ι → Over S)
    (k : ∀ i, U i ⟶ T) (hflat : ∀ i, Flat (k i).left)
    (hlfp : ∀ i, LocallyOfFinitePresentation (k i).left)
    (hcov : ∀ t : T.left, ∃ i, t ∈ Set.range (k i).left) :
    Sieve.ofArrows U k ∈ (Scheme.fppfTopology.over S) T := by
  rw [GrothendieckTopology.mem_over_iff, Sieve.overEquiv_ofArrows]
  exact Precoverage.generate_mem_toGrothendieck
    ((ofArrows_mem_precoverage_iff (@Flat ⊓ @LocallyOfFinitePresentation)).2
      ⟨hcov, fun i => ⟨hflat i, hlfp i⟩⟩)

variable {F : (Over S)ᵒᵖ ⥤ Type v} {Z Q : LocallyNoetherianOver S}

/-- The pair condition (h₂) on locally Noetherian test schemes gives the same condition for all
schemes over `S`: two morphisms `gi gj : Y ⟶ Z` with `gi ≫ q = gj ≫ q` factor through the fibre
product `Z ×_Q Z`, which is locally Noetherian because `q` is locally of finite presentation. -/
theorem map_eq_map_of_comp_eq_of_locallyNoetherian (q : Z ⟶ Q)
    [LocallyOfFinitePresentation q.hom.left] (z : F.obj (op Z.obj))
    (h₂ : ∀ ⦃T : LocallyNoetherianOver S⦄ (a b : T ⟶ Z), a ≫ q = b ≫ q →
      F.map a.hom.op z = F.map b.hom.op z)
    {Y : Over S} (gi gj : Y ⟶ Z.obj) (hij : gi ≫ q.hom = gj ≫ q.hom) :
    F.map gi.op z = F.map gj.op z := by
  let W : Over S := Over.mk (pullback.fst q.hom.left q.hom.left ≫ Z.obj.hom)
  have hW : IsLocallyNoetherian W.left :=
    inferInstanceAs (IsLocallyNoetherian (pullback q.hom.left q.hom.left))
  let p₁ : W ⟶ Z.obj := Over.homMk (pullback.fst q.hom.left q.hom.left)
  let p₂ : W ⟶ Z.obj := Over.homMk (pullback.snd q.hom.left q.hom.left) (by
    change pullback.snd q.hom.left q.hom.left ≫ Z.obj.hom =
      pullback.fst q.hom.left q.hom.left ≫ Z.obj.hom
    rw [← Over.w q.hom, pullback.condition_assoc])
  have key : F.map p₁.op z = F.map p₂.op z :=
    h₂ (T := ⟨W, hW⟩) (ObjectProperty.homMk p₁) (ObjectProperty.homMk p₂)
      (ObjectProperty.hom_ext _ (Over.OverMorphism.ext
        (pullback.condition (f := q.hom.left) (g := q.hom.left))))
  have hij' : gi.left ≫ q.hom.left = gj.left ≫ q.hom.left := by
    simpa using congrArg CommaMorphism.left hij
  let c : Y ⟶ W := Over.homMk (pullback.lift gi.left gj.left hij') (by
    change pullback.lift gi.left gj.left hij' ≫ pullback.fst q.hom.left q.hom.left ≫ Z.obj.hom =
      Y.hom
    exact (pullback.lift_fst_assoc _ _ _ _).trans (Over.w gi))
  have e₁ : c ≫ p₁ = gi := Over.OverMorphism.ext (pullback.lift_fst _ _ _)
  have e₂ : c ≫ p₂ = gj := Over.OverMorphism.ext (pullback.lift_snd _ _ _)
  rw [← e₁, ← e₂, op_comp, op_comp, Functor.map_comp_apply, Functor.map_comp_apply, key]

/-- **(h₂) from a cartesian square.** If `p₁, p₂ : R ⟶ Z` over `S` form a cartesian square with
`q` and `q` (for example `R = Z ×_Q Z`, or a scheme representing Kleiman's `R = Z ×_P Z` together
with the identification `R = Z ×_Q Z`) and `p₁^* z = p₂^* z`, then (h₂) holds: two morphisms
`a b : T ⟶ Z` with `a ≫ q = b ≫ q` factor through `R`. This is the blueprint's universal form of
(h₂). -/
theorem map_eq_map_of_comp_eq_of_isPullback (q : Z ⟶ Q) (z : F.obj (op Z.obj)) {R : Over S}
    (p₁ p₂ : R ⟶ Z.obj) (hR : IsPullback p₁.left p₂.left q.hom.left q.hom.left)
    (hz : F.map p₁.op z = F.map p₂.op z) ⦃T : LocallyNoetherianOver S⦄ (a b : T ⟶ Z)
    (hab : a ≫ q = b ≫ q) : F.map a.hom.op z = F.map b.hom.op z := by
  have hab' : a.hom.left ≫ q.hom.left = b.hom.left ≫ q.hom.left :=
    congrArg (fun g => g.hom.left) hab
  let r : T.obj ⟶ R := Over.homMk (hR.lift a.hom.left b.hom.left hab') (by
    rw [← Over.w p₁, hR.lift_fst_assoc, Over.w a.hom])
  have e₁ : r ≫ p₁ = a.hom := Over.OverMorphism.ext (hR.lift_fst _ _ _)
  have e₂ : r ≫ p₂ = b.hom := Over.OverMorphism.ext (hR.lift_snd _ _ _)
  rw [← e₁, ← e₂, op_comp, op_comp, Functor.map_comp_apply, Functor.map_comp_apply, hz]

/-- **Descent along the fppf covering `q`.** Under the pair condition (h₂), a section
`z ∈ F(Z)` of an fppf sheaf descends uniquely along a flat surjective morphism `q : Z ⟶ Q`
locally of finite presentation: the sheaf condition for the covering `{q}`. -/
theorem existsUnique_map_eq_of_fppfQuotient
    (hF : Presieve.IsSheaf (Scheme.fppfTopology.over S) F) (q : Z ⟶ Q)
    [Flat q.hom.left] [Surjective q.hom.left] [LocallyOfFinitePresentation q.hom.left]
    (z : F.obj (op Z.obj))
    (h₂ : ∀ ⦃T : LocallyNoetherianOver S⦄ (a b : T ⟶ Z), a ≫ q = b ≫ q →
      F.map a.hom.op z = F.map b.hom.op z) :
    ∃! l : F.obj (op Q.obj), F.map q.hom.op l = z := by
  have hsh := hF.isSheafFor (Presieve.ofArrows (fun _ : PUnit.{1} => Z.obj) fun _ => q.hom)
    (ofArrows_mem_fppfTopology_over _ _ (fun _ => inferInstance) (fun _ => inferInstance)
      fun t => ⟨PUnit.unit, q.hom.left.surjective t⟩)
  rw [Presieve.isSheafFor_arrows_iff] at hsh
  obtain ⟨l, hl, hl'⟩ := hsh (fun _ => z) fun _ _ _ gi gj hij =>
    map_eq_map_of_comp_eq_of_locallyNoetherian q z h₂ gi gj hij
  exact ⟨l, hl PUnit.unit, fun l' h => hl' l' fun _ => h⟩

/-- **The descended section `λ`**: the unique section `λ ∈ F(Q)` with `q^* λ = z`
(`existsUnique_map_eq_of_fppfQuotient`), through which `Q` represents `G`
(`representableByOfFppfQuotient`). Kleiman's proof of Lemma 4.9 (arXiv:math/0504020v1,
pp. 30–31) names no such section: it identifies `Q` with `P` as coequalizers of `R ⇉ Z`
(Exercise 4.10, p. 31). -/
def fppfQuotientSection (hF : Presieve.IsSheaf (Scheme.fppfTopology.over S) F) (q : Z ⟶ Q)
    [Flat q.hom.left] [Surjective q.hom.left] [LocallyOfFinitePresentation q.hom.left]
    (z : F.obj (op Z.obj))
    (h₂ : ∀ ⦃T : LocallyNoetherianOver S⦄ (a b : T ⟶ Z), a ≫ q = b ≫ q →
      F.map a.hom.op z = F.map b.hom.op z) : F.obj (op Q.obj) :=
  (existsUnique_map_eq_of_fppfQuotient hF q z h₂).exists.choose

/-- The section `λ` pulls back to `z` along `q`. -/
theorem map_fppfQuotientSection (hF : Presieve.IsSheaf (Scheme.fppfTopology.over S) F)
    (q : Z ⟶ Q) [Flat q.hom.left] [Surjective q.hom.left]
    [LocallyOfFinitePresentation q.hom.left] (z : F.obj (op Z.obj))
    (h₂ : ∀ ⦃T : LocallyNoetherianOver S⦄ (a b : T ⟶ Z), a ≫ q = b ≫ q →
      F.map a.hom.op z = F.map b.hom.op z) :
    F.map q.hom.op (fppfQuotientSection hF q z h₂) = z :=
  (existsUnique_map_eq_of_fppfQuotient hF q z h₂).exists.choose_spec

/-- Uniqueness of `λ`: every section of `F` over `Q` pulling back to `z` along `q` is `λ`. -/
theorem eq_fppfQuotientSection_of_map_eq (hF : Presieve.IsSheaf (Scheme.fppfTopology.over S) F)
    (q : Z ⟶ Q) [Flat q.hom.left] [Surjective q.hom.left]
    [LocallyOfFinitePresentation q.hom.left] (z : F.obj (op Z.obj))
    (h₂ : ∀ ⦃T : LocallyNoetherianOver S⦄ (a b : T ⟶ Z), a ≫ q = b ≫ q →
      F.map a.hom.op z = F.map b.hom.op z)
    {l : F.obj (op Q.obj)} (hl : F.map q.hom.op l = z) : l = fppfQuotientSection hF q z h₂ :=
  (existsUnique_map_eq_of_fppfQuotient hF q z h₂).unique hl (map_fppfQuotientSection hF q z h₂)

/-- `λ` lies in `G(Q)` when `z ∈ G(Z)` and `G` descends along `q`. -/
theorem fppfQuotientSection_mem (hF : Presieve.IsSheaf (Scheme.fppfTopology.over S) F)
    (G : Subfunctor ((locallyNoetherianOverInclusion S).op ⋙ F)) (q : Z ⟶ Q) [Flat q.hom.left]
    [Surjective q.hom.left] [LocallyOfFinitePresentation q.hom.left] (z : F.obj (op Z.obj))
    (h₂ : ∀ ⦃T : LocallyNoetherianOver S⦄ (a b : T ⟶ Z), a ≫ q = b ≫ q →
      F.map a.hom.op z = F.map b.hom.op z)
    (hz : z ∈ G.obj (op Z))
    (hG : ∀ ξ : F.obj (op Q.obj), F.map q.hom.op ξ ∈ G.obj (op Z) → ξ ∈ G.obj (op Q)) :
    fppfQuotientSection hF q z h₂ ∈ G.obj (op Q) :=
  hG _ ((map_fppfQuotientSection hF q z h₂).symm ▸ hz)

/-- Injectivity on one covering: for an epimorphism `π : P ⟶ T` from a locally Noetherian scheme
along which `f₁` and `f₂` lift through `q`, the condition `f₁^* l = f₂^* l` gives `f₁ = f₂`,
by (h₁) at `P`. -/
theorem hom_ext_of_epi_of_fppfQuotient (q : Z ⟶ Q) (z : F.obj (op Z.obj))
    (h₁ : ∀ ⦃T : LocallyNoetherianOver S⦄ (a b : T ⟶ Z), F.map a.hom.op z = F.map b.hom.op z →
      a ≫ q = b ≫ q)
    {l : F.obj (op Q.obj)} (hl : F.map q.hom.op l = z) {T : LocallyNoetherianOver S}
    {f₁ f₂ : T ⟶ Q} (h : F.map f₁.hom.op l = F.map f₂.hom.op l) {P : Scheme.{u}}
    [IsLocallyNoetherian P] (π : P ⟶ T.obj.left) [Epi π] (y₁ y₂ : P ⟶ Z.obj.left)
    (hy₁ : y₁ ≫ q.hom.left = π ≫ f₁.hom.left) (hy₂ : y₂ ≫ q.hom.left = π ≫ f₂.hom.left) :
    f₁ = f₂ := by
  let W : Over S := Over.mk (π ≫ T.obj.hom)
  let πo : W ⟶ T.obj := Over.homMk π
  let w₁ : W ⟶ Z.obj := Over.homMk y₁ (by
    change y₁ ≫ Z.obj.hom = π ≫ T.obj.hom
    rw [← Over.w q.hom, reassoc_of% hy₁, Over.w f₁.hom])
  let w₂ : W ⟶ Z.obj := Over.homMk y₂ (by
    change y₂ ≫ Z.obj.hom = π ≫ T.obj.hom
    rw [← Over.w q.hom, reassoc_of% hy₂, Over.w f₂.hom])
  have e₁ : w₁ ≫ q.hom = πo ≫ f₁.hom := Over.OverMorphism.ext hy₁
  have e₂ : w₂ ≫ q.hom = πo ≫ f₂.hom := Over.OverMorphism.ext hy₂
  have hz : F.map w₁.op z = F.map w₂.op z := by
    calc F.map w₁.op z = F.map (w₁ ≫ q.hom).op l := by
          rw [op_comp, Functor.map_comp_apply, hl]
      _ = F.map πo.op (F.map f₁.hom.op l) := by rw [e₁, op_comp, Functor.map_comp_apply]
      _ = F.map πo.op (F.map f₂.hom.op l) := by rw [h]
      _ = F.map (w₂ ≫ q.hom).op l := by rw [e₂, op_comp, Functor.map_comp_apply]
      _ = F.map w₂.op z := by rw [op_comp, Functor.map_comp_apply, hl]
  have hq : w₁ ≫ q.hom = w₂ ≫ q.hom := congrArg InducedCategory.Hom.hom
    (h₁ (T := ⟨W, (inferInstance : IsLocallyNoetherian P)⟩) (ObjectProperty.homMk w₁)
      (ObjectProperty.homMk w₂) hz)
  have hπ : π ≫ f₁.hom.left = π ≫ f₂.hom.left := by
    rw [← hy₁, ← hy₂]
    exact congrArg CommaMorphism.left hq
  exact ObjectProperty.hom_ext _ (Over.OverMorphism.ext ((cancel_epi π).1 hπ))

/-- **Injectivity of `f ↦ f^* λ`** on locally Noetherian test schemes (Kleiman's Lemma 4.9,
fppf form): `f₁^* l = f₂^* l` for a section `l` with `q^* l = z` implies `f₁ = f₂`. The covering
is `T ×_{f₁,Q} Z ×_{f₂,Q} Z ⟶ T`, flat, surjective and locally of finite presentation, hence an
epimorphism, with locally Noetherian source. -/
theorem hom_ext_of_fppfQuotient (q : Z ⟶ Q) [Flat q.hom.left] [Surjective q.hom.left]
    [LocallyOfFinitePresentation q.hom.left] (z : F.obj (op Z.obj))
    (h₁ : ∀ ⦃T : LocallyNoetherianOver S⦄ (a b : T ⟶ Z), F.map a.hom.op z = F.map b.hom.op z →
      a ≫ q = b ≫ q)
    {l : F.obj (op Q.obj)} (hl : F.map q.hom.op l = z) {T : LocallyNoetherianOver S}
    {f₁ f₂ : T ⟶ Q} (h : F.map f₁.hom.op l = F.map f₂.hom.op l) : f₁ = f₂ :=
  hom_ext_of_epi_of_fppfQuotient q z h₁ hl h
    (pullback.fst (pullback.fst f₁.hom.left q.hom.left ≫ f₂.hom.left) q.hom.left ≫
      pullback.fst f₁.hom.left q.hom.left)
    (pullback.fst (pullback.fst f₁.hom.left q.hom.left ≫ f₂.hom.left) q.hom.left ≫
      pullback.snd f₁.hom.left q.hom.left)
    (pullback.snd (pullback.fst f₁.hom.left q.hom.left ≫ f₂.hom.left) q.hom.left)
    (by rw [Category.assoc, Category.assoc, ← pullback.condition])
    (by rw [Category.assoc, ← pullback.condition])

/-- Compatibility of two local lifts: if `a^* z = k^* ξ` and `a'^* z = k'^* ξ` for morphisms
`k : U ⟶ T` and `k' : V ⟶ T`, then (h₁) on the locally Noetherian fibre product `U ×_T V` makes
`a ≫ q` and `a' ≫ q` agree on every pair `gi, gj` with `gi ≫ k = gj ≫ k'`. -/
theorem comp_eq_comp_of_map_eq_of_fppfQuotient (q : Z ⟶ Q) (z : F.obj (op Z.obj))
    (h₁ : ∀ ⦃T : LocallyNoetherianOver S⦄ (a b : T ⟶ Z), F.map a.hom.op z = F.map b.hom.op z →
      a ≫ q = b ≫ q)
    {T : Over S} {U V : LocallyNoetherianOver S} (k : U.obj ⟶ T) (k' : V.obj ⟶ T)
    [LocallyOfFiniteType k'.left] (a : U ⟶ Z) (a' : V ⟶ Z) (ξ : F.obj (op T))
    (ha : F.map a.hom.op z = F.map k.op ξ) (ha' : F.map a'.hom.op z = F.map k'.op ξ)
    {Y : Over S} (gi : Y ⟶ U.obj) (gj : Y ⟶ V.obj) (hij : gi ≫ k = gj ≫ k') :
    gi ≫ a.hom ≫ q.hom = gj ≫ a'.hom ≫ q.hom := by
  let W : Over S := Over.mk (pullback.fst k.left k'.left ≫ U.obj.hom)
  have hW : IsLocallyNoetherian W.left :=
    inferInstanceAs (IsLocallyNoetherian (pullback k.left k'.left))
  let w₁ : W ⟶ U.obj := Over.homMk (pullback.fst k.left k'.left)
  let w₂ : W ⟶ V.obj := Over.homMk (pullback.snd k.left k'.left) (by
    change pullback.snd k.left k'.left ≫ V.obj.hom = pullback.fst k.left k'.left ≫ U.obj.hom
    rw [← Over.w k', ← Over.w k, pullback.condition_assoc])
  have hw : w₁ ≫ k = w₂ ≫ k' :=
    Over.OverMorphism.ext (pullback.condition (f := k.left) (g := k'.left))
  have hz : F.map (w₁ ≫ a.hom).op z = F.map (w₂ ≫ a'.hom).op z := by
    calc F.map (w₁ ≫ a.hom).op z = F.map w₁.op (F.map k.op ξ) := by
          rw [op_comp, Functor.map_comp_apply, ha]
      _ = F.map (w₁ ≫ k).op ξ := by rw [op_comp, Functor.map_comp_apply]
      _ = F.map (w₂ ≫ k').op ξ := by rw [hw]
      _ = F.map w₂.op (F.map k'.op ξ) := by rw [op_comp, Functor.map_comp_apply]
      _ = F.map (w₂ ≫ a'.hom).op z := by rw [op_comp, Functor.map_comp_apply, ha']
  have hq : (w₁ ≫ a.hom) ≫ q.hom = (w₂ ≫ a'.hom) ≫ q.hom := congrArg InducedCategory.Hom.hom
    (h₁ (T := ⟨W, hW⟩) (ObjectProperty.homMk (w₁ ≫ a.hom))
      (ObjectProperty.homMk (w₂ ≫ a'.hom)) hz)
  have hij' : gi.left ≫ k.left = gj.left ≫ k'.left := by
    simpa using congrArg CommaMorphism.left hij
  let c : Y ⟶ W := Over.homMk (pullback.lift gi.left gj.left hij') (by
    change pullback.lift gi.left gj.left hij' ≫ pullback.fst k.left k'.left ≫ U.obj.hom = Y.hom
    exact (pullback.lift_fst_assoc _ _ _ _).trans (Over.w gi))
  have e₁ : c ≫ w₁ = gi := Over.OverMorphism.ext (pullback.lift_fst _ _ _)
  have e₂ : c ≫ w₂ = gj := Over.OverMorphism.ext (pullback.lift_snd _ _ _)
  rw [← e₁, ← e₂]
  simp only [Category.assoc] at hq ⊢
  rw [hq]

/-- **Surjectivity of `f ↦ f^* λ`** onto `G(T)` on locally Noetherian test schemes (Kleiman's
Lemma 4.9, fppf form): the local lifts of (h₃) form an fppf covering of `T`; their composites with
`q` are compatible by (h₁), so they glue to `f : T ⟶ Q` in the fppf sheaf of points of `Q`, and
`f^* l = ξ` by separatedness of `F` for the same covering. -/
theorem exists_map_eq_of_fppfQuotient (hF : Presieve.IsSheaf (Scheme.fppfTopology.over S) F)
    (G : Subfunctor ((locallyNoetherianOverInclusion S).op ⋙ F)) (q : Z ⟶ Q)
    (z : F.obj (op Z.obj))
    (h₁ : ∀ ⦃T : LocallyNoetherianOver S⦄ (a b : T ⟶ Z), F.map a.hom.op z = F.map b.hom.op z →
      a ≫ q = b ≫ q)
    (h₃ : ∀ ⦃T : LocallyNoetherianOver S⦄ (ξ : F.obj (op T.obj)), ξ ∈ G.obj (op T) →
      ∀ t : T.obj.left, ∃ (U : LocallyNoetherianOver S) (k : U ⟶ T) (a : U ⟶ Z),
        Flat k.hom.left ∧ LocallyOfFinitePresentation k.hom.left ∧ t ∈ Set.range k.hom.left ∧
          F.map a.hom.op z = F.map k.hom.op ξ)
    {l : F.obj (op Q.obj)} (hl : F.map q.hom.op l = z) {T : LocallyNoetherianOver S}
    (ξ : F.obj (op T.obj)) (hξ : ξ ∈ G.obj (op T)) :
    ∃ f : T ⟶ Q, F.map f.hom.op l = ξ := by
  choose U k a hflat hlfp hrange ha using h₃ ξ hξ
  have hcov := ofArrows_mem_fppfTopology_over (fun t => (U t).obj) (fun t => (k t).hom) hflat
    hlfp fun t => ⟨t, hrange t⟩
  have hQ := (GrothendieckTopology.Subcanonical.isSheaf_of_isRepresentable
    (J := Scheme.fppfTopology.over S) (yoneda.obj Q.obj)).isSheafFor _ hcov
  rw [Presieve.isSheafFor_arrows_iff] at hQ
  obtain ⟨f, hf, -⟩ := hQ (fun t => (a t).hom ≫ q.hom) fun t s Y gi gj hij => by
    have := hlfp s
    simpa using comp_eq_comp_of_map_eq_of_fppfQuotient q z h₁ (k t).hom (k s).hom (a t) (a s) ξ
      (ha t) (ha s) gi gj hij
  refine ⟨ObjectProperty.homMk f, (hF.isSheafFor _ hcov).isSeparatedFor.ext ?_⟩
  rintro _ _ ⟨t⟩
  have hft : (k t).hom ≫ f = (a t).hom ≫ q.hom := by simpa using hf t
  calc F.map (k t).hom.op (F.map f.op l) = F.map ((k t).hom ≫ f).op l := by
        rw [op_comp, Functor.map_comp_apply]
    _ = F.map ((a t).hom ≫ q.hom).op l := by rw [hft]
    _ = F.map (a t).hom.op z := by rw [op_comp, Functor.map_comp_apply, hl]
    _ = F.map (k t).hom.op ξ := ha t

/-- **Kleiman's Lemma 4.9, fppf form, on locally Noetherian test schemes**
(arXiv:math/0504020v1, Lemma 4.9, p. 30, with the quotient `q : Z ⟶ Q` given): under (h₁),
(h₂), (h₃), `z ∈ G(Z)` and descent of `G` along `q`, the scheme `Q` represents `G` on locally
Noetherian test schemes, through `f ↦ f^* λ` with `λ = fppfQuotientSection hF q z h₂`. -/
def representableByOfFppfQuotient (hF : Presieve.IsSheaf (Scheme.fppfTopology.over S) F)
    (G : Subfunctor ((locallyNoetherianOverInclusion S).op ⋙ F)) (q : Z ⟶ Q) [Flat q.hom.left]
    [Surjective q.hom.left] [LocallyOfFinitePresentation q.hom.left] (z : F.obj (op Z.obj))
    (hz : z ∈ G.obj (op Z))
    (hG : ∀ ξ : F.obj (op Q.obj), F.map q.hom.op ξ ∈ G.obj (op Z) → ξ ∈ G.obj (op Q))
    (h₁ : ∀ ⦃T : LocallyNoetherianOver S⦄ (a b : T ⟶ Z), F.map a.hom.op z = F.map b.hom.op z →
      a ≫ q = b ≫ q)
    (h₂ : ∀ ⦃T : LocallyNoetherianOver S⦄ (a b : T ⟶ Z), a ≫ q = b ≫ q →
      F.map a.hom.op z = F.map b.hom.op z)
    (h₃ : ∀ ⦃T : LocallyNoetherianOver S⦄ (ξ : F.obj (op T.obj)), ξ ∈ G.obj (op T) →
      ∀ t : T.obj.left, ∃ (U : LocallyNoetherianOver S) (k : U ⟶ T) (a : U ⟶ Z),
        Flat k.hom.left ∧ LocallyOfFinitePresentation k.hom.left ∧ t ∈ Set.range k.hom.left ∧
          F.map a.hom.op z = F.map k.hom.op ξ) :
    G.toFunctor.RepresentableBy Q where
  homEquiv {T} := Equiv.ofBijective
    (fun f => ⟨F.map f.hom.op (fppfQuotientSection hF q z h₂),
      G.map f.op (fppfQuotientSection_mem hF G q z h₂ hz hG)⟩)
    ⟨fun f₁ f₂ h => hom_ext_of_fppfQuotient q z h₁ (map_fppfQuotientSection hF q z h₂)
        (congrArg Subtype.val h),
      fun ξ => by
        obtain ⟨f, hf⟩ := exists_map_eq_of_fppfQuotient hF G q z h₁ h₃
          (map_fppfQuotientSection hF q z h₂) ξ.1 ξ.2
        exact ⟨f, Subtype.ext hf⟩⟩
  homEquiv_comp {T T'} f g := by
    apply Subtype.ext
    change F.map (f ≫ g).hom.op (fppfQuotientSection hF q z h₂) =
      F.map f.hom.op (F.map g.hom.op (fppfQuotientSection hF q z h₂))
    rw [ObjectProperty.FullSubcategory.comp_hom, op_comp, Functor.map_comp_apply]

/-- The bijection of `representableByOfFppfQuotient` is `f ↦ f^* λ`. -/
theorem representableByOfFppfQuotient_homEquiv_coe
    (hF : Presieve.IsSheaf (Scheme.fppfTopology.over S) F)
    (G : Subfunctor ((locallyNoetherianOverInclusion S).op ⋙ F)) (q : Z ⟶ Q) [Flat q.hom.left]
    [Surjective q.hom.left] [LocallyOfFinitePresentation q.hom.left] (z : F.obj (op Z.obj))
    (hz : z ∈ G.obj (op Z))
    (hG : ∀ ξ : F.obj (op Q.obj), F.map q.hom.op ξ ∈ G.obj (op Z) → ξ ∈ G.obj (op Q))
    (h₁ : ∀ ⦃T : LocallyNoetherianOver S⦄ (a b : T ⟶ Z), F.map a.hom.op z = F.map b.hom.op z →
      a ≫ q = b ≫ q)
    (h₂ : ∀ ⦃T : LocallyNoetherianOver S⦄ (a b : T ⟶ Z), a ≫ q = b ≫ q →
      F.map a.hom.op z = F.map b.hom.op z)
    (h₃ : ∀ ⦃T : LocallyNoetherianOver S⦄ (ξ : F.obj (op T.obj)), ξ ∈ G.obj (op T) →
      ∀ t : T.obj.left, ∃ (U : LocallyNoetherianOver S) (k : U ⟶ T) (a : U ⟶ Z),
        Flat k.hom.left ∧ LocallyOfFinitePresentation k.hom.left ∧ t ∈ Set.range k.hom.left ∧
          F.map a.hom.op z = F.map k.hom.op ξ)
    {T : LocallyNoetherianOver S} (f : T ⟶ Q) :
    ((representableByOfFppfQuotient hF G q z hz hG h₁ h₂ h₃).homEquiv f).1 =
      F.map f.hom.op (fppfQuotientSection hF q z h₂) :=
  rfl

end AlgebraicGeometry.Scheme
