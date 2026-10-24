/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Picard.Strata.Relation.Representability
public import Aglib.AlgebraicGeometry.Properties.Noetherian.EquivalenceRelation

/-!
# `R = Z ×_P Z`: proper flat projections, a closed equivalence relation on `Z`

In the setting of `Picard/Strata/Relation/Representability` (a Noetherian ring `A`, `i : X ⟶ P^N_A`
a closed immersion with `ι ≃ Fin (N + 1)`, `πX = i ≫ toSpec A ι` flat and geometrically integral,
the fine stratum `C = fineCondition i N e φ₀ ψ 0 (k + 1)`, a representation `E` of
`Div^{ψ − φ₀}_X` by `D`, `Z = C.abelPreimageOver E`), let `R = Gr(p_{Z*}𝒪(W_Z), k)` with
projections `pr₁, pr₂ : R ⟶ Z` and `j = (pr₁, pr₂) : R ⟶ Z ×_S Z`. This file proves the
properties of `R` used in Kleiman, *The Picard scheme*, arXiv:math/0504020v1, p. 30: in the proof
of Thm 4.8 ("the product `Z ×_{P_0^{φ0}} Z` is a scheme and ... the first projection is smooth and
projective") and in the proof of Lemma 4.9: its first paragraph ("the first projection `R → Z`
is proper, and factors naturally through a map `h : R → Z ×_S Z`. Hence `h` is proper. But `h` is a
monomorphism; that is, `h` is injective on `T`-points. Therefore, `h` is a closed embedding by
[EGA IV₃, 8.11.5]") and its second ("the subset `R(T) ⊂ Z(T) ×_{S(T)} Z(T)` is the graph of an
equivalence relation"):

* `Strata.isNoetherian_abelRelationOver`: `R` is Noetherian when `Z` is.
* `Strata.abelRelationSwap`: the automorphism of `R` exchanging the two projections, from the
  symmetry of `Z ×_P Z` and the representability of `R`; it is an involution.
* proper and flat projections (instances on `(abelRelationFst e k E).hom.left` and
  `(abelRelationSnd e k E).hom.left`): `pr₁` is the structure map of the Grassmannian bundle,
  proper and flat (`Grassmannian/LocallyFree/Proper`), and `pr₂ = swap ≫ pr₁`. Kleiman's
  smoothness and projectivity are not used.
* `Strata.abelRelation_left_injective`: `R(T) ⟶ Z(T) × Z(T)` is injective on locally Noetherian
  points (of schemes, not only over `S`).
* `FiberCondition.isSeparated_abelPreimageOver_hom`,
  `FiberCondition.locallyOfFiniteType_abelPreimageOver_hom`,
  `FiberCondition.isLocallyNoetherian_pullback_abelPreimageOver_hom`: for any fibre condition,
  `Z ⟶ S` is separated, respectively locally of finite type with `Z ×_S Z` locally Noetherian,
  when `D ⟶ S` is.
* `Strata.isClosedImmersion_abelRelationι`: if `D ⟶ S` is separated and locally of finite type
  (for example H-quasi-projective), `j` is a closed immersion: it is proper (`pr₁` is proper and
  `Z ×_S Z ⟶ Z` is separated) and injective on locally Noetherian points
  (`isClosedImmersion_of_isProper_of_locallyNoetherian_yoneda_map_injective`; EGA IV₃ 8.11.5 in
  Kleiman).
* `Strata.equivalence_pointsRelation_abelRelation`, `Strata.isEquivalenceRelation_abelRelation`:
  `pr₁, pr₂` is an equivalence relation, on locally Noetherian points and internally
  (`isEquivalenceRelation_iff_locallyNoetherian_points_of_mono`).

* `Strata.comp_eq_comp_of_fppfPicardSheaf_map_eq_of_abelRelationFst_comp_eq_abelRelationSnd_comp`:
  for `q : Z ⟶ Q` with `pr₁ ≫ q = pr₂ ≫ q`, points of `Z` with the same class have the same image
  in `Q`; with
  `fppfPicardSheaf_map_abelRelationFst_eq_map_abelRelationSnd` these give the two pair conditions
  of `Scheme.representableByOfFppfQuotient` for `z = α_Z` once `R ≅ Z ×_Q Z`.

The projections, proper and flat, and the equivalence relation on locally Noetherian points are
the hypotheses of the quotient theorem of Nitsure, *Construction of Hilbert and Quot schemes*,
arXiv:math/0504590v1, Thm 6.8, p. 33 (for `Z ⟶ S` quasi-projective), tested on locally Noetherian
points.
-/

@[expose] public section

noncomputable section

open CategoryTheory Limits Opposite

universe u

namespace AlgebraicGeometry.Scheme.RelativePicard.FiberCondition

open ProjectiveSpace

variable {ι : Type u} {A : Type u} [CommRing A] {X : Scheme.{u}}
  {πX : X ⟶ Spec (CommRingCat.of A)} {i : X ⟶ ProjectiveSpace A ι} {hi : i ≫ toSpec A ι = πX}
  [IsPreimmersion i] {θ : Polynomial ℚ} (C : FiberCondition πX)
  {D : Scheme.LocallyNoetherianOver (Spec (CommRingCat.of A))}
  (E : (locallyNoetherianRelativeDivisorFunctor i hi θ).RepresentableBy D)

/-- `Z ⟶ S` is separated when `D ⟶ S` is: `Z ⟶ D` is an open immersion. -/
instance isSeparated_abelPreimageOver_hom [IsSeparated D.obj.hom] :
    IsSeparated (C.abelPreimageOver E).obj.hom := by
  rw [abelPreimageOver_hom]
  infer_instance

/-- `Z ⟶ S` is locally of finite type when `D ⟶ S` is. -/
instance locallyOfFiniteType_abelPreimageOver_hom [LocallyOfFiniteType D.obj.hom] :
    LocallyOfFiniteType (C.abelPreimageOver E).obj.hom := by
  rw [abelPreimageOver_hom]
  infer_instance

/-- `Z ×_S Z` is locally Noetherian when `D ⟶ S` is locally of finite type. -/
instance isLocallyNoetherian_pullback_abelPreimageOver_hom [LocallyOfFiniteType D.obj.hom] :
    IsLocallyNoetherian (pullback (C.abelPreimageOver E).obj.hom (C.abelPreimageOver E).obj.hom) :=
  LocallyOfFiniteType.isLocallyNoetherian (pullback.fst _ _)

end AlgebraicGeometry.Scheme.RelativePicard.FiberCondition

namespace AlgebraicGeometry.Scheme.RelativePicard.Strata

open Modules.Invertible ProjectiveSpace LinearSystem Grassmannian

variable {A : Type u} [CommRing A] {ι : Type u} {X : Scheme.{u}}
  {i : X ⟶ ProjectiveSpace A ι} [IsClosedImmersion i] [Flat (i ≫ toSpec A ι)]
  {N : ℕ} (e : ι ≃ Fin (N + 1)) {φ₀ ψ : Polynomial ℚ} (k : ℕ)
  {D : Scheme.LocallyNoetherianOver (Spec (CommRingCat.of A))}
  (E : (locallyNoetherianRelativeDivisorFunctor i rfl (ψ - φ₀)).RepresentableBy D)

/-- The first projection of `R` is proper. -/
instance isProper_abelRelationFst_hom_left : IsProper (abelRelationFst e k E).hom.left :=
  isProper_abelRelationBundle_hom e k E

/-- The first projection of `R` is flat. -/
instance flat_abelRelationFst_hom_left : Flat (abelRelationFst e k E).hom.left :=
  flat_abelRelationBundle_hom e k E

/-- The first projection of `R` is locally of finite type. -/
instance locallyOfFiniteType_abelRelationFst_hom_left :
    LocallyOfFiniteType (abelRelationFst e k E).hom.left :=
  locallyOfFiniteType_abelRelationBundle_hom e k E

/-- **`R` is Noetherian when `Z` is**: `R ⟶ Z` is proper, hence quasi-compact, and locally of
finite type. For example `Z` is Noetherian when `A` is Noetherian and `D` is H-quasi-projective
(`FiberCondition.isNoetherian_abelPreimageOver`). -/
instance isNoetherian_abelRelationOver
    [IsNoetherian ((fineCondition i N e φ₀ ψ 0 (k + 1)).abelPreimageOver E).obj.left] :
    IsNoetherian (abelRelationOver e k E).obj.left :=
  have : CompactSpace (abelRelationOver e k E).obj.left :=
    @QuasiCompact.compactSpace_of_compactSpace _ _ (abelRelationBundle e k E).hom
      (quasiCompact_grassmannianBundle_hom _ k (k + 1) _) inferInstance
  { }

variable [GeometricallyIntegral (i ≫ toSpec A ι)] [IsNoetherianRing A]

/-- **The symmetry of `R`**: the point of `R` over `R` with projections `(pr₂, pr₁)`, which
exists because `pr₂^* α_Z = pr₁^* α_Z` and `R` represents `Z ×_P Z`. -/
def abelRelationSwap : abelRelationOver e k E ⟶ abelRelationOver e k E :=
  (abelRelationRepresentableBy e k E).homEquiv.symm
    ⟨(abelRelationSnd e k E, abelRelationFst e k E),
      (fppfPicardSheaf_map_abelRelationFst_eq_map_abelRelationSnd e k E).symm⟩

@[reassoc (attr := simp)]
theorem abelRelationSwap_fst :
    abelRelationSwap e k E ≫ abelRelationFst e k E = abelRelationSnd e k E :=
  congrArg (fun x => x.1.1) ((abelRelationRepresentableBy e k E).homEquiv.apply_symm_apply
    ⟨(abelRelationSnd e k E, abelRelationFst e k E),
      (fppfPicardSheaf_map_abelRelationFst_eq_map_abelRelationSnd e k E).symm⟩)

@[reassoc (attr := simp)]
theorem abelRelationSwap_snd :
    abelRelationSwap e k E ≫ abelRelationSnd e k E = abelRelationFst e k E :=
  congrArg (fun x => x.1.2) ((abelRelationRepresentableBy e k E).homEquiv.apply_symm_apply
    ⟨(abelRelationSnd e k E, abelRelationFst e k E),
      (fppfPicardSheaf_map_abelRelationFst_eq_map_abelRelationSnd e k E).symm⟩)

/-- The symmetry of `R` is an involution. -/
@[reassoc (attr := simp)]
theorem abelRelationSwap_swap : abelRelationSwap e k E ≫ abelRelationSwap e k E = 𝟙 _ :=
  abelRelation_hom_ext e k E
    (by rw [Category.assoc, abelRelationSwap_fst, abelRelationSwap_snd, Category.id_comp])
    (by rw [Category.assoc, abelRelationSwap_snd, abelRelationSwap_fst, Category.id_comp])

instance isIso_abelRelationSwap_hom_left : IsIso (abelRelationSwap e k E).hom.left :=
  ⟨⟨(abelRelationSwap e k E).hom.left,
    congrArg (fun f => f.hom.left) (abelRelationSwap_swap e k E),
    congrArg (fun f => f.hom.left) (abelRelationSwap_swap e k E)⟩⟩

/-- `pr₂ = swap ≫ pr₁` on the underlying schemes. -/
theorem abelRelationSnd_hom_left_eq :
    (abelRelationSnd e k E).hom.left =
      (abelRelationSwap e k E).hom.left ≫ (abelRelationFst e k E).hom.left :=
  (congrArg (fun f => f.hom.left) (abelRelationSwap_fst e k E)).symm

/-- **The second projection of `R` is proper**: it is the symmetry of `R` followed by the first
projection. -/
instance isProper_abelRelationSnd_hom_left : IsProper (abelRelationSnd e k E).hom.left := by
  rw [abelRelationSnd_hom_left_eq]
  infer_instance

/-- **The second projection of `R` is flat.** -/
instance flat_abelRelationSnd_hom_left : Flat (abelRelationSnd e k E).hom.left := by
  rw [abelRelationSnd_hom_left_eq]
  infer_instance

omit [IsNoetherianRing A] in
/-- **`R(T) ⟶ Z(T) × Z(T)` is injective on locally Noetherian points** of schemes: two morphisms
`r, r' : T ⟶ R` from a locally Noetherian scheme with the same composites with both projections
are equal (both are points over `S` through `r ≫ (R ⟶ S)`). -/
theorem abelRelation_left_injective (T : Scheme.{u}) [IsLocallyNoetherian T]
    (r r' : T ⟶ (abelRelationOver e k E).obj.left)
    (h₁ : r ≫ (abelRelationFst e k E).hom.left = r' ≫ (abelRelationFst e k E).hom.left)
    (h₂ : r ≫ (abelRelationSnd e k E).hom.left = r' ≫ (abelRelationSnd e k E).hom.left) :
    r = r' := by
  let T' : Scheme.LocallyNoetherianOver (Spec (CommRingCat.of A)) :=
    ⟨Over.mk (r ≫ (abelRelationOver e k E).obj.hom), inferInstanceAs (IsLocallyNoetherian T)⟩
  have hw : r' ≫ (abelRelationOver e k E).obj.hom = r ≫ (abelRelationOver e k E).obj.hom := by
    rw [← Over.w (abelRelationFst e k E).hom, ← Category.assoc, ← h₁, Category.assoc]
  let c : T' ⟶ abelRelationOver e k E := ObjectProperty.homMk (Over.homMk r rfl)
  let c' : T' ⟶ abelRelationOver e k E := ObjectProperty.homMk (Over.homMk r' hw)
  have h := abelRelation_hom_ext e k E (c := c) (c' := c')
    (ObjectProperty.hom_ext _ (Over.OverMorphism.ext h₁))
    (ObjectProperty.hom_ext _ (Over.OverMorphism.ext h₂))
  exact congrArg (fun f => f.hom.left) h

/-- **`pr₁, pr₂` is an equivalence relation on locally Noetherian points over `S`**: for `T`
locally Noetherian over `S`, the pairs `(r ≫ pr₁, r ≫ pr₂)` are the pairs of points of `Z` with
the same class in `Pic_{X/S,(fppf)}(T)`. -/
theorem equivalence_pointsRelation_abelRelation_over
    (T : Scheme.LocallyNoetherianOver (Spec (CommRingCat.of A))) :
    _root_.Equivalence (pointsRelation (abelRelationFst e k E).hom (abelRelationSnd e k E).hom
      T.obj) := by
  have key : ∀ a b : T.obj ⟶ ((fineCondition i N e φ₀ ψ 0 (k + 1)).abelPreimageOver E).obj,
      pointsRelation (abelRelationFst e k E).hom (abelRelationSnd e k E).hom T.obj a b ↔
        (fppfPicardSheaf (i ≫ toSpec A ι)).obj.map a.op
            ((fineCondition i N e φ₀ ψ 0 (k + 1)).abelPreimageFppfAbelClass E) =
          (fppfPicardSheaf (i ≫ toSpec A ι)).obj.map b.op
            ((fineCondition i N e φ₀ ψ 0 (k + 1)).abelPreimageFppfAbelClass E) := by
    intro a b
    refine Iff.trans ?_ (exists_comp_abelRelationFst_and_comp_abelRelationSnd_iff e k E
      (ObjectProperty.homMk a) (ObjectProperty.homMk b))
    constructor
    · rintro ⟨r, h₁, h₂⟩
      exact ⟨ObjectProperty.homMk r, ObjectProperty.hom_ext _ h₁, ObjectProperty.hom_ext _ h₂⟩
    · rintro ⟨c, h₁, h₂⟩
      exact ⟨c.hom, congrArg (fun f => f.hom) h₁, congrArg (fun f => f.hom) h₂⟩
  refine ⟨fun a => (key a a).mpr rfl, fun h => (key _ _).mpr ((key _ _).mp h).symm,
    fun h h' => (key _ _).mpr (((key _ _).mp h).trans ((key _ _).mp h'))⟩

/-- **`pr₁, pr₂` is an equivalence relation on locally Noetherian points** of schemes: for every
locally Noetherian scheme `T`, the image of `R(T)` in `Z(T) × Z(T)` is an equivalence relation. -/
theorem equivalence_pointsRelation_abelRelation (T : Scheme.{u}) [IsLocallyNoetherian T] :
    _root_.Equivalence (pointsRelation (abelRelationFst e k E).hom.left
      (abelRelationSnd e k E).hom.left T) :=
  (LocallyNoetherianOver.equivalence_pointsRelation_iff (abelRelationFst e k E).hom
    (abelRelationSnd e k E).hom).mp (equivalence_pointsRelation_abelRelation_over e k E) T

/-- **Points of `Z` with the same class have the same image in a quotient by `R`**: for
`q : Z ⟶ Q` over `S` with `pr₁ ≫ q = pr₂ ≫ q` (for example the quotient of `Z` by the equivalence
relation `R`), `a^* α_Z = b^* α_Z` implies `a ≫ q = b ≫ q`. This is hypothesis (h₁) of
`Scheme.representableByOfFppfQuotient` for `z = α_Z`. -/
theorem comp_eq_comp_of_fppfPicardSheaf_map_eq_of_abelRelationFst_comp_eq_abelRelationSnd_comp
    {Q : Scheme.LocallyNoetherianOver (Spec (CommRingCat.of A))}
    (q : (fineCondition i N e φ₀ ψ 0 (k + 1)).abelPreimageOver E ⟶ Q)
    (hq : (abelRelationFst e k E).hom.left ≫ q.hom.left =
      (abelRelationSnd e k E).hom.left ≫ q.hom.left)
    {T : Scheme.LocallyNoetherianOver (Spec (CommRingCat.of A))}
    (a b : T ⟶ (fineCondition i N e φ₀ ψ 0 (k + 1)).abelPreimageOver E)
    (hab : (fppfPicardSheaf (i ≫ toSpec A ι)).obj.map a.hom.op
        ((fineCondition i N e φ₀ ψ 0 (k + 1)).abelPreimageFppfAbelClass E) =
      (fppfPicardSheaf (i ≫ toSpec A ι)).obj.map b.hom.op
        ((fineCondition i N e φ₀ ψ 0 (k + 1)).abelPreimageFppfAbelClass E)) :
    a ≫ q = b ≫ q := by
  obtain ⟨c, rfl, rfl⟩ := exists_comp_abelRelationFst_and_comp_abelRelationSnd_of_eq e k E hab
  refine ObjectProperty.hom_ext _ (Over.OverMorphism.ext ?_)
  change c.hom.left ≫ (abelRelationFst e k E).hom.left ≫ q.hom.left =
    c.hom.left ≫ (abelRelationSnd e k E).hom.left ≫ q.hom.left
  rw [hq]

variable [IsSeparated D.obj.hom] [LocallyOfFiniteType D.obj.hom]

/-- **`R ⟶ Z ×_S Z` is proper**: `pr₁` is proper and `Z ×_S Z ⟶ Z` is separated. -/
instance isProper_abelRelationι : IsProper (abelRelationι e k E) := by
  have : IsProper (abelRelationι e k E ≫ pullback.fst _ _) := by
    rw [abelRelationι_fst]
    infer_instance
  exact IsProper.of_comp (abelRelationι e k E) (pullback.fst _ _)

/-- **`R ⟶ Z ×_S Z` is a closed immersion** (Kleiman, arXiv:math/0504020v1, proof of Lemma 4.9,
p. 30, through EGA IV₃ 8.11.5): it is proper and injective on locally Noetherian points
(`isClosedImmersion_of_isProper_of_locallyNoetherian_yoneda_map_injective`). -/
instance isClosedImmersion_abelRelationι : IsClosedImmersion (abelRelationι e k E) :=
  isClosedImmersion_of_isProper_of_locallyNoetherian_yoneda_map_injective _ fun T _ r r' h =>
    abelRelation_left_injective e k E T r r'
      (by simpa using congrArg (· ≫ pullback.fst _ _) h)
      (by simpa using congrArg (· ≫ pullback.snd _ _) h)

/-- **`pr₁, pr₂ : R ⟶ Z` is an equivalence relation** (Mathlib's internal
`CategoryTheory.IsEquivalenceRelation`), tested on locally Noetherian points through the
monomorphism `R ⟶ Z ×_S Z` (`isEquivalenceRelation_iff_locallyNoetherian_points_of_mono`). -/
theorem isEquivalenceRelation_abelRelation :
    IsEquivalenceRelation (abelRelationFst e k E).hom.left (abelRelationSnd e k E).hom.left := by
  have : LocallyOfFiniteType (abelRelationι e k E ≫ pullback.fst _ _) := by
    rw [abelRelationι_fst]
    infer_instance
  have h := (isEquivalenceRelation_iff_locallyNoetherian_points_of_mono
    ((fineCondition i N e φ₀ ψ 0 (k + 1)).abelPreimageOver E).obj.hom
      (abelRelationι e k E)).mpr (by
        rw [abelRelationι_fst, abelRelationι_snd]
        exact fun T _ => equivalence_pointsRelation_abelRelation e k E T)
  rwa [abelRelationι_fst, abelRelationι_snd] at h

end AlgebraicGeometry.Scheme.RelativePicard.Strata
