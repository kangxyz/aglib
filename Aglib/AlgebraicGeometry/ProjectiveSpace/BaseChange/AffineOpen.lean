/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.ProjectiveSpace.BaseChange.Cartesian
public import Aglib.AlgebraicGeometry.ProjectiveSpace.Structure
public import Aglib.AlgebraicGeometry.Modules.Flat.Relative.AffineSections

/-!
# Projective space over a scheme: affine opens of the base and base change of the base

Let `s : S ⟶ Spec A` and `X_S = P^n_A ×_{Spec A} S` (`pullback (toSpec A ι) s`), with second
projection `X_S ⟶ S`.

* **Affine opens.** For an affine open `U` of `S`, `affineBaseRingHom s hU : A →+* Γ(S, U)` has
  `Spec` equal to `hU.fromSpec ≫ s` (`specMap_affineBaseRingHom`), and
  `affineBaseMap ι s hU : P^n_{Γ(S, U)} ⟶ X_S` exhibits `P^n_{Γ(S, U)}` as the base change of
  `X_S ⟶ S` along `hU.fromSpec` (`isPullback_affineBaseMap`). For affine opens `W ≤ U` the family
  over `W` is the base change of that over `U` along the restriction `Γ(S, U) → Γ(S, W)`
  (`affineBaseRingHom_restrict`, `affineBaseMap_restrict`).
* **Base change of the base.** For `g : T ⟶ S`, `pullbackBaseChange ι s g` is the morphism
  `P^n_A ×_{Spec A} T ⟶ X_S` (for `g ≫ s : T ⟶ Spec A`), the base change of `X_S ⟶ S` along `g`
  (`isPullback_pullbackBaseChange`). Over affine opens `V ≤ g ⁻¹ U` it is the base change along
  `g.appLE U V : Γ(S, U) → Γ(T, V)` (`affineBaseRingHom_comp`, `affineBaseMap_pullbackBaseChange`).
* `X_S` is locally Noetherian when `S` is and the coordinates are finite
  (`isLocallyNoetherian_pullback_toSpec`).

These are the restrictions used by the flattening stratification over a locally Noetherian base
(`FlatteningStratification/AffineBase`, `FlatteningStratification/Global`).
-/

@[expose] public section

noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry.ProjectiveSpace

variable {A : Type u} [CommRing A] (ι : Type u) {S : Scheme.{u}} (s : S ⟶ Spec (CommRingCat.of A))

/-- The ring map `A → Γ(S, U)` of an affine open `U` of a scheme `S` over `Spec A`. -/
def affineBaseRingHom {U : S.Opens} (_hU : IsAffineOpen U) : A →+* Γ(S, U) :=
  ((Scheme.ΓSpecIso (CommRingCat.of A)).inv ≫ s.appLE ⊤ U (by simp)).hom

theorem specMap_affineBaseRingHom {U : S.Opens} (hU : IsAffineOpen U) :
    Spec.map (CommRingCat.ofHom (affineBaseRingHom s hU)) = hU.fromSpec ≫ s :=
  Scheme.Modules.SpecMap_affineOpen_baseRingHom s hU

/-- The ring maps of two affine opens `W ≤ U` differ by the restriction `Γ(S, U) → Γ(S, W)`. -/
theorem affineBaseRingHom_restrict {U W : S.Opens} (hU : IsAffineOpen U) (hW : IsAffineOpen W)
    (hWU : W ≤ U) :
    (S.presheaf.map (homOfLE hWU).op).hom.comp (affineBaseRingHom s hU) =
      affineBaseRingHom s hW := by
  rw [affineBaseRingHom, affineBaseRingHom, ← CommRingCat.hom_comp, Category.assoc,
    Scheme.Hom.appLE_map]

/-- Along `g : T ⟶ S` and affine opens `V ≤ g ⁻¹ U`, the ring map of `V` over `g ≫ s` is that of
`U` followed by `g.appLE U V`. -/
theorem affineBaseRingHom_comp {T : Scheme.{u}} (g : T ⟶ S) {U : S.Opens} (hU : IsAffineOpen U)
    {V : T.Opens} (hV : IsAffineOpen V) (hVU : V ≤ g ⁻¹ᵁ U) :
    (g.appLE U V hVU).hom.comp (affineBaseRingHom s hU) = affineBaseRingHom (g ≫ s) hV := by
  rw [affineBaseRingHom, affineBaseRingHom, ← CommRingCat.hom_comp, Category.assoc,
    Scheme.Hom.appLE_comp_appLE]

/-- The restriction of `X_S = P^n_A ×_{Spec A} S` over an affine open `U`: the morphism
`P^n_{Γ(S, U)} ⟶ X_S` over `hU.fromSpec`. -/
def affineBaseMap {U : S.Opens} (hU : IsAffineOpen U) :
    ProjectiveSpace Γ(S, U) ι ⟶ pullback (toSpec A ι) s :=
  pullback.lift (map (affineBaseRingHom s hU) ι) (toSpec Γ(S, U) ι ≫ hU.fromSpec) (by
    rw [map_toSpec, specMap_affineBaseRingHom, Category.assoc])

@[reassoc (attr := simp)]
theorem affineBaseMap_fst {U : S.Opens} (hU : IsAffineOpen U) :
    affineBaseMap ι s hU ≫ pullback.fst (toSpec A ι) s = map (affineBaseRingHom s hU) ι :=
  pullback.lift_fst _ _ _

@[reassoc (attr := simp)]
theorem affineBaseMap_snd {U : S.Opens} (hU : IsAffineOpen U) :
    affineBaseMap ι s hU ≫ pullback.snd (toSpec A ι) s = toSpec Γ(S, U) ι ≫ hU.fromSpec :=
  pullback.lift_snd _ _ _

/-- `P^n_{Γ(S, U)}` is the base change of `X_S ⟶ S` along `hU.fromSpec`. -/
theorem isPullback_affineBaseMap {U : S.Opens} (hU : IsAffineOpen U) :
    IsPullback (affineBaseMap ι s hU) (toSpec Γ(S, U) ι) (pullback.snd (toSpec A ι) s)
      hU.fromSpec := by
  have h := isPullback_map (affineBaseRingHom s hU) ι
  rw [specMap_affineBaseRingHom, ← affineBaseMap_fst] at h
  exact IsPullback.of_right h (affineBaseMap_snd ι s hU) (IsPullback.of_hasPullback (toSpec A ι) s)

/-- For affine opens `W ≤ U`, the family over `W` is the base change of the family over `U`
along the restriction `Γ(S, U) → Γ(S, W)`. -/
theorem affineBaseMap_restrict {U W : S.Opens} (hU : IsAffineOpen U) (hW : IsAffineOpen W)
    (hWU : W ≤ U) :
    affineBaseMap ι s hW = map (S.presheaf.map (homOfLE hWU).op).hom ι ≫ affineBaseMap ι s hU := by
  apply pullback.hom_ext
  · rw [affineBaseMap_fst, Category.assoc, affineBaseMap_fst, ← map_comp,
      affineBaseRingHom_restrict s hU hW hWU]
  · rw [affineBaseMap_snd, Category.assoc, affineBaseMap_snd, map_toSpec_assoc,
      CommRingCat.ofHom_hom, IsAffineOpen.map_fromSpec]

/-- The base change of `X_S` along `g : T ⟶ S`: the morphism `P^n_A ×_{Spec A} T ⟶ X_S`, for the
structure morphism `g ≫ s` of `T`. -/
def pullbackBaseChange {T : Scheme.{u}} (g : T ⟶ S) :
    pullback (toSpec A ι) (g ≫ s) ⟶ pullback (toSpec A ι) s :=
  pullback.lift (pullback.fst _ _) (pullback.snd _ _ ≫ g) (by
    rw [pullback.condition, Category.assoc])

@[reassoc (attr := simp)]
theorem pullbackBaseChange_fst {T : Scheme.{u}} (g : T ⟶ S) :
    pullbackBaseChange ι s g ≫ pullback.fst (toSpec A ι) s = pullback.fst (toSpec A ι) (g ≫ s) :=
  pullback.lift_fst _ _ _

@[reassoc (attr := simp)]
theorem pullbackBaseChange_snd {T : Scheme.{u}} (g : T ⟶ S) :
    pullbackBaseChange ι s g ≫ pullback.snd (toSpec A ι) s =
      pullback.snd (toSpec A ι) (g ≫ s) ≫ g :=
  pullback.lift_snd _ _ _

/-- `P^n_A ×_{Spec A} T` is the base change of `X_S ⟶ S` along `g : T ⟶ S`. -/
theorem isPullback_pullbackBaseChange {T : Scheme.{u}} (g : T ⟶ S) :
    IsPullback (pullbackBaseChange ι s g) (pullback.snd (toSpec A ι) (g ≫ s))
      (pullback.snd (toSpec A ι) s) g := by
  have h := IsPullback.of_hasPullback (toSpec A ι) (g ≫ s)
  rw [← pullbackBaseChange_fst] at h
  exact IsPullback.of_right h (pullbackBaseChange_snd ι s g)
    (IsPullback.of_hasPullback (toSpec A ι) s)

/-- **Base change of the base over affine opens**: for `g : T ⟶ S` and affine opens
`V ≤ g ⁻¹ U`, the restriction of `P^n_A ×_{Spec A} T` over `V`, followed by the base change
`pullbackBaseChange ι s g`, is the base change of the restriction of `X_S` over `U` along
`g.appLE U V`. -/
theorem affineBaseMap_pullbackBaseChange {T : Scheme.{u}} (g : T ⟶ S) {U : S.Opens}
    (hU : IsAffineOpen U) {V : T.Opens} (hV : IsAffineOpen V) (hVU : V ≤ g ⁻¹ᵁ U) :
    affineBaseMap ι (g ≫ s) hV ≫ pullbackBaseChange ι s g =
      map (g.appLE U V hVU).hom ι ≫ affineBaseMap ι s hU := by
  apply pullback.hom_ext
  · rw [Category.assoc, pullbackBaseChange_fst, affineBaseMap_fst, Category.assoc,
      affineBaseMap_fst, ← map_comp, affineBaseRingHom_comp s g hU hV hVU]
  · rw [Category.assoc, pullbackBaseChange_snd, affineBaseMap_snd_assoc, Category.assoc,
      affineBaseMap_snd, map_toSpec_assoc, CommRingCat.ofHom_hom,
      IsAffineOpen.SpecMap_appLE_fromSpec g hU hV hVU]

/-- `X_S = P^n_A ×_{Spec A} S` is locally Noetherian when `S` is and the coordinates are
finite. -/
instance isLocallyNoetherian_pullback_toSpec [Finite ι] [IsLocallyNoetherian S] :
    IsLocallyNoetherian (pullback (toSpec A ι) s) :=
  LocallyOfFiniteType.isLocallyNoetherian (pullback.snd (toSpec A ι) s)

end AlgebraicGeometry.ProjectiveSpace
