/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EffectiveCartierDivisor.Relative.Basic
public import Aglib.AlgebraicGeometry.HilbertScheme.Immersed.Functor

/-!
# The functor of relative effective Cartier divisors with a fixed Hilbert polynomial

Let `A` be a ring, `ι` a coordinate type, `X` a scheme with `πX : X ⟶ Spec A`, and
`i : X ⟶ P^n_A = ProjectiveSpace A ι` a preimmersion over `Spec A` (`hi : i ≫ toSpec A ι = πX`),
for example a closed immersion. For a scheme `T` over `Spec A` write `X_T = X ×_{Spec A} T`
(`pullback πX T.hom`, the scheme `RelativePicard.familyScheme πX` at `T`) and
`i_T = immersionBaseChange i hi T.hom : X_T ⟶ P^n_A ×_{Spec A} T`.

* `IsRelativeDivisorFamily i hi θ g D`: a closed subscheme `D ⊆ X_T` is a relative effective
  Cartier divisor of `X_T` over `T` (`Scheme.Hom.IsRelativeEffectiveCartier`: an effective Cartier
  divisor flat over `T`; Kleiman, *The Picard scheme*, arXiv:math/0504020v1, Def. 3.3, p. 22) and
  a point of the Hilbert functor of `X` with polynomial `θ` (`IsImmersedHilbertFamily`: `D` is
  proper over `T` and its image `D.map i_T` in `P^n_A ×_{Spec A} T` is flat over `T` with all
  fibre Hilbert polynomials `θ`). For a closed immersion `i` and finitely many coordinates the
  properness is automatic (`isRelativeDivisorFamily_iff_of_isClosedImmersion`), and so is the
  flatness of the image: a relative effective Cartier divisor whose image has fibre Hilbert
  polynomial `θ` at every field point is a point
  (`IsRelativeDivisorFamily.of_isRelativeEffectiveCartier`).
* `relativeDivisorFunctor i hi θ`: the functor `T ↦ {D ⊆ X_T | IsRelativeDivisorFamily}` on all
  schemes over `Spec A`, acting by pullback along `pullback.map πX _ πX _ (𝟙 X) f (𝟙 _)` (the
  maps of `RelativePicard.familyScheme πX`). This is Kleiman's functor `Div_{X/S}` (Def. 3.6,
  p. 23), restricted to the divisors whose fibres have Hilbert polynomial `θ` in `P^n` and that are
  proper over `T` (automatic for a closed immersion), the form `Div^θ_X` of the Picard plan; it is
  stated on `X_T` (X-first), so that the ideal of a point is an ideal sheaf on
  `RelativePicard.familyScheme πX` at `T`. The base change of a point is a point
  (`IsRelativeDivisorFamily.comap`): flatness of `D` makes the pulled-back ideal the ideal of the
  base change (Kleiman, the remark after Def. 3.6, p. 23;
  `Scheme.Hom.IsRelativeEffectiveCartier.of_isPullback` for the cartesian square
  `Scheme.isPullback_pullbackMap_snd`), and `IsImmersedHilbertFamily.comap`.
  `locallyNoetherianRelativeDivisorFunctor` is its restriction to locally Noetherian test schemes.
* `relativeDivisorSubfunctor i hi θ`: the subfunctor of `immersedHilbertFunctor i hi θ` of the
  points that are relative effective Cartier divisors, and `relativeDivisorFunctorIso`: its
  underlying functor is `relativeDivisorFunctor i hi θ`. This is the sense in which `Div^θ_X` is a
  subfunctor of `Hilb^θ_X` in Kleiman's Thm 3.7 (p. 23); its openness on locally Noetherian test
  schemes is `isOpenSubfunctor_locallyNoetherianRelativeDivisorSubfunctor`
  (`HilbertScheme/Divisor/Representability`).

Kleiman's `Div_{X/S}` carries no polynomial; fixing the Hilbert polynomial `θ` in `P^n` through
`i` is the convention of the Picard plan (row F14), and for `𝒪_X(1) = i^* 𝒪(1)` it is
Kleiman's `Hilb^θ_{X/S}`-polynomial.
-/

@[expose] public section

noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite
open scoped Polynomial

universe u

namespace AlgebraicGeometry.ProjectiveSpace

variable {ι : Type u} {A : Type u} [CommRing A] {X : Scheme.{u}}
  {πX : X ⟶ Spec (CommRingCat.of A)} (i : X ⟶ ProjectiveSpace A ι) (hi : i ≫ toSpec A ι = πX)
  (θ : ℚ[X])

/-- **Points of the divisor functor `Div^θ_X`** (Kleiman, arXiv:math/0504020v1, Def. 3.6, p. 23,
with fibre Hilbert polynomial `θ` in `P^n` through `i`): a closed subscheme
`D ⊆ X ×_{Spec A} T` that is a relative effective Cartier divisor over `T` (Def. 3.3, p. 22) and a
point of the Hilbert functor of `X` with polynomial `θ`. -/
structure IsRelativeDivisorFamily {T : Scheme.{u}} (g : T ⟶ Spec (CommRingCat.of A))
    (D : (pullback πX g).IdealSheafData) : Prop where
  /-- `D` is a relative effective Cartier divisor of `X ×_{Spec A} T` over `T`. -/
  isRelativeEffectiveCartier :
    Scheme.Hom.IsRelativeEffectiveCartier D.subschemeι (pullback.snd πX g)
  /-- `D` is a point of the Hilbert functor of `X` with polynomial `θ`: proper over `T`, with
  image in `P^n_A ×_{Spec A} T` flat over `T` with fibre Hilbert polynomials `θ`. -/
  isImmersedHilbertFamily : IsImmersedHilbertFamily i hi θ g D

namespace IsRelativeDivisorFamily

variable {i hi θ} {T T' : Scheme.{u}} {g : T ⟶ Spec (CommRingCat.of A)}
  {g' : T' ⟶ Spec (CommRingCat.of A)} {D : (pullback πX g).IdealSheafData}

/-- A point of `Div^θ_X` is flat over the base. -/
theorem flat (hD : IsRelativeDivisorFamily i hi θ g D) :
    Flat (D.subschemeι ≫ pullback.snd πX g) :=
  hD.isRelativeEffectiveCartier.flat

/-- The image of a point of `Div^θ_X` in `P^n_A ×_{Spec A} T` is a point of `Hilb^θ(T)`. -/
theorem isHilbertFamily_map (hD : IsRelativeDivisorFamily i hi θ g D) :
    IsHilbertFamily ι θ g (D.map (immersionBaseChange i hi g)) :=
  hD.isImmersedHilbertFamily.isHilbertFamily_map

/-- A point of `Div^θ_X` is closed in `P^n_A ×_{Spec A} T`. -/
theorem isClosedImmersion [IsPreimmersion i] (hD : IsRelativeDivisorFamily i hi θ g D) :
    IsClosedImmersion (D.subschemeι ≫ immersionBaseChange i hi g) :=
  hD.isImmersedHilbertFamily.isClosedImmersion

/-- **Base change of points of `Div^θ_X`** (Kleiman, arXiv:math/0504020v1, the remark after
Def. 3.6, p. 23): for `f : T' ⟶ T` over `Spec A`, the pullback of a point `D` along
`X_{T'} ⟶ X_T` is a point. Since `D` is flat over `T`, the pullback of its ideal is the ideal of
the base change, which is therefore invertible
(`Scheme.Hom.IsRelativeEffectiveCartier.of_isPullback` for the cartesian square
`Scheme.isPullback_pullbackMap_snd`); the Hilbert condition is `IsImmersedHilbertFamily.comap`. -/
theorem comap [IsPreimmersion i] (f : T' ⟶ T) (h : f ≫ g = g')
    (hD : IsRelativeDivisorFamily i hi θ g D) :
    IsRelativeDivisorFamily i hi θ g' (D.comap (pullback.map πX g' πX g (𝟙 X) f (𝟙 _)
      (by simp) (by rw [Category.comp_id, h]))) where
  isRelativeEffectiveCartier := hD.isRelativeEffectiveCartier.of_isPullback
    (Scheme.isPullback_pullbackMap_snd πX g g' f h) (D.isPullback_subschemeMap_comap _)
  isImmersedHilbertFamily := hD.isImmersedHilbertFamily.comap f h

end IsRelativeDivisorFamily

/-- **Points of `Div^θ_X` for a closed `X ⊆ P^n_A`**: for a closed immersion `i` and finitely many
coordinates, a closed subscheme `D ⊆ X ×_{Spec A} T` is a point of `Div^θ_X(T)` if and only if it
is a relative effective Cartier divisor over `T` whose image in `P^n_A ×_{Spec A} T` is a point of
`Hilb^θ(T)`; properness over `T` is automatic. -/
theorem isRelativeDivisorFamily_iff_of_isClosedImmersion [IsClosedImmersion i] [Finite ι]
    {T : Scheme.{u}} (g : T ⟶ Spec (CommRingCat.of A)) (D : (pullback πX g).IdealSheafData) :
    IsRelativeDivisorFamily i hi θ g D ↔
      Scheme.Hom.IsRelativeEffectiveCartier D.subschemeι (pullback.snd πX g) ∧
        IsHilbertFamily ι θ g (D.map (immersionBaseChange i hi g)) :=
  ⟨fun hD => ⟨hD.isRelativeEffectiveCartier, hD.isHilbertFamily_map⟩, fun hD =>
    ⟨hD.1, (isImmersedHilbertFamily_iff_of_isClosedImmersion i hi θ g D).mpr hD.2⟩⟩

/-- **Constructing points of `Div^θ_X` for a closed `X ⊆ P^n_A`**: for a closed immersion `i` and
finitely many coordinates, a relative effective Cartier divisor `D ⊆ X ×_{Spec A} T` over `T`
whose image in `P^n_A ×_{Spec A} T` has fibre Hilbert polynomial `θ` at every field point of `T` is
a point of `Div^θ_X(T)`: the image is isomorphic to `D` over `T`
(`Scheme.IdealSheafData.mapSubschemeIso`), hence flat over `T`. -/
theorem IsRelativeDivisorFamily.of_isRelativeEffectiveCartier [IsClosedImmersion i] [Finite ι]
    {T : Scheme.{u}} {g : T ⟶ Spec (CommRingCat.of A)} {D : (pullback πX g).IdealSheafData}
    (hD : Scheme.Hom.IsRelativeEffectiveCartier D.subschemeι (pullback.snd πX g))
    (hθ : ∀ (K : Type u) [Field K] (x : Spec (CommRingCat.of K) ⟶ T),
      subschemeHilbertPolynomial ι K
        ((D.map (immersionBaseChange i hi g)).comap (pointMap ι g x)) = θ) :
    IsRelativeDivisorFamily i hi θ g D := by
  refine (isRelativeDivisorFamily_iff_of_isClosedImmersion i hi θ g D).mpr ⟨hD, ⟨?_, hθ⟩⟩
  have := hD.flat
  rw [← Iso.inv_hom_id_assoc (D.mapSubschemeIso (immersionBaseChange i hi g))
    (D.map (immersionBaseChange i hi g)).subschemeι,
    Scheme.IdealSheafData.mapSubschemeIso_hom_subschemeι, Category.assoc, Category.assoc,
    immersionBaseChange_snd]
  infer_instance

-- `pullback.map` is a `pullback.lift` carrying its own `HasPullback` instances; relaxing
-- instance transparency lets `pullback.lift_fst`/`pullback.lift_snd` match them, as in
-- Mathlib's `pullback.map_comp` and `pullback.map_id`.
set_option backward.isDefEq.respectTransparency false in
/-- **The functor `Div^θ_X` of relative effective Cartier divisors** (Kleiman,
arXiv:math/0504020v1, Def. 3.6, p. 23, with fibre Hilbert polynomial `θ` in `P^n` through `i`), on
all schemes `T` over `Spec A`, X-first: `T` goes to the relative effective Cartier divisors
`D ⊆ X ×_{Spec A} T` over `T` that are points of the Hilbert functor of `X` with polynomial `θ`,
and `f : T' ⟶ T` acts by pullback along `pullback.map πX _ πX _ (𝟙 X) f (𝟙 _)` (the maps of
`RelativePicard.familyScheme πX`). Kleiman's representability statement (Thm 3.7, p. 23)
concerns a projective and flat `X`; on locally Noetherian test schemes it is
`HilbertScheme/Divisor/Representability`. -/
def relativeDivisorFunctor [IsPreimmersion i] :
    (Over (Spec (CommRingCat.of A)))ᵒᵖ ⥤ Type u where
  obj T := {D : (pullback πX T.unop.hom).IdealSheafData //
    IsRelativeDivisorFamily i hi θ T.unop.hom D}
  map {T T'} f := TypeCat.ofHom fun D =>
    ⟨D.1.comap (pullback.map πX T'.unop.hom πX T.unop.hom (𝟙 X) f.unop.left (𝟙 _) (by simp)
        (by rw [Category.comp_id, Over.w f.unop])),
      D.2.comap f.unop.left (Over.w f.unop)⟩
  map_id T := by
    refine ConcreteCategory.hom_ext _ _ fun D => Subtype.ext ?_
    change D.1.comap (pullback.map πX _ πX _ (𝟙 X) (𝟙 T.unop.left) (𝟙 _) _ _) = D.1
    rw [pullback.map_id, Scheme.IdealSheafData.comap_id]
  map_comp {T T' T''} f f' := by
    refine ConcreteCategory.hom_ext _ _ fun D => Subtype.ext ?_
    change D.1.comap (pullback.map πX _ πX _ (𝟙 X) (f'.unop.left ≫ f.unop.left) (𝟙 _) _ _) =
      (D.1.comap (pullback.map πX _ πX _ (𝟙 X) f.unop.left (𝟙 _) _ _)).comap
        (pullback.map πX _ πX _ (𝟙 X) f'.unop.left (𝟙 _) _ _)
    rw [← Scheme.IdealSheafData.comap_comp]
    congr 1
    apply pullback.hom_ext <;> simp [pullback.map]

theorem relativeDivisorFunctor_map_coe [IsPreimmersion i]
    {T T' : (Over (Spec (CommRingCat.of A)))ᵒᵖ} (f : T ⟶ T')
    (D : (relativeDivisorFunctor i hi θ).obj T) :
    ((relativeDivisorFunctor i hi θ).map f D).1 =
      D.1.comap (pullback.map πX T'.unop.hom πX T.unop.hom (𝟙 X) f.unop.left (𝟙 _) (by simp)
        (by rw [Category.comp_id, Over.w f.unop])) :=
  rfl

/-- **`Div^θ_X` on locally Noetherian test schemes**: the restriction of
`relativeDivisorFunctor i hi θ` along `Scheme.locallyNoetherianOverInclusion`. -/
abbrev locallyNoetherianRelativeDivisorFunctor [IsPreimmersion i] :
    (Scheme.LocallyNoetherianOver (Spec (CommRingCat.of A)))ᵒᵖ ⥤ Type u :=
  (Scheme.locallyNoetherianOverInclusion _).op ⋙ relativeDivisorFunctor i hi θ

/-- **`Div^θ_X` as a subfunctor of `Hilb^θ_X`** (Kleiman, arXiv:math/0504020v1, Thm 3.7, p. 23):
the points of the Hilbert functor of `X` that are relative effective Cartier divisors over the
base. Base change preserves them (`Scheme.Hom.IsRelativeEffectiveCartier.of_isPullback`). -/
def relativeDivisorSubfunctor [IsPreimmersion i] :
    Subfunctor (immersedHilbertFunctor i hi θ) where
  obj T := {V | Scheme.Hom.IsRelativeEffectiveCartier V.1.subschemeι
    (pullback.snd πX T.unop.hom)}
  map {T T'} f V hV := hV.of_isPullback
    (Scheme.isPullback_pullbackMap_snd πX T.unop.hom T'.unop.hom f.unop.left (Over.w f.unop))
    (V.1.isPullback_subschemeMap_comap _)

theorem mem_relativeDivisorSubfunctor_obj [IsPreimmersion i]
    {T : (Over (Spec (CommRingCat.of A)))ᵒᵖ} (V : (immersedHilbertFunctor i hi θ).obj T) :
    V ∈ (relativeDivisorSubfunctor i hi θ).obj T ↔
      Scheme.Hom.IsRelativeEffectiveCartier V.1.subschemeι (pullback.snd πX T.unop.hom) :=
  Iff.rfl

/-- The component of `relativeDivisorFunctorIso` at `T`: forgetting the nesting of the two
conditions. -/
def relativeDivisorFunctorObjEquiv [IsPreimmersion i] (T : (Over (Spec (CommRingCat.of A)))ᵒᵖ) :
    (relativeDivisorSubfunctor i hi θ).toFunctor.obj T ≃
      (relativeDivisorFunctor i hi θ).obj T where
  toFun D := ⟨D.1.1, D.2, D.1.2⟩
  invFun D := ⟨⟨D.1, D.2.isImmersedHilbertFamily⟩, D.2.isRelativeEffectiveCartier⟩
  left_inv _ := rfl
  right_inv _ := rfl

/-- **The subfunctor of divisors of `Hilb^θ_X` is `Div^θ_X`**: the underlying functor of
`relativeDivisorSubfunctor i hi θ` is isomorphic to `relativeDivisorFunctor i hi θ`, with the
identity on the underlying closed subschemes. -/
def relativeDivisorFunctorIso [IsPreimmersion i] :
    (relativeDivisorSubfunctor i hi θ).toFunctor ≅ relativeDivisorFunctor i hi θ :=
  NatIso.ofComponents (fun T => (relativeDivisorFunctorObjEquiv i hi θ T).toIso) fun _ => rfl

theorem relativeDivisorFunctorIso_hom_app_coe [IsPreimmersion i]
    (T : (Over (Spec (CommRingCat.of A)))ᵒᵖ)
    (D : (relativeDivisorSubfunctor i hi θ).toFunctor.obj T) :
    ((relativeDivisorFunctorIso i hi θ).hom.app T D).1 = D.1.1 :=
  rfl

theorem relativeDivisorFunctorIso_inv_app_coe [IsPreimmersion i]
    (T : (Over (Spec (CommRingCat.of A)))ᵒᵖ) (D : (relativeDivisorFunctor i hi θ).obj T) :
    ((relativeDivisorFunctorIso i hi θ).inv.app T D).1.1 = D.1 :=
  rfl

end AlgebraicGeometry.ProjectiveSpace
