/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Picard.Abel.Divisor
public import Aglib.AlgebraicGeometry.Picard.Comparison.LocallyTrivial
public import Aglib.AlgebraicGeometry.Picard.LinearSystem.AbelClass

/-!
# The relation `Z ×_P Z` through the relative Picard functor

Let `p : X ⟶ S` be proper, flat and geometrically integral over a locally Noetherian `S`, and
`P = Pic_{X/S,(fppf)}`. By Kleiman, *The Picard scheme*, arXiv:math/0504020v1, Thm 2.5(1), p. 18,
the map `P_{X/S}(T) ⟶ P(T)` is injective for every `S`-scheme `T`
(`toFppfPicardSheaf_app_injective_of_isProper_of_flat_of_geometricallyIntegral`), and
`P_{X/S}(T) = Pic(X ×_S T) / Pic(T)` by definition (Def. 2.2, p. 17). Hence:

* `RelativePicard.quotientProjection_comp_toFppfPicardSheaf_app_eq_iff`: two classes on
  `X ×_S T` have the same image in `P(T)` if and only if they differ by a class pulled back from
  `T`; `RelativePicard.fppfAbelClass_eq_fppfAbelClass_iff` is the case of two Abel classes.

Let `A` be a ring, `i : X ⟶ P^n_A` a preimmersion over `S = Spec A` (`hi : i ≫ toSpec A ι = πX`),
`C` a fibre condition, `E` a representation of `Div^θ_X` on locally Noetherian test schemes by
`D`, and `Z = C.abelPreimageOver E` the open subscheme `Pic^C ×_P Div^θ_X` of `D`, with universal
class `α_Z = C.abelPreimageFppfAbelClass E` (`Picard/Abel/Divisor`). For a locally Noetherian
`T` and `a : T ⟶ Z`, write `W_a` for the divisor classified by `a`.

* `FiberCondition.abelPreimageRepresentableBy_homEquiv_coe_eq_comap`: `W_a` is the pullback of
  the universal divisor `W_Z` along `X ×_S T ⟶ X ×_S Z`.
* `FiberCondition.fppfPicardSheaf_map_abelPreimageFppfAbelClass_eq_iff`: for `a, b : T ⟶ Z`,
  `a^* α_Z = b^* α_Z` if and only if `abelClass W_a = abelClass W_b + p_T^* N` for a class `N` on
  `T`. This is the content, for two points of `Z`, of the step "Virtually by definition, the
  product `T′ ×_{P_0^{φ0}} Z` is equal to `LinSys_{L′/X_{T′}/T′}`" of Kleiman's proof of Thm 4.8
  (p. 30); it uses Thm 2.5(1).
* `FiberCondition.abelRelation C E`: the functor `R = Z ×_P Z` on locally Noetherian test schemes,
  `T ↦ {(a, b) : T ⟶ Z | a^* α_Z = b^* α_Z}`. Its representability, on a fine stratum, is
  `Picard/Strata/Relation/Representability`.
-/

@[expose] public section

noncomputable section

open CategoryTheory Limits Opposite

universe u

namespace AlgebraicGeometry.Scheme.RelativePicard

open Modules.Invertible LinearSystem ProjectiveSpace

section Comparison

variable {S X : Scheme.{u}} (p : X ⟶ S) [IsLocallyNoetherian S] [IsProper p] [Flat p]
  [GeometricallyIntegral p]

/-- **Equal classes in `Pic_{X/S,(fppf)}(T)`** (Kleiman, arXiv:math/0504020v1, Thm 2.5(1), p. 18,
and Def. 2.2, p. 17): for `p` proper, flat and geometrically integral over a locally Noetherian
`S`, two classes on `X ×_S T` have the same image in `Pic_{X/S,(fppf)}(T)` if and only if they
differ by a class pulled back from `T`. -/
theorem quotientProjection_comp_toFppfPicardSheaf_app_eq_iff {T : Over S}
    (x y : PicardGroup (pullback p T.hom)) :
    (quotientProjection p ≫ toFppfPicardSheaf p).app (op T) x =
        (quotientProjection p ≫ toFppfPicardSheaf p).app (op T) y ↔
      ∃ n : PicardGroup T.left, x = y + pullbackClass (pullback.snd p T.hom) n := by
  rw [← quotientProjection_app_eq_iff p x y]
  exact (toFppfPicardSheaf_app_injective_of_isProper_of_flat_of_geometricallyIntegral p
    (op T)).eq_iff

/-- **Equal fppf Abel classes** (Kleiman, arXiv:math/0504020v1, Thm 2.5(1), p. 18): two relative
effective Cartier divisors of `X ×_S T ⟶ T` have the same class in `Pic_{X/S,(fppf)}(T)` if and
only if their Abel classes differ by a class pulled back from `T`. -/
theorem fppfAbelClass_eq_fppfAbelClass_iff {T : Over S}
    {D D' : (pullback p T.hom).IdealSheafData}
    (hD : Hom.IsRelativeEffectiveCartier D.subschemeι (pullback.snd p T.hom))
    (hD' : Hom.IsRelativeEffectiveCartier D'.subschemeι (pullback.snd p T.hom)) :
    fppfAbelClass p D hD = fppfAbelClass p D' hD' ↔
      ∃ n : PicardGroup T.left,
        abelClass p D hD = abelClass p D' hD' + pullbackClass (pullback.snd p T.hom) n :=
  quotientProjection_comp_toFppfPicardSheaf_app_eq_iff p _ _

end Comparison

namespace FiberCondition

variable {ι : Type u} {A : Type u} [CommRing A] {X : Scheme.{u}}
  {πX : X ⟶ Spec (CommRingCat.of A)} {i : X ⟶ ProjectiveSpace A ι} {hi : i ≫ toSpec A ι = πX}
  [IsPreimmersion i] {θ : Polynomial ℚ} (C : FiberCondition πX)
  {D : Scheme.LocallyNoetherianOver (Spec (CommRingCat.of A))}
  (E : (locallyNoetherianRelativeDivisorFunctor i hi θ).RepresentableBy D)

/-- **The divisor classified by a point of `Z`** is the pullback of the universal divisor of `Z`
along the base-change map `X ×_S T ⟶ X ×_S Z` of the family. -/
theorem abelPreimageRepresentableBy_homEquiv_coe_eq_comap
    {T : Scheme.LocallyNoetherianOver (Spec (CommRingCat.of A))} (z : T ⟶ C.abelPreimageOver E) :
    ((C.abelPreimageRepresentableBy E).homEquiv z).1.1 =
      ((C.abelPreimageRepresentableBy E).homEquiv (𝟙 _)).1.1.comap
        (LinearSystem.familyMap πX z.hom) := by
  rw [Functor.RepresentableBy.homEquiv_eq]
  rfl

/-- **The relation `Z ×_P Z` through `P_{X/S}`** (Kleiman, arXiv:math/0504020v1, proof of
Thm 4.8, p. 30, with Thm 2.5(1), p. 18): for `p = πX` proper, flat and geometrically integral over
a Noetherian ring and points `a, b : T ⟶ Z` of `Z = C.abelPreimageOver E`, the pullbacks of the
universal class `α_Z` agree if and only if the Abel classes of the classified divisors differ by a
class pulled back from `T`. -/
theorem fppfPicardSheaf_map_abelPreimageFppfAbelClass_eq_iff [IsNoetherianRing A] [IsProper πX]
    [Flat πX] [GeometricallyIntegral πX]
    {T : Scheme.LocallyNoetherianOver (Spec (CommRingCat.of A))} (a b : T ⟶ C.abelPreimageOver E) :
    (fppfPicardSheaf πX).obj.map a.hom.op (C.abelPreimageFppfAbelClass E) =
        (fppfPicardSheaf πX).obj.map b.hom.op (C.abelPreimageFppfAbelClass E) ↔
      ∃ n : PicardGroup T.obj.left,
        abelClass πX (T := T.obj) ((C.abelPreimageRepresentableBy E).homEquiv a).1.1
            ((C.abelPreimageRepresentableBy E).homEquiv a).1.2.isRelativeEffectiveCartier =
          abelClass πX (T := T.obj) ((C.abelPreimageRepresentableBy E).homEquiv b).1.1
              ((C.abelPreimageRepresentableBy E).homEquiv b).1.2.isRelativeEffectiveCartier +
            pullbackClass (pullback.snd πX T.obj.hom) n := by
  rw [fppfPicardSheaf_map_abelPreimageFppfAbelClass, fppfPicardSheaf_map_abelPreimageFppfAbelClass]
  exact fppfAbelClass_eq_fppfAbelClass_iff πX _ _

/-- Pullback of the universal class of `Z` along a composite. -/
theorem fppfPicardSheaf_map_comp_abelPreimageFppfAbelClass
    {T T' : Scheme.LocallyNoetherianOver (Spec (CommRingCat.of A))} (f : T' ⟶ T)
    (a : T ⟶ C.abelPreimageOver E) :
    (fppfPicardSheaf πX).obj.map (f ≫ a).hom.op (C.abelPreimageFppfAbelClass E) =
      (fppfPicardSheaf πX).obj.map f.hom.op
        ((fppfPicardSheaf πX).obj.map a.hom.op (C.abelPreimageFppfAbelClass E)) := by
  rw [ObjectProperty.FullSubcategory.comp_hom, op_comp, Functor.map_comp,
    ConcreteCategory.comp_apply]

/-- **The relation `R = Z ×_P Z`** on locally Noetherian test schemes (Kleiman,
arXiv:math/0504020v1, proof of Thm 4.8, p. 30): the pairs `(a, b)` of points of
`Z = C.abelPreimageOver E` over `T` with `a^* α_Z = b^* α_Z` in `Pic_{X/S,(fppf)}(T)`, functorial
by composition. -/
def abelRelation : (Scheme.LocallyNoetherianOver (Spec (CommRingCat.of A)))ᵒᵖ ⥤ Type u where
  obj T := {ab : (T.unop ⟶ C.abelPreimageOver E) × (T.unop ⟶ C.abelPreimageOver E) //
    (fppfPicardSheaf πX).obj.map ab.1.hom.op (C.abelPreimageFppfAbelClass E) =
      (fppfPicardSheaf πX).obj.map ab.2.hom.op (C.abelPreimageFppfAbelClass E)}
  map {T T'} f := TypeCat.ofHom fun ab => ⟨(f.unop ≫ ab.1.1, f.unop ≫ ab.1.2), by
    rw [fppfPicardSheaf_map_comp_abelPreimageFppfAbelClass,
      fppfPicardSheaf_map_comp_abelPreimageFppfAbelClass, ab.2]⟩
  map_id T := by
    refine ConcreteCategory.hom_ext _ _ fun ab => Subtype.ext ?_
    change (𝟙 T.unop ≫ ab.1.1, 𝟙 T.unop ≫ ab.1.2) = ab.1
    rw [Category.id_comp, Category.id_comp]
  map_comp {T T' T''} f g := by
    refine ConcreteCategory.hom_ext _ _ fun ab => Subtype.ext ?_
    change ((g.unop ≫ f.unop) ≫ ab.1.1, (g.unop ≫ f.unop) ≫ ab.1.2) =
      (g.unop ≫ f.unop ≫ ab.1.1, g.unop ≫ f.unop ≫ ab.1.2)
    rw [Category.assoc, Category.assoc]

theorem abelRelation_map_coe {T T' : (Scheme.LocallyNoetherianOver (Spec (CommRingCat.of A)))ᵒᵖ}
    (f : T ⟶ T') (ab : (C.abelRelation E).obj T) :
    ((C.abelRelation E).map f ab).1 = (f.unop ≫ ab.1.1, f.unop ≫ ab.1.2) :=
  rfl

end FiberCondition

end AlgebraicGeometry.Scheme.RelativePicard
