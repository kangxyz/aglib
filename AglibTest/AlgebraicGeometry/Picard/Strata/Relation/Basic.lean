/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Picard.Strata.Relation.Basic

/-!
# Consumer checks for the relation `Z ×_P Z` through `P_{X/S}`

Equal classes in `Pic_{X/S,(fppf)}` differ by base classes (Kleiman, *The Picard scheme*,
arXiv:math/0504020v1, Thm 2.5(1), p. 18), for two Abel classes and for the pullbacks of the
universal class of `Z = C.abelPreimageOver E` (proof of Thm 4.8, p. 30); the divisor classified by
a point of `Z`; the functor `Z ×_P Z`; with axiom guards.
-/

@[expose] public section

noncomputable section

open CategoryTheory Limits Opposite AlgebraicGeometry
open AlgebraicGeometry.ProjectiveSpace Scheme.Modules.Invertible Scheme.RelativePicard
open scoped Polynomial

universe u

namespace AglibTest.StrataRelationBasic

/-- Equal fppf Abel classes differ by a base class, for `p` proper, flat and geometrically
integral over a locally Noetherian base. -/
example {S X : Scheme.{u}} (p : X ⟶ S) [IsLocallyNoetherian S] [IsProper p] [Flat p]
    [GeometricallyIntegral p] {T : Over S} {D D' : (pullback p T.hom).IdealSheafData}
    (hD : Scheme.Hom.IsRelativeEffectiveCartier D.subschemeι (pullback.snd p T.hom))
    (hD' : Scheme.Hom.IsRelativeEffectiveCartier D'.subschemeι (pullback.snd p T.hom)) :
    fppfAbelClass p D hD = fppfAbelClass p D' hD' ↔
      ∃ n : PicardGroup T.left,
        abelClass p D hD = abelClass p D' hD' + pullbackClass (pullback.snd p T.hom) n :=
  fppfAbelClass_eq_fppfAbelClass_iff p hD hD'

variable {A : Type u} [CommRing A] {ι : Type u} {X : Scheme.{u}}
  {πX : X ⟶ Spec (CommRingCat.of A)} {i : X ⟶ ProjectiveSpace A ι} {hi : i ≫ toSpec A ι = πX}
  [IsPreimmersion i] {θ : ℚ[X]} (C : FiberCondition πX)
  {D : Scheme.LocallyNoetherianOver (Spec (CommRingCat.of A))}
  (E : (locallyNoetherianRelativeDivisorFunctor i hi θ).RepresentableBy D)

/-- The pullbacks of `α_Z` along two points of `Z` agree exactly when the classified divisors have
Abel classes differing by a base class. -/
example [IsNoetherianRing A] [IsProper πX] [Flat πX] [GeometricallyIntegral πX]
    {T : Scheme.LocallyNoetherianOver (Spec (CommRingCat.of A))} (a b : T ⟶ C.abelPreimageOver E) :
    (fppfPicardSheaf πX).obj.map a.hom.op (C.abelPreimageFppfAbelClass E) =
        (fppfPicardSheaf πX).obj.map b.hom.op (C.abelPreimageFppfAbelClass E) ↔
      ∃ n : PicardGroup T.obj.left,
        abelClass πX (T := T.obj) ((C.abelPreimageRepresentableBy E).homEquiv a).1.1
            ((C.abelPreimageRepresentableBy E).homEquiv a).1.2.isRelativeEffectiveCartier =
          abelClass πX (T := T.obj) ((C.abelPreimageRepresentableBy E).homEquiv b).1.1
              ((C.abelPreimageRepresentableBy E).homEquiv b).1.2.isRelativeEffectiveCartier +
            pullbackClass (pullback.snd πX T.obj.hom) n :=
  C.fppfPicardSheaf_map_abelPreimageFppfAbelClass_eq_iff E a b

/-- The divisor classified by a point of `Z` is the pullback of the universal divisor. -/
example {T : Scheme.LocallyNoetherianOver (Spec (CommRingCat.of A))}
    (z : T ⟶ C.abelPreimageOver E) :
    ((C.abelPreimageRepresentableBy E).homEquiv z).1.1 =
      ((C.abelPreimageRepresentableBy E).homEquiv (𝟙 _)).1.1.comap
        (Scheme.LinearSystem.familyMap πX z.hom) :=
  C.abelPreimageRepresentableBy_homEquiv_coe_eq_comap E z

/-- The functor `Z ×_P Z` acts by composition. -/
example {T T' : (Scheme.LocallyNoetherianOver (Spec (CommRingCat.of A)))ᵒᵖ} (f : T ⟶ T')
    (ab : (C.abelRelation E).obj T) :
    ((C.abelRelation E).map f ab).1 = (f.unop ≫ ab.1.1, f.unop ≫ ab.1.2) :=
  C.abelRelation_map_coe E f ab

/--
info: 'AlgebraicGeometry.Scheme.RelativePicard.quotientProjection_comp_toFppfPicardSheaf_app_eq_iff'
  depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms quotientProjection_comp_toFppfPicardSheaf_app_eq_iff

/--
info: 'AlgebraicGeometry.Scheme.RelativePicard.fppfAbelClass_eq_fppfAbelClass_iff' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms fppfAbelClass_eq_fppfAbelClass_iff

/--
info: 'AlgebraicGeometry.Scheme.RelativePicard.FiberCondition.fppfPicardSheaf_map_abelPreimageFppfAbelClass_eq_iff'
  depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms FiberCondition.fppfPicardSheaf_map_abelPreimageFppfAbelClass_eq_iff

/--
info: 'AlgebraicGeometry.Scheme.RelativePicard.FiberCondition.abelPreimageRepresentableBy_homEquiv_coe_eq_comap'
  depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms FiberCondition.abelPreimageRepresentableBy_homEquiv_coe_eq_comap

/--
info: 'AlgebraicGeometry.Scheme.RelativePicard.FiberCondition.abelRelation' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms FiberCondition.abelRelation

end AglibTest.StrataRelationBasic
