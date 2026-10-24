/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.HilbertScheme.Divisor.Representability
public import Aglib.AlgebraicGeometry.Picard.Abel.Divisor

/-!
# Consumer checks for the Abel map of `Div^θ_X`

The Abel map `D ↦ [𝒪(D)] = −[I_D]` out of the divisor functor `Div^θ_X` into the absolute Picard
functor, a lift of Kleiman's Abel map (*The Picard scheme*, arXiv:math/0504020v1, Def. 4.6,
p. 27), its fppf form, the pullbacks of the universal Abel class of a representation of
`Div^θ_X`, and the open subscheme `Pic^C ×_P Div^θ_X` of the representing scheme for a fibre
condition `C` (proof of Thm 4.8, p. 30), with its H-quasi-projectivity for the representation
`divisorSchemeOver` of `HilbertScheme/Divisor/Representability`; with axiom guards.
-/

@[expose] public section

noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
open AlgebraicGeometry.ProjectiveSpace Scheme.RelativePicard Scheme.Modules.Invertible
open Scheme.LocalRepresentability
open scoped Polynomial

universe u

namespace AglibTest.AbelDivisor

variable {A : Type u} [CommRing A] {ι : Type u} {X : Scheme.{u}}
  (i : X ⟶ ProjectiveSpace A ι) [IsClosedImmersion i] (θ : ℚ[X])

/-- `Div^θ_X` pulls divisors back along the maps of `familyScheme`, those of
`familyPicardFunctor`. -/
example {T T' : Over (Spec (CommRingCat.of A))} (g : T' ⟶ T)
    (D : (relativeDivisorFunctor i rfl θ).obj (op T)) :
    ((relativeDivisorFunctor i rfl θ).map g.op D).1 =
      D.1.comap ((familyScheme (i ≫ toSpec A ι)).map g) :=
  relativeDivisorFunctor_map_coe_eq_comap_familyScheme_map i rfl θ g.op D

/-- A line bundle represents the Abel class exactly when its dual is the ideal of the divisor. -/
example {T : Over (Spec (CommRingCat.of A))}
    (D : (relativeDivisorFunctor i rfl θ).obj (op T))
    (L : LineBundle (pullback (i ≫ toSpec A ι) T.hom)) :
    classOf _ L = abelClass _ D.1 D.2.isRelativeEffectiveCartier ↔
      Nonempty ((dualLineBundle _ L).val ≅ Scheme.Hom.idealModule D.1.subschemeι) :=
  classOf_eq_abelClass_iff _ D.2.isRelativeEffectiveCartier L

/-- In particular the dual of the Abel class of `D` is the ideal of `D`. -/
example {T : Over (Spec (CommRingCat.of A))} (D : (relativeDivisorFunctor i rfl θ).obj (op T)) :
    Nonempty ((dualLineBundle _ (dualLineBundle _
      D.2.isRelativeEffectiveCartier.idealLineBundle)).val ≅
        Scheme.Hom.idealModule D.1.subschemeι) :=
  nonempty_dualLineBundle_iso_idealModule_of_classOf_eq_abelClass _
    D.2.isRelativeEffectiveCartier rfl

/-- The Abel map sends a divisor to its Abel class, and it is a natural transformation out of
the lifted divisor functor. -/
example {T T' : Over (Spec (CommRingCat.of A))} (g : T' ⟶ T)
    (D : (relativeDivisorFunctor i rfl θ).obj (op T)) :
    (divisorAbelMap i rfl θ).app (op T) (ULift.up D) =
        abelClass _ D.1 D.2.isRelativeEffectiveCartier ∧
      (relativeDivisorFunctor i rfl θ ⋙ uliftFunctor.{u + 1}).map g.op ≫
          (divisorAbelMap i rfl θ).app (op T') =
        (divisorAbelMap i rfl θ).app (op T) ≫
          (familyPicardFunctor (i ≫ toSpec A ι) ⋙
            CategoryTheory.forget AddCommGrpCat.{u + 1}).map g.op :=
  ⟨divisorAbelMap_app_apply i rfl θ (op T) D, (divisorAbelMap i rfl θ).naturality g.op⟩

/-- The fppf Abel map sends a divisor to its fppf Abel class, and it is a natural transformation
out of the lifted divisor functor. -/
example {T T' : Over (Spec (CommRingCat.of A))} (g : T' ⟶ T)
    (D : (relativeDivisorFunctor i rfl θ).obj (op T)) :
    (divisorFppfAbelMap i rfl θ).app (op T) (ULift.up D) =
        fppfAbelClass _ D.1 D.2.isRelativeEffectiveCartier ∧
      (relativeDivisorFunctor i rfl θ ⋙ uliftFunctor.{u + 1}).map g.op ≫
          (divisorFppfAbelMap i rfl θ).app (op T') =
        (divisorFppfAbelMap i rfl θ).app (op T) ≫
          ((fppfPicardSheaf (i ≫ toSpec A ι)).obj ⋙
            CategoryTheory.forget AddCommGrpCat.{u + 1}).map g.op :=
  ⟨divisorFppfAbelMap_app_apply i rfl θ (op T) D, (divisorFppfAbelMap i rfl θ).naturality g.op⟩

variable {θ} {D : Scheme.LocallyNoetherianOver (Spec (CommRingCat.of A))}
  (E : (locallyNoetherianRelativeDivisorFunctor i rfl θ).RepresentableBy D)
  (C : FiberCondition (i ≫ toSpec A ι))

/-- The pullback of the universal Abel class along `a : T ⟶ D` is the Abel class of the divisor
classified by `a`. -/
example {T : Scheme.LocallyNoetherianOver (Spec (CommRingCat.of A))} (a : T ⟶ D) :
    (fppfPicardSheaf (i ≫ toSpec A ι)).obj.map a.hom.op (universalFppfAbelClass E) =
      fppfAbelClass _ (E.homEquiv a).1 (E.homEquiv a).2.isRelativeEffectiveCartier :=
  fppfPicardSheaf_map_universalFppfAbelClass E a

/-- A divisor lies in `Pic^C ×_P Div^θ_X` exactly when its Abel class satisfies `C` at every
point. -/
example {T : Over (Spec (CommRingCat.of A))} (W : (relativeDivisorFunctor i rfl θ).obj (op T)) :
    W ∈ (C.abelPreimage i rfl θ).obj (op T) ↔
      ∀ t : T.left, C.Holds T (abelClass _ W.1 W.2.isRelativeEffectiveCartier) t :=
  C.mem_abelPreimage_obj_iff_forall_holds i rfl θ W

/-- The open subscheme `Z = Pic^C ×_P Div^θ_X` of `D` represents `Pic^C ×_P Div^θ_X`, through
the composite with its inclusion into `D`; the factorization criterion is the openness. -/
example {T : Scheme.LocallyNoetherianOver (Spec (CommRingCat.of A))}
    (z : T ⟶ C.abelPreimageOver E) (a : T ⟶ D) :
    Nonempty ((restrictSubfunctor (Scheme.locallyNoetherianOver _)
        (C.abelPreimage i rfl θ)).toFunctor.RepresentableBy (C.abelPreimageOver E)) ∧
      ((C.abelPreimageRepresentableBy E).homEquiv z).1 = E.homEquiv (z ≫ C.abelPreimageι E) ∧
      (E.homEquiv a ∈ (C.abelPreimage i rfl θ).obj (op T.obj) ↔
        a.hom.left ⁻¹ᵁ C.opens (universalFppfAbelClass E) = ⊤) ∧
      IsOpenImmersion (C.abelPreimageι E).hom.left :=
  ⟨⟨C.abelPreimageRepresentableBy E⟩, C.abelPreimageRepresentableBy_homEquiv_coe E z,
    C.homEquiv_mem_abelPreimage_iff E a, inferInstance⟩

/-- The universal Abel class on `Z` lies in `Pic^C`, and it pulls back to the Abel class of the
divisor classified by a morphism to `Z`. -/
example {T : Scheme.LocallyNoetherianOver (Spec (CommRingCat.of A))}
    (z : T ⟶ C.abelPreimageOver E) :
    C.abelPreimageFppfAbelClass E ∈ C.subfunctor.obj (op (C.abelPreimageOver E).obj) ∧
      (fppfPicardSheaf (i ≫ toSpec A ι)).obj.map z.hom.op (C.abelPreimageFppfAbelClass E) =
        fppfAbelClass _ ((C.abelPreimageRepresentableBy E).homEquiv z).1.1
          ((C.abelPreimageRepresentableBy E).homEquiv z).1.2.isRelativeEffectiveCartier :=
  ⟨C.abelPreimageFppfAbelClass_mem_subfunctor E,
    C.fppfPicardSheaf_map_abelPreimageFppfAbelClass E z⟩

/-- The universal Abel class on `Z` is the Abel class of the universal divisor of `Z`. -/
example : C.abelPreimageFppfAbelClass E =
    fppfAbelClass _ ((C.abelPreimageRepresentableBy E).homEquiv (𝟙 _)).1.1
      ((C.abelPreimageRepresentableBy E).homEquiv (𝟙 _)).1.2.isRelativeEffectiveCartier :=
  C.abelPreimageFppfAbelClass_eq E

/-- `Z` is H-quasi-projective and Noetherian over a Noetherian ring when `D` is
H-quasi-projective. -/
example [IsNoetherianRing A] [IsHQuasiProjective D.obj.hom] :
    IsHQuasiProjective (C.abelPreimageOver E).obj.hom ∧
      IsNoetherian (C.abelPreimageOver E).obj.left :=
  ⟨inferInstance, inferInstance⟩

/-- For the representation of `Div^θ_X` by the open divisor locus `divisorSchemeOver E'` of a
representing scheme `H` of `Hilb^θ_X`, `Z` is H-quasi-projective and Noetherian when `H` is
H-quasi-projective. -/
example [Finite ι] [IsNoetherianRing A] [Flat (i ≫ toSpec A ι)]
    {H : Scheme.LocallyNoetherianOver (Spec (CommRingCat.of A))}
    (E' : (locallyNoetherianImmersedHilbertFunctor i rfl θ).RepresentableBy H)
    [IsHQuasiProjective H.obj.hom] :
    IsHQuasiProjective
        (C.abelPreimageOver (locallyNoetherianRelativeDivisorFunctorRepresentableBy E')).obj.hom ∧
      IsNoetherian
        (C.abelPreimageOver (locallyNoetherianRelativeDivisorFunctorRepresentableBy E')).obj.left :=
  ⟨inferInstance, inferInstance⟩

/--
info: 'AlgebraicGeometry.ProjectiveSpace.relativeDivisorFunctor_map_coe_eq_comap_familyScheme_map' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms relativeDivisorFunctor_map_coe_eq_comap_familyScheme_map

/--
info: 'AlgebraicGeometry.Scheme.RelativePicard.classOf_eq_abelClass_iff' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms classOf_eq_abelClass_iff

/--
info: 'AlgebraicGeometry.Scheme.RelativePicard.divisorFppfAbelMap' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms divisorFppfAbelMap

/--
info: 'AlgebraicGeometry.Scheme.RelativePicard.fppfPicardSheaf_map_universalFppfAbelClass' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms fppfPicardSheaf_map_universalFppfAbelClass

/--
info: 'AlgebraicGeometry.Scheme.RelativePicard.FiberCondition.abelPreimageRepresentableBy' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms FiberCondition.abelPreimageRepresentableBy

/--
info: 'AlgebraicGeometry.Scheme.RelativePicard.FiberCondition.fppfPicardSheaf_map_abelPreimageFppfAbelClass' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms FiberCondition.fppfPicardSheaf_map_abelPreimageFppfAbelClass

/--
info: 'AlgebraicGeometry.Scheme.RelativePicard.FiberCondition.isHQuasiProjective_abelPreimageOver_hom' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms FiberCondition.isHQuasiProjective_abelPreimageOver_hom

end AglibTest.AbelDivisor
