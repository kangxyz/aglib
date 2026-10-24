/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.HilbertScheme.Divisor.Functor
public import Aglib.AlgebraicGeometry.Picard.Abel.Basic
public import Aglib.AlgebraicGeometry.Picard.FiberCondition.OpenSubfunctor
public import Aglib.AlgebraicGeometry.ProjectiveSpace.QuasiProjective
public import Aglib.AlgebraicGeometry.Sites.OverRepresentability.OpenSubscheme

/-!
# The Abel map of `Div^θ_X` and the preimages of the fibre-condition subsheaves

Let `A` be a ring, `i : X ⟶ P^n_A = ProjectiveSpace A ι` a preimmersion over `S = Spec A`
(`hi : i ≫ toSpec A ι = πX`), for example a closed immersion, and `θ ∈ ℚ[X]`. Write
`Div^θ_X = relativeDivisorFunctor i hi θ` for the functor of relative effective Cartier divisors of
`X ×_S T` over `T` with fibre Hilbert polynomial `θ` (`HilbertScheme/Divisor/Functor`), and
`P = Pic_{X/S,(fppf)}` (`fppfPicardSheaf πX`).

* `relativeDivisorFunctor_map_coe_eq_comap_familyScheme_map`: `Div^θ_X` pulls divisors back along
  the maps `(RelativePicard.familyScheme πX).map f`, the maps along which
  `familyPicardFunctor πX` pulls back line-bundle classes.
* `classOf_eq_abelClass_iff`: for a relative effective Cartier divisor `D ⊆ X ×_S T` and a line
  bundle `L` on `X ×_S T`, `[L]` is the Abel class `−[I_D] = [𝒪(D)]` if and only if `L^∨ ≅ I_D`
  (Kleiman, *The Picard scheme*, arXiv:math/0504020v1, 3.1, p. 22: "`𝒪_X(−D) = I`").
* `divisorAbelMap i hi θ`: **the Abel map** `D ↦ [𝒪_{X_T}(D)] = −[I_D]` on `Div^θ_X`, with
  values in the absolute Picard functor `Pic_X`. Kleiman's Abel map `Div_{X/S} ⟶ Pic_{X/S}`
  (Def. 4.6, p. 27; his `Pic_{X/S}` is `P_{X/S}` here), restricted to `Div^θ_X`, is its
  composite with `Pic_X ⟶ P_{X/S}`. It is a natural transformation from `Div^θ_X` lifted to
  `Type (u + 1)` by `uliftFunctor`, because Picard groups of `u`-schemes live in `Type (u + 1)`;
  naturality is `familyPicardFunctor_map_abelClass`. `divisorFppfAbelMap i hi θ` is its
  composite with the class map `Pic_X ⟶ P_{X/S} ⟶ P`, Kleiman's Abel map with its target
  replaced by an associated sheaf (Def. 4.6: "The target `Pic_{X/S}` may be replaced by any of
  its associated sheaves"); it sends `D` to `fppfAbelClass πX D`.
* For a representation `E` of `Div^θ_X` on locally Noetherian test schemes by `D`, with universal
  divisor `W = (E.homEquiv (𝟙 D)).1`: `universalFppfAbelClass E ∈ P(D)` is the class of `𝒪(W)`,
  and for `a : T ⟶ D` its pullback is the class of the divisor `E.homEquiv a` that `a` classifies
  (`fppfPicardSheaf_map_universalFppfAbelClass`). So the Abel map of schemes `D ⟶ P` is the Yoneda
  map of `universalFppfAbelClass E`.
* For a fibre condition `C` (`Picard/FiberCondition/Subsheaf`), `C.abelPreimage i hi θ` is the
  subfunctor of `Div^θ_X` of the divisors whose class lies in `Pic^C = C.subfunctor`, that is,
  `Pic^C ×_P Div^θ_X`; its points are the divisors whose Abel class satisfies `C` at every point
  (`mem_abelPreimage_obj_iff_forall_holds`). On locally Noetherian test schemes it is represented
  by the open subscheme `C.abelPreimageOver E` of `D` cut out by `C` at
  `universalFppfAbelClass E` (`C.opens`, `Picard/FiberCondition/OpenSubfunctor`), through
  `Scheme.LocalRepresentability.representableByRestrictOpens`
  (`abelPreimageRepresentableBy`). The restriction `abelPreimageFppfAbelClass` of the universal
  class to it lies in `Pic^C`, is the class of the universal divisor of the open subscheme
  (`abelPreimageFppfAbelClass_eq`), and pulls back to the class of the classified divisor. If `D` is
  H-quasi-projective over a Noetherian `A`, so is the open subscheme, which is then Noetherian
  (`isHQuasiProjective_abelPreimageOver_hom`, `isNoetherian_abelPreimageOver`).

The last item is Kleiman's "Form the product `P_0^{φ0} ×_P Div_{X/S}`. It is a scheme `Z`, in fact,
an open subscheme of `Div_{X/S}`" (proof of Thm 4.8, p. 30), for an arbitrary fibre condition and
the divisors with fibre Hilbert polynomial `θ`; the stratum of that proof, with `θ = ψ − φ0`, is in
`Picard/Strata/DivisorLocus`. The test schemes are locally Noetherian because the openness of
`C.opens` is proved over locally Noetherian bases.
-/

@[expose] public section

noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite
open scoped Polynomial

universe u

namespace AlgebraicGeometry

namespace ProjectiveSpace

variable {ι : Type u} {A : Type u} [CommRing A] {X : Scheme.{u}}
  {πX : X ⟶ Spec (CommRingCat.of A)} (i : X ⟶ ProjectiveSpace A ι) (hi : i ≫ toSpec A ι = πX)
  [IsPreimmersion i] (θ : ℚ[X])

/-- **The maps of `Div^θ_X` are those of the family** `T ↦ X ×_{Spec A} T`: for `f : T ⟶ T'` in
`(Over (Spec A))ᵒᵖ`, `Div^θ_X` pulls a divisor back along
`(RelativePicard.familyScheme πX).map f.unop`, the map along which `familyPicardFunctor πX` pulls
back line-bundle classes. -/
theorem relativeDivisorFunctor_map_coe_eq_comap_familyScheme_map
    {T T' : (Over (Spec (CommRingCat.of A)))ᵒᵖ} (f : T ⟶ T')
    (D : (relativeDivisorFunctor i hi θ).obj T) :
    ((relativeDivisorFunctor i hi θ).map f D).1 =
      D.1.comap ((Scheme.RelativePicard.familyScheme πX).map f.unop) :=
  rfl

end ProjectiveSpace

namespace Scheme.RelativePicard

open Modules.Invertible ProjectiveSpace

section Bridge

variable {S X : Scheme.{u}} (p : X ⟶ S) {T : Over S} {D : (pullback p T.hom).IdealSheafData}
  (hD : Hom.IsRelativeEffectiveCartier D.subschemeι (pullback.snd p T.hom))

/-- **A line bundle represents the Abel class exactly when its dual is the ideal**: for a relative
effective Cartier divisor `D ⊆ X ×_S T` over `T` and a line bundle `L` on `X ×_S T`,
`[L] = abelClass p D hD = −[I_D]` if and only if `L^∨ ≅ I_D` (Kleiman, arXiv:math/0504020v1, 3.1,
p. 22: "`𝒪_X(−D) = I`"). -/
theorem classOf_eq_abelClass_iff (L : LineBundle (pullback p T.hom)) :
    classOf _ L = abelClass p D hD ↔
      Nonempty ((dualLineBundle _ L).val ≅ Hom.idealModule D.subschemeι) := by
  rw [abelClass, ← neg_eq_iff_eq_neg, ← classOf_dual]
  exact class_eq_iff _ _ _

/-- **The dual of a representative of the Abel class is the ideal of the divisor**: if
`[L] = abelClass p D hD`, then `L^∨ ≅ I_D`. -/
theorem nonempty_dualLineBundle_iso_idealModule_of_classOf_eq_abelClass
    {L : LineBundle (pullback p T.hom)} (h : classOf _ L = abelClass p D hD) :
    Nonempty ((dualLineBundle _ L).val ≅ Hom.idealModule D.subschemeι) :=
  (classOf_eq_abelClass_iff p hD L).mp h

end Bridge

section AbelMap

variable {ι : Type u} {A : Type u} [CommRing A] {X : Scheme.{u}}
  {πX : X ⟶ Spec (CommRingCat.of A)} (i : X ⟶ ProjectiveSpace A ι) (hi : i ≫ toSpec A ι = πX)
  [IsPreimmersion i] (θ : ℚ[X])

/-- **The Abel map of `Div^θ_X`**, with values in the absolute Picard functor: the natural
transformation sending a relative effective Cartier divisor `D ⊆ X ×_{Spec A} T` with fibre
Hilbert polynomial `θ` to its Abel class `[𝒪_{X_T}(D)] = −[I_D] ∈ Pic(X ×_{Spec A} T)`. Its
composite with `Pic(X ×_{Spec A} T) ⟶ P_{X/S}(T)` is Kleiman's Abel map (arXiv:math/0504020v1,
Def. 4.6, p. 27) on `Div^θ_X`. The divisor functor is lifted from `Type u` to `Type (u + 1)`, the
universe of the Picard groups. -/
def divisorAbelMap : relativeDivisorFunctor i hi θ ⋙ uliftFunctor.{u + 1} ⟶
    familyPicardFunctor πX ⋙ CategoryTheory.forget AddCommGrpCat.{u + 1} where
  app T := TypeCat.ofHom fun D : ULift.{u + 1} ((relativeDivisorFunctor i hi θ).obj T) =>
    abelClass πX D.down.1 D.down.2.isRelativeEffectiveCartier
  naturality _ _ f := ConcreteCategory.hom_ext _ _ fun D =>
    (familyPicardFunctor_map_abelClass πX f.unop D.down.1
      D.down.2.isRelativeEffectiveCartier).symm

theorem divisorAbelMap_app_apply (T : (Over (Spec (CommRingCat.of A)))ᵒᵖ)
    (D : (relativeDivisorFunctor i hi θ).obj T) :
    (divisorAbelMap i hi θ).app T (ULift.up D) =
      abelClass πX (T := T.unop) D.1 D.2.isRelativeEffectiveCartier :=
  rfl

/-- **The Abel map to `Pic_{X/S,(fppf)}`**: the composite of `divisorAbelMap` with the class map
`Pic(X ×_S T) ⟶ P_{X/S}(T) ⟶ Pic_{X/S,(fppf)}(T)` (Kleiman, arXiv:math/0504020v1, Def. 4.6,
p. 27: the target may be replaced by any of its associated sheaves). -/
def divisorFppfAbelMap : relativeDivisorFunctor i hi θ ⋙ uliftFunctor.{u + 1} ⟶
    (fppfPicardSheaf πX).obj ⋙ CategoryTheory.forget AddCommGrpCat.{u + 1} :=
  divisorAbelMap i hi θ ≫ Functor.whiskerRight (quotientProjection πX ≫ toFppfPicardSheaf πX)
    (CategoryTheory.forget AddCommGrpCat.{u + 1})

/-- The fppf Abel map sends a divisor to its fppf Abel class `fppfAbelClass`. -/
theorem divisorFppfAbelMap_app_apply (T : (Over (Spec (CommRingCat.of A)))ᵒᵖ)
    (D : (relativeDivisorFunctor i hi θ).obj T) :
    (divisorFppfAbelMap i hi θ).app T (ULift.up D) =
      fppfAbelClass πX (T := T.unop) D.1 D.2.isRelativeEffectiveCartier :=
  rfl

variable {i hi θ} {D : Scheme.LocallyNoetherianOver (Spec (CommRingCat.of A))}
  (E : (locallyNoetherianRelativeDivisorFunctor i hi θ).RepresentableBy D)

/-- **The Abel class of the universal divisor**: for a representation `E` of `Div^θ_X` on locally
Noetherian test schemes by `D`, the class in `Pic_{X/S,(fppf)}(D)` of `𝒪(W)` for the universal
divisor `W = (E.homEquiv (𝟙 D)).1`. -/
def universalFppfAbelClass : (fppfPicardSheaf πX).obj.obj (op D.obj) :=
  fppfAbelClass πX (E.homEquiv (𝟙 D)).1 (E.homEquiv (𝟙 D)).2.isRelativeEffectiveCartier

/-- The universal Abel class is the value of the fppf Abel map at the universal divisor. -/
theorem universalFppfAbelClass_eq_divisorFppfAbelMap_app :
    universalFppfAbelClass E =
      (divisorFppfAbelMap i hi θ).app (op D.obj) (ULift.up (E.homEquiv (𝟙 D))) :=
  rfl

/-- **Pullbacks of the universal Abel class**: for a morphism `a : T ⟶ D` of locally Noetherian
test schemes, the pullback of `universalFppfAbelClass E` along `a` is the fppf Abel class of the
divisor `E.homEquiv a` classified by `a`. So the Abel map of schemes `D ⟶ Pic_{X/S,(fppf)}` is the
Yoneda map of `universalFppfAbelClass E`. -/
theorem fppfPicardSheaf_map_universalFppfAbelClass
    {T : Scheme.LocallyNoetherianOver (Spec (CommRingCat.of A))} (a : T ⟶ D) :
    (fppfPicardSheaf πX).obj.map a.hom.op (universalFppfAbelClass E) =
      fppfAbelClass πX (T := T.obj) (E.homEquiv a).1
        (E.homEquiv a).2.isRelativeEffectiveCartier := by
  rw [E.homEquiv_eq a]
  exact fppfPicardSheaf_map_fppfAbelClass πX a.hom _ _

end AbelMap

namespace FiberCondition

variable {ι : Type u} {A : Type u} [CommRing A] {X : Scheme.{u}}
  {πX : X ⟶ Spec (CommRingCat.of A)} {i : X ⟶ ProjectiveSpace A ι} {hi : i ≫ toSpec A ι = πX}
  [IsPreimmersion i] {θ : ℚ[X]} (C : FiberCondition πX)

variable (i hi θ) in
/-- **`Pic^C ×_P Div^θ_X`**: the subfunctor of `Div^θ_X` of the divisors whose fppf Abel class lies
in the subsheaf `Pic^C = C.subfunctor` of `Pic_{X/S,(fppf)}`, the preimage of `Pic^C` under the
fppf Abel map `divisorFppfAbelMap` (Kleiman, arXiv:math/0504020v1, proof of Thm 4.8, p. 30, for
the stratum `P_0^{φ0}`). Base change preserves it by the naturality of the fppf Abel class
(`fppfPicardSheaf_map_fppfAbelClass`). -/
def abelPreimage : Subfunctor (relativeDivisorFunctor i hi θ) where
  obj T := {D | fppfAbelClass πX (T := T.unop) D.1 D.2.isRelativeEffectiveCartier ∈
    C.subfunctor.obj T}
  map {T T'} f D hD := by
    have h := C.subfunctor.map f
      (show fppfAbelClass πX (T := T.unop) D.1 D.2.isRelativeEffectiveCartier ∈
        C.subfunctor.obj T from hD)
    change (fppfPicardSheaf πX).obj.map f.unop.op
      (fppfAbelClass πX D.1 D.2.isRelativeEffectiveCartier) ∈ C.subfunctor.obj T' at h
    rw [fppfPicardSheaf_map_fppfAbelClass] at h
    exact h

variable (i hi θ) in
/-- A divisor lies in `C.abelPreimage` if and only if its fppf Abel class lies in `Pic^C`. -/
theorem mem_abelPreimage_obj_iff {T : Over (Spec (CommRingCat.of A))}
    (D : (relativeDivisorFunctor i hi θ).obj (op T)) :
    D ∈ (C.abelPreimage i hi θ).obj (op T) ↔
      fppfAbelClass πX (T := T) D.1 D.2.isRelativeEffectiveCartier ∈ C.subfunctor.obj (op T) :=
  Iff.rfl

variable (i hi θ) in
/-- **Pointwise description of `Pic^C ×_P Div^θ_X`**: a divisor lies in `C.abelPreimage` if and
only if its Abel class `−[I_D]` satisfies `C` at every point of the base. -/
theorem mem_abelPreimage_obj_iff_forall_holds {T : Over (Spec (CommRingCat.of A))}
    (D : (relativeDivisorFunctor i hi θ).obj (op T)) :
    D ∈ (C.abelPreimage i hi θ).obj (op T) ↔
      ∀ t : T.left, C.Holds T (abelClass πX D.1 D.2.isRelativeEffectiveCartier) t :=
  C.app_mem_subfunctor_iff (abelClass πX D.1 D.2.isRelativeEffectiveCartier)

variable {D : Scheme.LocallyNoetherianOver (Spec (CommRingCat.of A))}
  (E : (locallyNoetherianRelativeDivisorFunctor i hi θ).RepresentableBy D)

/-- **The open subscheme `Z = Pic^C ×_P Div^θ_X`** of the representing scheme `D` of `Div^θ_X`, as
a locally Noetherian test scheme: the open `C.opens (universalFppfAbelClass E)` of the points of
`D` where the universal Abel class satisfies `C` (Kleiman, arXiv:math/0504020v1, proof of Thm 4.8,
p. 30: "It is a scheme `Z`, in fact, an open subscheme of `Div_{X/S}`"). -/
def abelPreimageOver : Scheme.LocallyNoetherianOver (Spec (CommRingCat.of A)) :=
  LocalRepresentability.restrictOpens D (C.opens (universalFppfAbelClass E))

/-- The open immersion of `C.abelPreimageOver E` into the representing scheme `D` of `Div^θ_X`, as
a morphism of locally Noetherian test schemes. -/
def abelPreimageι : C.abelPreimageOver E ⟶ D :=
  LocalRepresentability.restrictOpensι D (C.opens (universalFppfAbelClass E))

theorem abelPreimageι_hom_left :
    (C.abelPreimageι E).hom.left = (C.opens (universalFppfAbelClass E)).ι :=
  rfl

instance isOpenImmersion_abelPreimageι_hom_left : IsOpenImmersion (C.abelPreimageι E).hom.left :=
  inferInstanceAs (IsOpenImmersion (C.opens (universalFppfAbelClass E)).ι)

theorem abelPreimageOver_hom :
    (C.abelPreimageOver E).obj.hom = (C.abelPreimageι E).hom.left ≫ D.obj.hom :=
  rfl

/-- **The factorization criterion**: a morphism `a : T ⟶ D` from a locally Noetherian test scheme
classifies a point of `Pic^C ×_P Div^θ_X` if and only if it factors through the open
`C.opens (universalFppfAbelClass E)`. -/
theorem homEquiv_mem_abelPreimage_iff
    {T : Scheme.LocallyNoetherianOver (Spec (CommRingCat.of A))} (a : T ⟶ D) :
    E.homEquiv a ∈ (C.abelPreimage i hi θ).obj (op T.obj) ↔
      a.hom.left ⁻¹ᵁ C.opens (universalFppfAbelClass E) = ⊤ := by
  rw [mem_abelPreimage_obj_iff, ← fppfPicardSheaf_map_universalFppfAbelClass]
  exact C.map_mem_subfunctor_iff _ a.hom

/-- **`Z` represents `Pic^C ×_P Div^θ_X`** on locally Noetherian test schemes (Kleiman,
arXiv:math/0504020v1, proof of Thm 4.8, p. 30): the open subscheme `C.abelPreimageOver E` of the
representing scheme `D` of `Div^θ_X` represents the divisors whose fppf Abel class lies in
`Pic^C`; a morphism `z : T ⟶ C.abelPreimageOver E` corresponds to the divisor classified by its
composite with `C.abelPreimageι E` (`abelPreimageRepresentableBy_homEquiv_coe`). -/
def abelPreimageRepresentableBy :
    (LocalRepresentability.restrictSubfunctor (Scheme.locallyNoetherianOver _)
      (C.abelPreimage i hi θ)).toFunctor.RepresentableBy (C.abelPreimageOver E) :=
  LocalRepresentability.representableByRestrictOpens E _ _ fun _ a =>
    C.homEquiv_mem_abelPreimage_iff E a

theorem abelPreimageRepresentableBy_homEquiv_coe
    {T : Scheme.LocallyNoetherianOver (Spec (CommRingCat.of A))}
    (z : T ⟶ C.abelPreimageOver E) :
    ((C.abelPreimageRepresentableBy E).homEquiv z).1 = E.homEquiv (z ≫ C.abelPreimageι E) :=
  rfl

/-- **The universal Abel class on `Z`**: the restriction of `universalFppfAbelClass E` to the open
subscheme `C.abelPreimageOver E`. -/
def abelPreimageFppfAbelClass : (fppfPicardSheaf πX).obj.obj (op (C.abelPreimageOver E).obj) :=
  (fppfPicardSheaf πX).obj.map (C.abelPreimageι E).hom.op (universalFppfAbelClass E)

/-- The universal Abel class on `Z` lies in `Pic^C`. -/
theorem abelPreimageFppfAbelClass_mem_subfunctor :
    C.abelPreimageFppfAbelClass E ∈ C.subfunctor.obj (op (C.abelPreimageOver E).obj) := by
  rw [abelPreimageFppfAbelClass, C.map_mem_subfunctor_iff]
  exact Scheme.Opens.ι_preimage_self _

/-- **Pullbacks of the universal Abel class on `Z`**: for `z : T ⟶ C.abelPreimageOver E`, the
pullback of `abelPreimageFppfAbelClass` along `z` is the fppf Abel class of the divisor that `z`
classifies. -/
theorem fppfPicardSheaf_map_abelPreimageFppfAbelClass
    {T : Scheme.LocallyNoetherianOver (Spec (CommRingCat.of A))}
    (z : T ⟶ C.abelPreimageOver E) :
    (fppfPicardSheaf πX).obj.map z.hom.op (C.abelPreimageFppfAbelClass E) =
      fppfAbelClass πX (T := T.obj) ((C.abelPreimageRepresentableBy E).homEquiv z).1.1
        ((C.abelPreimageRepresentableBy E).homEquiv z).1.2.isRelativeEffectiveCartier := by
  rw [abelPreimageFppfAbelClass, ← ConcreteCategory.comp_apply, ← Functor.map_comp, ← op_comp]
  exact fppfPicardSheaf_map_universalFppfAbelClass E (z ≫ C.abelPreimageι E)

/-- **The universal Abel class on `Z` is the Abel class of its universal divisor** (Kleiman,
arXiv:math/0504020v1, proof of Thm 4.8, p. 30: "the map `α : Z → P_0^{φ0}` is defined by the
invertible sheaf associated to the universal relative effective divisor on `X_Z/Z`"). -/
theorem abelPreimageFppfAbelClass_eq :
    C.abelPreimageFppfAbelClass E =
      fppfAbelClass πX (T := (C.abelPreimageOver E).obj)
        ((C.abelPreimageRepresentableBy E).homEquiv (𝟙 _)).1.1
        ((C.abelPreimageRepresentableBy E).homEquiv (𝟙 _)).1.2.isRelativeEffectiveCartier := by
  have h := C.fppfPicardSheaf_map_abelPreimageFppfAbelClass E (𝟙 _)
  change (fppfPicardSheaf πX).obj.map (𝟙 (op (C.abelPreimageOver E).obj))
    (C.abelPreimageFppfAbelClass E) = _ at h
  rwa [CategoryTheory.Functor.map_id, ConcreteCategory.id_apply] at h

/-- **`Z` is H-quasi-projective** over a Noetherian ring when the representing scheme of
`Div^θ_X` is: an open immersion into an H-quasi-projective scheme over a Noetherian ring
(`IsHQuasiProjective.comp_of_isImmersion`; Kleiman, arXiv:math/0504020v1, proof of Thm 4.8,
p. 30: "Hence `Z` is quasi-projective"). -/
instance isHQuasiProjective_abelPreimageOver_hom [IsNoetherianRing A]
    [IsHQuasiProjective D.obj.hom] : IsHQuasiProjective (C.abelPreimageOver E).obj.hom :=
  IsHQuasiProjective.comp_of_isImmersion (C.abelPreimageι E).hom.left D.obj.hom

/-- **`Z` is Noetherian** when the representing scheme of `Div^θ_X` is H-quasi-projective over a
Noetherian ring. -/
instance isNoetherian_abelPreimageOver [IsNoetherianRing A] [IsHQuasiProjective D.obj.hom] :
    IsNoetherian (C.abelPreimageOver E).obj.left :=
  IsHQuasiProjective.isNoetherian (C.abelPreimageOver E).obj.hom

end FiberCondition

end Scheme.RelativePicard

end AlgebraicGeometry
