/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.Algebra.Homology.DerivedCategory.Ext.Cokernel
public import Aglib.Algebra.Category.ModuleCat.ChangeOfRings.Linear
public import Aglib.Algebra.Category.ModuleCat.ChangeOfRings.Flat
public import Aglib.Algebra.Category.ModuleCat.Localization.ScalarExtension
public import Mathlib.Algebra.Category.ModuleCat.ChangeOfRingsExact
public import Mathlib.Algebra.Category.ModuleCat.Projective
public import Mathlib.Algebra.Module.FinitePresentation
public import Mathlib.Algebra.Module.LocalizedModule.Submodule
public import Mathlib.Algebra.Homology.DerivedCategory.Ext.MapAdjunction

/-!
# Localization of the original finite-source Ext map

For a finite source over a Noetherian ring, original Yoneda postcomposition
by a coefficient localization map is localizing in every degree. Finite free
covers and their finite kernels supply actual resolution segments. Degree
one uses the original Hom cokernel; positive dimension shifts use the
original unsigned Yoneda connecting maps.

The native scalar-adjunction unit then identifies this calculation with the
same exact-functor `mapExtLinearMap`. Coefficients are arbitrary, and neither
locality, regularity, finite projective dimension nor a regular-sequence
presentation is assumed. The original source-endomorphism action is retained.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian
open scoped ModuleCat.Algebra

universe u w z

namespace IsLocalizedModule

/-- The actual coefficient postcomposition localizes Hom from a finitely presented source. -/
private theorem compRight_of_finitePresentation
    {R P N N' : Type*} [CommRing R]
    [AddCommGroup P] [Module R P] [Module.FinitePresentation R P]
    [AddCommGroup N] [Module R N] [AddCommGroup N'] [Module R N']
    (T : Submonoid R) (g : N →ₗ[R] N') [IsLocalizedModule T g] :
    IsLocalizedModule T (LinearMap.compRight R g : (P →ₗ[R] N) →ₗ[R] (P →ₗ[R] N')) := by
  constructor
  · intro s
    rw [Module.End.isUnit_iff]
    have hs := (Module.End.isUnit_iff _).mp (IsLocalizedModule.map_units g s)
    constructor
    · exact fun _ _ e => LinearMap.ext fun p => hs.1 (LinearMap.congr_fun e p)
    · intro f
      refine ⟨((IsLocalizedModule.map_units g s).unit⁻¹).1 ∘ₗ f, ?_⟩
      ext p
      exact Module.End.isUnit_apply_inv_apply_of_isUnit
        (IsLocalizedModule.map_units g s) (f p)
  · intro f
    obtain ⟨f', s, hs⟩ := Module.FinitePresentation.exists_lift_of_isLocalizedModule T g f
    exact ⟨⟨f', s⟩, hs.symm⟩
  · intro f₁ f₂ h
    exact Module.Finite.exists_smul_of_comp_eq_of_isLocalizedModule T g f₁ f₂ h

end IsLocalizedModule

namespace IsLocalizedModule

variable {R X Y X' Y' : Type*} [CommRing R]
  [AddCommGroup X] [Module R X] [AddCommGroup Y] [Module R Y]
  [AddCommGroup X'] [Module R X'] [AddCommGroup Y'] [Module R Y']
  (f : X →ₗ[R] X') (g : Y →ₗ[R] Y') (a : X →ₗ[R] Y) (a' : X' →ₗ[R] Y')
  (h : g.comp a = a'.comp f)

/-- The original map on cokernel representatives in a commuting linear square. -/
private def rangeQuotientMap : (Y ⧸ LinearMap.range a) →ₗ[R] (Y' ⧸ LinearMap.range a') :=
  (LinearMap.range a).mapQ (LinearMap.range a') g (by
    rintro y ⟨x, rfl⟩
    exact ⟨f x, (LinearMap.congr_fun h x).symm⟩)

/-- The map retains the original coefficient localization on every quotient representative. -/
private theorem rangeQuotientMap_mk (y : Y) :
    rangeQuotientMap f g a a' h (Submodule.Quotient.mk y) =
      Submodule.Quotient.mk (g y) := rfl

/-- The actual induced cokernel map localizes whenever the two vertical maps do. -/
private theorem rangeQuotientMap_isLocalized (T : Submonoid R)
    [IsLocalizedModule T f] [IsLocalizedModule T g] :
    IsLocalizedModule T (rangeQuotientMap f g a a' h) := by
  let A := Localization T
  let : Module A X' := IsLocalizedModule.module T f
  let : IsScalarTower R A X' := IsLocalizedModule.isScalarTower_module T f
  let : Module A Y' := IsLocalizedModule.module T g
  let : IsScalarTower R A Y' := IsLocalizedModule.isScalarTower_module T g
  have hmap : IsLocalizedModule.map T f g a = a' := by
    apply IsLocalizedModule.linearMap_ext T f g
    rw [IsLocalizedModule.map_comp]
    exact h
  let P : Submodule A Y' := (LinearMap.range a).localized' A T g
  have hP : P.restrictScalars R = LinearMap.range a' := by
    dsimp only [P]
    rw [Submodule.restrictScalars_localized',
      ← f.range_localizedMap_eq_localized₀_range T g a, hmap]
  let e : (Y' ⧸ P) ≃ₗ[R] Y' ⧸ LinearMap.range a' :=
    (Submodule.Quotient.restrictScalarsEquiv R P).symm.trans
      (Submodule.quotEquivOfEq _ _ hP)
  let q := (LinearMap.range a).toLocalizedQuotient' A T g
  let : IsLocalizedModule T q := by dsimp only [q]; infer_instance
  have he : rangeQuotientMap f g a a' h = e.toLinearMap.comp q := by
    apply LinearMap.ext
    intro x
    obtain ⟨y, rfl⟩ := Submodule.mkQ_surjective (LinearMap.range a) x
    change Submodule.Quotient.mk (g y) = e (q (Submodule.Quotient.mk y))
    simp [e, q]
  rw [he]
  exact IsLocalizedModule.of_linearEquiv T q e

end IsLocalizedModule

namespace CategoryTheory.ShortComplex.ShortExact

variable {R : Type u} [CommRing R] [HasExt.{w} (ModuleCat.{u} R)]
  {S : ShortComplex (ModuleCat.{u} R)} (hS : S.ShortExact) [Projective S.X₂]

/-- Positive-degree dimension shifting is the original unsigned Yoneda connecting map. -/
private def finiteSourceExtShift (N : ModuleCat.{u} R) (n : ℕ) :
    Ext.{w} S.X₁ N (n + 1) ≃ₗ[R] Ext.{w} S.X₃ N (n + 2) :=
  LinearEquiv.ofBijective
    (hS.extClass.precompOfLinear R N (by omega : 1 + (n + 1) = n + 2)) (by
      constructor
      · apply (injective_iff_map_eq_zero _).mpr
        intro x hx
        obtain ⟨y, hy⟩ := Ext.contravariant_sequence_exact₁ hS N x
          (n₁ := n + 2) (by omega) hx
        rw [Ext.eq_zero_of_projective y, Ext.comp_zero] at hy
        exact hy.symm
      · intro x
        exact Ext.contravariant_sequence_exact₃ hS N x
          (Ext.eq_zero_of_projective _) (by omega))

/-- The actual connecting isomorphism commutes with original coefficient postcomposition. -/
private theorem finiteSourceExtShift_postcomp
    {N N' : ModuleCat.{u} R} (g : N ⟶ N') (n : ℕ) (x : Ext.{w} S.X₁ N (n + 1)) :
    hS.finiteSourceExtShift N' n (x.comp (Ext.mk₀ g) (add_zero _)) =
      (hS.finiteSourceExtShift N n x).comp (Ext.mk₀ g) (add_zero _) := by
  exact (Ext.comp_assoc_of_third_deg_zero hS.extClass x (Ext.mk₀ g) (by omega)).symm

/-- The degree-one cokernel map retains the same Yoneda class under coefficient localization. -/
private theorem homCokernelExtOneLinearEquiv_postcomp_mk
    {N N' : ModuleCat.{u} R} (g : N ⟶ N') (f : S.X₁ ⟶ N) :
    hS.homCokernelExtOneLinearEquiv (R := R) N' (Submodule.Quotient.mk (f ≫ g)) =
      (hS.homCokernelExtOneLinearEquiv (R := R) N (Submodule.Quotient.mk f)).comp
        (Ext.mk₀ g) (add_zero 1) := by
  rw [homCokernelExtOneLinearEquiv_mk, homCokernelExtOneLinearEquiv_mk,
    Ext.comp_assoc_of_third_deg_zero, Ext.mk₀_comp_mk₀]

end CategoryTheory.ShortComplex.ShortExact

namespace CategoryTheory.Adjunction

variable {C D : Type*} [Category* C] [Category* D] [Abelian C] [Abelian D]
  [HasExt.{w} C] [HasExt.{z} D]
  {F : C ⥤ D} {G : D ⥤ C} [F.Additive] [G.Additive]
  [PreservesFiniteLimits F] [PreservesFiniteColimits F]
  [PreservesFiniteLimits G] [PreservesFiniteColimits G]

/-- The original exact-functor Ext map is coefficient-unit postcomposition under
the original exact adjunction. This is the required normalization of base change. -/
private theorem extEquiv_mapExactFunctor_unit_original (adj : F ⊣ G) {M N : C} {n : ℕ}
    (x : Ext.{w} M N n) :
    adj.extEquiv (x.mapExactFunctor F) =
      x.comp (Ext.mk₀ (adj.unit.app N)) (add_zero n) := by
  rw [Adjunction.extEquiv_apply, ← Ext.comp_mapExactFunctor]
  simpa only [Ext.id_mapExactFunctor] using
    (Ext.mapExactFunctor_comp_mk₀_natTransApp x adj.unit).symm

end CategoryTheory.Adjunction


namespace ModuleCat

section Coefficient

variable {R : Type u} [CommRing R] (T : Submonoid R)
  {N N' : ModuleCat.{u} R} (g : N ⟶ N') [IsLocalizedModule T g.hom]

private theorem homPostcomp_isLocalized (P : ModuleCat.{u} R)
    [Module.FinitePresentation R P] :
    IsLocalizedModule T (Linear.rightComp R P g) := by
  let q : (P →ₗ[R] N) →ₗ[R] (P →ₗ[R] N') := LinearMap.compRight R g.hom
  let e : (P ⟶ N) ≃ₗ[R] (P →ₗ[R] N) := ModuleCat.homLinearEquiv
  let e' : (P ⟶ N') ≃ₗ[R] (P →ₗ[R] N') := ModuleCat.homLinearEquiv
  let : IsLocalizedModule T q := IsLocalizedModule.compRight_of_finitePresentation T g.hom
  let : IsLocalizedModule T (q.comp e.toLinearMap) :=
    IsLocalizedModule.of_linearEquiv_right T q e
  have he : Linear.rightComp R P g = e'.symm.toLinearMap.comp (q.comp e.toLinearMap) := by
    apply LinearMap.ext
    intro f
    apply ModuleCat.hom_ext
    rfl
  rw [he]
  exact IsLocalizedModule.of_linearEquiv T (q.comp e.toLinearMap) e'.symm

variable [HasExt.{w} (ModuleCat.{u} R)]

private theorem extZeroPostcomp_isLocalized (M : ModuleCat.{u} R)
    [Module.FinitePresentation R M] :
    IsLocalizedModule T ((Ext.mk₀ g).postcompOfLinear R M (add_zero 0)) := by
  let e : Ext.{w} M N 0 ≃ₗ[R] (M ⟶ N) := Ext.linearEquiv₀
  let e' : Ext.{w} M N' 0 ≃ₗ[R] (M ⟶ N') := Ext.linearEquiv₀
  let q := Linear.rightComp R M g
  let : IsLocalizedModule T q := homPostcomp_isLocalized T g M
  let : IsLocalizedModule T (q.comp e.toLinearMap) :=
    IsLocalizedModule.of_linearEquiv_right T q e
  have hq (x : Ext.{w} M N 0) :
      e' (x.comp (Ext.mk₀ g) (add_zero 0)) = e x ≫ g := by
    apply (Ext.mk₀_bijective M N').injective
    change Ext.mk₀ (Ext.linearEquiv₀ (R := R)
        (x.comp (Ext.mk₀ g) (add_zero 0))) = Ext.mk₀ (Ext.linearEquiv₀ (R := R) x ≫ g)
    rw [Ext.mk₀_linearEquiv₀_apply, ← Ext.mk₀_comp_mk₀, Ext.mk₀_linearEquiv₀_apply]
  have he : (Ext.mk₀ g).postcompOfLinear R M (add_zero 0) =
      e'.symm.toLinearMap.comp (q.comp e.toLinearMap) := by
    apply LinearMap.ext
    intro x
    apply e'.injective
    change e' (x.comp (Ext.mk₀ g) (add_zero 0)) = e' (e'.symm (q (e x)))
    rw [LinearEquiv.apply_symm_apply]
    exact hq x
  rw [he]
  exact IsLocalizedModule.of_linearEquiv T (q.comp e.toLinearMap) e'.symm

private theorem extOnePostcomp_isLocalized
    {S : ShortComplex (ModuleCat.{u} R)} (hS : S.ShortExact) [Projective S.X₂]
    [Module.FinitePresentation R S.X₁] [Module.FinitePresentation R S.X₂] :
    IsLocalizedModule T ((Ext.mk₀ g).postcompOfLinear R S.X₃ (add_zero 1)) := by
  let a := Linear.leftComp R N S.f
  let a' := Linear.leftComp R N' S.f
  let f := Linear.rightComp R S.X₂ g
  let k := Linear.rightComp R S.X₁ g
  have hw : k.comp a = a'.comp f := by
    apply LinearMap.ext
    intro h
    exact Category.assoc S.f h g
  let q := IsLocalizedModule.rangeQuotientMap f k a a' hw
  let : IsLocalizedModule T f := homPostcomp_isLocalized T g S.X₂
  let : IsLocalizedModule T k := homPostcomp_isLocalized T g S.X₁
  let : IsLocalizedModule T q :=
    IsLocalizedModule.rangeQuotientMap_isLocalized f k a a' hw T
  let e := hS.homCokernelExtOneLinearEquiv (R := R) N
  let e' := hS.homCokernelExtOneLinearEquiv (R := R) N'
  let : IsLocalizedModule T (q.comp e.symm.toLinearMap) :=
    IsLocalizedModule.of_linearEquiv_right T q e.symm
  have he : (Ext.mk₀ g).postcompOfLinear R S.X₃ (add_zero 1) =
      e'.toLinearMap.comp (q.comp e.symm.toLinearMap) := by
    apply LinearMap.ext
    intro x
    obtain ⟨y, rfl⟩ := e.surjective x
    obtain ⟨h, rfl⟩ := Submodule.mkQ_surjective (LinearMap.range a) y
    change (e (Submodule.Quotient.mk h)).comp (Ext.mk₀ g) (add_zero 1) =
      e' (q (e.symm (e (Submodule.Quotient.mk h))))
    rw [LinearEquiv.symm_apply_apply]
    change (e (Submodule.Quotient.mk h)).comp (Ext.mk₀ g) (add_zero 1) =
      e' (IsLocalizedModule.rangeQuotientMap f k a a' hw (Submodule.Quotient.mk h))
    rw [IsLocalizedModule.rangeQuotientMap_mk]
    exact (hS.homCokernelExtOneLinearEquiv_postcomp_mk g h).symm
  rw [he]
  exact IsLocalizedModule.of_linearEquiv T (q.comp e.symm.toLinearMap) e'

omit [IsLocalizedModule T g.hom] in
private theorem extPositivePostcomp_isLocalized
    {S : ShortComplex (ModuleCat.{u} R)} (hS : S.ShortExact) [Projective S.X₂]
    (n : ℕ)
    (h : IsLocalizedModule T ((Ext.mk₀ g).postcompOfLinear R S.X₁ (add_zero (n + 1)))) :
    IsLocalizedModule T ((Ext.mk₀ g).postcompOfLinear R S.X₃ (add_zero (n + 2))) := by
  let q := (Ext.mk₀ g).postcompOfLinear R S.X₁ (add_zero (n + 1))
  let : IsLocalizedModule T q := h
  let e := hS.finiteSourceExtShift N n
  let e' := hS.finiteSourceExtShift N' n
  let : IsLocalizedModule T (q.comp e.symm.toLinearMap) :=
    IsLocalizedModule.of_linearEquiv_right T q e.symm
  have he : (Ext.mk₀ g).postcompOfLinear R S.X₃ (add_zero (n + 2)) =
      e'.toLinearMap.comp (q.comp e.symm.toLinearMap) := by
    apply LinearMap.ext
    intro x
    obtain ⟨y, rfl⟩ := e.surjective x
    change (e y).comp (Ext.mk₀ g) (add_zero (n + 2)) = e' (q (e.symm (e y)))
    rw [LinearEquiv.symm_apply_apply]
    exact (hS.finiteSourceExtShift_postcomp g n y).symm
  rw [he]
  exact IsLocalizedModule.of_linearEquiv T (q.comp e.symm.toLinearMap) e'

/-- For a finite source over a Noetherian ring, original Yoneda coefficient
postcomposition by the specified localization map localizes every Ext group. -/
theorem extPostcomp_isLocalized_of_finite [IsNoetherianRing R]
    (M : ModuleCat.{u} R) [Module.Finite R M] (n : ℕ) :
    IsLocalizedModule T ((Ext.mk₀ g).postcompOfLinear R M (add_zero n)) := by
  induction n using Nat.strong_induction_on generalizing M with
  | h n ih =>
    cases n with
    | zero =>
      let : Module.FinitePresentation R M := Module.finitePresentation_of_finite R M
      exact extZeroPostcomp_isLocalized T g M
    | succ n =>
      obtain ⟨P, _, _, _, _, p, hp⟩ := Module.exists_finite_presentation R M
      let S := p.shortComplexKer
      have hS : S.ShortExact := LinearMap.shortExact_shortComplexKer hp
      let : Module.Finite R S.X₁ := inferInstanceAs (Module.Finite R (LinearMap.ker p))
      let : Projective S.X₂ := inferInstanceAs (Projective (ModuleCat.of R P))
      cases n with
      | zero =>
        let : Module.FinitePresentation R S.X₁ :=
          Module.finitePresentation_of_finite R S.X₁
        let : Module.FinitePresentation R S.X₂ :=
          Module.finitePresentation_of_finite R S.X₂
        exact extOnePostcomp_isLocalized T g hS
      | succ n =>
        exact extPositivePostcomp_isLocalized T g hS n
          (ih (n + 1) (by omega) S.X₁)

end Coefficient

section BaseChange

variable {R A : Type u} [CommRing R] [CommRing A] [Algebra R A]

private instance scalarRestriction_linear :
    (ModuleCat.restrictScalars (algebraMap R A)).Linear R :=
  inferInstanceAs ((ModuleCat.restrictScalars (Algebra.ofId R A).toRingHom).Linear R)

variable [HasExt.{w} (ModuleCat.{u} R)] [HasExt.{z} (ModuleCat.{u} A)]

/-- The original exact-functor Ext map is the original coefficient-unit map
under native scalar adjunction. The two Ext sizes are independent. -/
theorem extScalarExtension_unit_equation
    [PreservesFiniteLimits (ModuleCat.extendScalars (algebraMap R A))]
    [PreservesFiniteColimits (ModuleCat.extendScalars (algebraMap R A))]
    (M N : ModuleCat.{u} R) (n : ℕ) (x : Ext.{w} M N n) :
    (ModuleCat.extendRestrictScalarsAdj.{u} (algebraMap R A)).extEquiv
        (x.mapExactFunctor (ModuleCat.extendScalars (algebraMap R A))) =
      x.comp (Ext.mk₀
        ((ModuleCat.extendRestrictScalarsAdj.{u} (algebraMap R A)).unit.app N))
          (add_zero n) :=
  CategoryTheory.Adjunction.extEquiv_mapExactFunctor_unit_original _ x

/-- Localization of the same native exact-functor map on Ext, for finite sources
and arbitrary coefficients over a Noetherian ring. -/
theorem extScalarExtension_isLocalized_of_finite [IsNoetherianRing R]
    (T : Submonoid R) [IsLocalization T A]
    (M N : ModuleCat.{u} R) [Module.Finite R M] (n : ℕ) :
    let : PreservesFiniteLimits (ModuleCat.extendScalars (algebraMap R A)) :=
      ModuleCat.extendScalars_preservesFiniteLimits_of_flat (algebraMap R A)
        (show (algebraMap R A).Flat from by
          exact RingHom.flat_algebraMap_iff.mpr (IsLocalization.flat A T))
    let : PreservesFiniteColimits (ModuleCat.extendScalars (algebraMap R A)) :=
      ModuleCat.extendScalars_preservesFiniteColimits_of_flat (algebraMap R A)
        (show (algebraMap R A).Flat from by
          exact RingHom.flat_algebraMap_iff.mpr (IsLocalization.flat A T))
    IsLocalizedModule T
      ((ModuleCat.extendScalars (algebraMap R A)).mapExtLinearMap R M N n) := by
  have hflat : (algebraMap R A).Flat :=
    RingHom.flat_algebraMap_iff.mpr (IsLocalization.flat A T)
  let : PreservesFiniteLimits (ModuleCat.extendScalars (algebraMap R A)) :=
    ModuleCat.extendScalars_preservesFiniteLimits_of_flat _ hflat
  let : PreservesFiniteColimits (ModuleCat.extendScalars (algebraMap R A)) :=
    ModuleCat.extendScalars_preservesFiniteColimits_of_flat _ hflat
  let F := ModuleCat.extendScalars (algebraMap R A)
  let adj := ModuleCat.extendRestrictScalarsAdj.{u} (algebraMap R A)
  let b := F.mapExtLinearMap R M N n
  let η := adj.unit.app N
  let : IsLocalizedModule T η.hom :=
    ModuleCat.extendRestrictScalarsAdj_unit_isLocalizedModule T (algebraMap R A)
      (by rw [toAlgebra_algebraMap]; infer_instance) N
  let e := adj.extLinearEquiv R (X := M) (Y := F.obj N) (n := n)
  let q := (Ext.mk₀ η).postcompOfLinear R M (add_zero n)
  let : IsLocalizedModule T q := extPostcomp_isLocalized_of_finite T η M n
  have he : b = e.symm.toLinearMap.comp q := by
    apply LinearMap.ext
    intro x
    apply e.injective
    change adj.extEquiv (x.mapExactFunctor F) = e (e.symm (q x))
    rw [LinearEquiv.apply_symm_apply]
    exact extScalarExtension_unit_equation M N n x
  change IsLocalizedModule T b
  rw [he]
  exact IsLocalizedModule.of_linearEquiv T q e.symm

/-- Original source endomorphisms act by the same native precomposition after scalar extension. -/
theorem extScalarExtension_precomp_endomorphism
    [PreservesFiniteLimits (ModuleCat.extendScalars (algebraMap R A))]
    [PreservesFiniteColimits (ModuleCat.extendScalars (algebraMap R A))]
    (M N : ModuleCat.{u} R) (a : M ⟶ M) (n : ℕ) (x : Ext.{w} M N n) :
    ((Ext.mk₀ a).comp x (zero_add n)).mapExactFunctor
        (ModuleCat.extendScalars (algebraMap R A)) =
      (Ext.mk₀ ((ModuleCat.extendScalars (algebraMap R A)).map a)).comp
        (x.mapExactFunctor (ModuleCat.extendScalars (algebraMap R A))) (zero_add n) := by
  rw [Ext.mapExactFunctor_comp, Ext.mapExactFunctor_mk₀]

end BaseChange

end ModuleCat
