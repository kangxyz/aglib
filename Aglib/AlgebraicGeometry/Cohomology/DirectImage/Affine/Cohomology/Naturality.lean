/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Cohomology.DirectImage.Affine.Cohomology

/-!
# Original affine higher-image comparison and coefficient naturality

The actual counit homology comparison is natural for the original complex
maps. Native resolution lifts therefore give the original coefficient map
under the affine higher-image and cohomology comparisons. All objects and
structural actions remain the original ones.
-/

@[expose] public section

noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian HomologicalComplex
open AlgebraicGeometry TopologicalSpace Opposite

namespace AlgebraicGeometry.Scheme.Cohomology

universe u w

private theorem affineCounitHomologyIso_naturality (R : CommRingCat.{u})
    {ι : Type w} (d : ComplexShape ι) {K L : HomologicalComplex (Spec R).Modules d}
    [QuasiIso (Scheme.Modules.Complex.tildeGlobalSectionsCounit R d K)]
    [QuasiIso (Scheme.Modules.Complex.tildeGlobalSectionsCounit R d L)]
    (φ : K ⟶ L) (i : ι) :
    (tilde.functor R).map
        (homologyMap ((moduleSpecΓFunctor.mapHomologicalComplex d).map φ) i) ≫
        (Scheme.Modules.Complex.tildeGlobalSectionsHomologyIso R d L i).hom =
      (Scheme.Modules.Complex.tildeGlobalSectionsHomologyIso R d K i).hom ≫
        homologyMap φ i := by
  let C := (moduleSpecΓFunctor.mapHomologicalComplex d).obj K
  let D := (moduleSpecΓFunctor.mapHomologicalComplex d).obj L
  let z := (moduleSpecΓFunctor.mapHomologicalComplex d).map φ
  let e₀ := (C.sc i).mapHomologyIso (tilde.functor R)
  let e₁ := (D.sc i).mapHomologyIso (tilde.functor R)
  have ht := ShortComplex.mapHomologyIso_inv_naturality
    ((HomologicalComplex.shortComplexFunctor (ModuleCat.{u} R) d i).map z) (tilde.functor R)
  change (tilde.functor R).map (homologyMap z i) ≫ e₁.inv =
    e₀.inv ≫ homologyMap (((tilde.functor R).mapHomologicalComplex d).map z) i at ht
  have hc := congrArg ((homologyFunctor (Spec R).Modules d i).map)
    (Scheme.Modules.Complex.tildeGlobalSectionsCounit_naturality R d φ)
  simp only [Functor.map_comp] at hc
  change homologyMap (((tilde.functor R).mapHomologicalComplex d).map z) i ≫
      homologyMap (Scheme.Modules.Complex.tildeGlobalSectionsCounit R d L) i =
    homologyMap (Scheme.Modules.Complex.tildeGlobalSectionsCounit R d K) i ≫
      homologyMap φ i at hc
  simp only [Scheme.Modules.Complex.tildeGlobalSectionsHomologyIso_hom, Category.assoc]
  change (tilde.functor R).map (homologyMap z i) ≫ e₁.inv ≫
      homologyMap (Scheme.Modules.Complex.tildeGlobalSectionsCounit R d L) i =
    e₀.inv ≫ homologyMap (Scheme.Modules.Complex.tildeGlobalSectionsCounit R d K) i ≫
      homologyMap φ i
  rw [← Category.assoc, ht]
  simp only [Category.assoc]
  exact congrArg (fun t => e₀.inv ≫ t) hc

variable {R : Type u} [CommRing R] {X : Scheme.{u}}
  (f : X ⟶ Spec (CommRingCat.of R)) [QuasiCompact f] [QuasiSeparated f]
  {M N : X.Modules} [M.IsQuasicoherent] [N.IsQuasicoherent]
  (I : InjectiveResolution M) (J : InjectiveResolution N)
  {v : M ⟶ N} (φ : InjectiveResolution.Hom I J v)

/-- The actual affine higher-image isomorphism preserves every original coefficient lift. -/
@[reassoc]
theorem moduleHigherDirectImageAffineIso_hom_naturality (n : ℕ) :
    ((Scheme.Modules.pushforward f).rightDerived n).map v ≫
        (moduleHigherDirectImageAffineIso f N J n).hom =
      (moduleHigherDirectImageAffineIso f M I n).hom ≫
        (tilde.functor (CommRingCat.of R)).map
          (homologyMap ((moduleSpecΓFunctor.mapHomologicalComplex (.up ℤ)).map
            (((Scheme.Modules.pushforward f).mapHomologicalComplex (.up ℤ)).map φ.hom'))
              (n : ℤ)) := by
  let K := ((Scheme.Modules.pushforward f).mapHomologicalComplex (.up ℤ)).obj I.cochainComplex
  let L := ((Scheme.Modules.pushforward f).mapHomologicalComplex (.up ℤ)).obj J.cochainComplex
  let q := ((Scheme.Modules.pushforward f).mapHomologicalComplex (.up ℤ)).map φ.hom'
  let : QuasiIso (Scheme.Modules.Complex.tildeGlobalSectionsCounit
      (CommRingCat.of R) (.up ℤ) K) := moduleResolutionPushforwardTildeCounit_quasiIso f M I
  let : QuasiIso (Scheme.Modules.Complex.tildeGlobalSectionsCounit
      (CommRingCat.of R) (.up ℤ) L) := moduleResolutionPushforwardTildeCounit_quasiIso f N J
  let e₀ := Scheme.Modules.Complex.tildeGlobalSectionsHomologyIso
    (CommRingCat.of R) (.up ℤ) K (n : ℤ)
  let e₁ := Scheme.Modules.Complex.tildeGlobalSectionsHomologyIso
    (CommRingCat.of R) (.up ℤ) L (n : ℤ)
  apply (cancel_mono e₁.hom).mp
  simp only [Category.assoc]
  change ((Scheme.Modules.pushforward f).rightDerived n).map v ≫
      (moduleHigherDirectImageAffineIso f N J n).hom ≫ e₁.hom =
    (moduleHigherDirectImageAffineIso f M I n).hom ≫
      (tilde.functor (CommRingCat.of R)).map
        (homologyMap ((moduleSpecΓFunctor.mapHomologicalComplex (.up ℤ)).map q) (n : ℤ)) ≫
      e₁.hom
  rw [affineCounitHomologyIso_naturality (CommRingCat.of R) (.up ℤ) q (n : ℤ)]
  rw [moduleHigherDirectImageAffineIso_hom_comp]
  rw [← Category.assoc, moduleHigherDirectImageAffineIso_hom_comp]
  exact InjectiveResolution.isoRightDerivedObjCochain_hom_naturality
    (Scheme.Modules.pushforward f) φ n

/-- The original affine section/cohomology comparison carries the actual higher-derived
coefficient map to the unchanged original cohomology coefficient map. -/
theorem moduleHigherDirectImageAffineSectionsLinearEquiv_naturality (n : ℕ)
    (x : moduleSpecΓFunctor.obj (((Scheme.Modules.pushforward f).rightDerived n).obj M)) :
    moduleHigherDirectImageAffineSectionsLinearEquiv f N J n
        (moduleSpecΓFunctor.map (((Scheme.Modules.pushforward f).rightDerived n).map v) x) =
      moduleCohomologyMapOfHom X
        (f.appTop.hom.comp (Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom) v n
        (moduleHigherDirectImageAffineSectionsLinearEquiv f M I n x) := by
  let φ : InjectiveResolution.Hom I J v :=
    ⟨InjectiveResolution.desc v J I, by
      simpa only [CochainComplex.single₀_map_f_zero] using
        InjectiveResolution.desc_commutes_zero v J I⟩
  let α := f.appTop.hom.comp (Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom
  let K := ((Scheme.Modules.pushforward f).mapHomologicalComplex (.up ℤ)).obj I.cochainComplex
  let L := ((Scheme.Modules.pushforward f).mapHomologicalComplex (.up ℤ)).obj J.cochainComplex
  let q := ((Scheme.Modules.pushforward f).mapHomologicalComplex (.up ℤ)).map φ.hom'
  let δ := (moduleSpecΓFunctor.mapHomologicalComplex (.up ℤ)).map q
  let t := homologyMap δ (n : ℤ)
  let a₀ := moduleSpecΓFunctor.map (moduleHigherDirectImageAffineIso f M I n).hom
  let a₁ := moduleSpecΓFunctor.map (moduleHigherDirectImageAffineIso f N J n).hom
  let r := moduleSpecΓFunctor.map (((Scheme.Modules.pushforward f).rightDerived n).map v)
  let e₀ := (tilde.toTildeΓNatIso (R := CommRingCat.of R)).app
    (((moduleSpecΓFunctor.mapHomologicalComplex (.up ℤ)).obj K).homology (n : ℤ))
  let e₁ := (tilde.toTildeΓNatIso (R := CommRingCat.of R)).app
    (((moduleSpecΓFunctor.mapHomologicalComplex (.up ℤ)).obj L).homology (n : ℤ))
  have hr := congrArg moduleSpecΓFunctor.map
    (moduleHigherDirectImageAffineIso_hom_naturality f I J φ n)
  simp only [Functor.map_comp] at hr
  change r ≫ a₁ = a₀ ≫ moduleSpecΓFunctor.map ((tilde.functor (CommRingCat.of R)).map t) at hr
  have hu := (tilde.toTildeΓNatIso (R := CommRingCat.of R)).inv.naturality t
  change moduleSpecΓFunctor.map ((tilde.functor (CommRingCat.of R)).map t) ≫ e₁.inv =
    e₀.inv ≫ t at hu
  have hm : r ≫ a₁ ≫ e₁.inv = a₀ ≫ e₀.inv ≫ t := by
    rw [← Category.assoc, hr]
    simp only [Category.assoc]
    rw [hu]
  have hx := ConcreteCategory.congr_hom hm x
  change e₁.inv (a₁ (r x)) = t (e₀.inv (a₀ x)) at hx
  let c₀ := moduleSpecPushforwardGlobalSectionsComplexIso f (.up ℤ) I.cochainComplex
  let c₁ := moduleSpecPushforwardGlobalSectionsComplexIso f (.up ℤ) J.cochainComplex
  let s := ((moduleGlobalSectionsFunctorOfHom X α).mapHomologicalComplex (.up ℤ)).map φ.hom'
  have hc : δ ≫ c₁.hom = c₀.hom ≫ s := by
    ext i y
    rfl
  have hh := congrArg ((homologyFunctor (ModuleCat.{u} R) (.up ℤ) (n : ℤ)).map) hc
  simp only [Functor.map_comp] at hh
  change t ≫ homologyMap c₁.hom (n : ℤ) =
    homologyMap c₀.hom (n : ℤ) ≫ homologyMap s (n : ℤ) at hh
  have hy := ConcreteCategory.congr_hom hh (e₀.inv (a₀ x))
  change homologyMap c₁.hom (n : ℤ) (t (e₀.inv (a₀ x))) =
    homologyMap s (n : ℤ) (homologyMap c₀.hom (n : ℤ) (e₀.inv (a₀ x))) at hy
  rw [moduleHigherDirectImageAffineSectionsLinearEquiv_apply f N J n,
    moduleHigherDirectImageAffineSectionsLinearEquiv_apply f M I n]
  change moduleResolutionSectionsCohomologyLinearEquiv X α J n
      (homologyMap c₁.hom (n : ℤ) (e₁.inv (a₁ (r x)))) =
    moduleCohomologyMapOfHom X α v n
      (moduleResolutionSectionsCohomologyLinearEquiv X α I n
        (homologyMap c₀.hom (n : ℤ) (e₀.inv (a₀ x))))
  rw [hx, hy]
  exact moduleResolutionSectionsCohomologyLinearEquiv_naturality X α I J φ n
    (homologyMap c₀.hom (n : ℤ) (e₀.inv (a₀ x)))

/-- The installed standard derived categories are the same ones used by the original map. -/
local instance affineCoefficientDerived (Z : Scheme.{u}) :
    HasDerivedCategory.{u + 1} Z.Modules := HasDerivedCategory.standard _

/-- The unchanged cohomology comparison preserves the actual coefficient map on homology of
the installed derived direct image at the original single, for any supplied resolutions. -/
theorem moduleDerivedPushforwardSingleAffineSectionsLinearEquiv_naturality (n : ℕ)
    (x : moduleSpecΓFunctor.obj
      ((DerivedCategory.Plus.homologyFunctor (Spec (CommRingCat.of R)).Modules (n : ℤ)).obj
        ((Scheme.Modules.pushforward f).rightDerivedFunctorPlus.obj
          ((DerivedCategory.Plus.singleFunctor X.Modules 0).obj M)))) :
    moduleDerivedPushforwardSingleAffineSectionsLinearEquiv f N J n
        (moduleSpecΓFunctor.map
          ((DerivedCategory.Plus.homologyFunctor (Spec (CommRingCat.of R)).Modules (n : ℤ)).map
            ((Scheme.Modules.pushforward f).rightDerivedFunctorPlus.map
              ((DerivedCategory.Plus.singleFunctor X.Modules 0).map v))) x) =
      moduleCohomologyMapOfHom X
        (f.appTop.hom.comp (Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom) v n
        (moduleDerivedPushforwardSingleAffineSectionsLinearEquiv f M I n x) := by
  let F : X.Modules ⥤ (Spec (CommRingCat.of R)).Modules := Scheme.Modules.pushforward f
  let H := DerivedCategory.Plus.homologyFunctor (Spec (CommRingCat.of R)).Modules (n : ℤ)
  let E := F.rightDerivedSingleHomologyIso n
  let t := H.map (F.rightDerivedFunctorPlus.map
    ((DerivedCategory.Plus.singleFunctor X.Modules 0).map v))
  have h := congrArg moduleSpecΓFunctor.map (E.inv.naturality v)
  simp only [Functor.map_comp] at h
  have hx := ConcreteCategory.congr_hom h x
  change moduleSpecΓFunctor.map (E.inv.app N) (moduleSpecΓFunctor.map t x) =
    moduleSpecΓFunctor.map ((F.rightDerived n).map v)
      (moduleSpecΓFunctor.map (E.inv.app M) x) at hx
  change moduleHigherDirectImageAffineSectionsLinearEquiv f N J n
      (moduleSpecΓFunctor.map (E.inv.app N) (moduleSpecΓFunctor.map t x)) =
    moduleCohomologyMapOfHom X
      (f.appTop.hom.comp (Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom) v n
      (moduleHigherDirectImageAffineSectionsLinearEquiv f M I n
        (moduleSpecΓFunctor.map (E.inv.app M) x))
  rw [hx]
  exact moduleHigherDirectImageAffineSectionsLinearEquiv_naturality f I J n
    (moduleSpecΓFunctor.map (E.inv.app M) x)

end AlgebraicGeometry.Scheme.Cohomology
