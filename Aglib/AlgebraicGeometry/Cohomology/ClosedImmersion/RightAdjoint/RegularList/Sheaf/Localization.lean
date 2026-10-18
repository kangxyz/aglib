/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.Algebra.Homology.DerivedCategory.RightDerivedFunctorPlus.InjectiveResolution
public import Aglib.AlgebraicGeometry.Cohomology.ClosedImmersion.RightAdjoint.RegularList
public import Mathlib.RingTheory.Regular.Flat
public import Aglib.Algebra.Homology.Embedding.MapExtend.Naturality
public import Aglib.AlgebraicGeometry.Modules.Complex.Tilde
public import Aglib.Algebra.Category.ModuleCat.ChangeOfRings.Coinduction.Quotient
public import Aglib.AlgebraicGeometry.Cohomology.Affine.InjectiveResolution
public import Aglib.CategoryTheory.Abelian.Injective.ExactFunctor
public import Aglib.AlgebraicGeometry.Modules.FinitePresentation.Basic
public import Aglib.Algebra.Homology.Koszul.Ext.BaseChange
public import Aglib.AlgebraicGeometry.Spec.Localization
public import Mathlib.RingTheory.TensorProduct.Quotient
public import Aglib.AlgebraicGeometry.Cohomology.ClosedImmersion.RightAdjoint.Affine
public import Aglib.AlgebraicGeometry.Modules.QuasiCoherent.Affine.Morphisms
public import Aglib.AlgebraicGeometry.Modules.Restriction.Sections
public import Aglib.AlgebraicGeometry.Modules.QuasiCoherent.Affine.PullbackSections
public import Aglib.AlgebraicGeometry.Modules.QuasiCoherent.Affine.RestrictionSections

/-!
# Original affine closed-adjoint localization

This leaf compares the actual principal restriction on the supplied injective-resolution
model with the original exact scalar-extension map on Ext. The quotient source retains
its original action and the normalization `1 tensor [r]` to localized `[r]`. The actual
principal-sections comparison retains the original restriction arrow. These are the
localization inputs for the actual tilde-global-sections counit computation in `Counit`.
-/

universe u w z u1 v1 w1 r1 a b

noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
open AlgebraicGeometry.Scheme.Modules
open scoped TensorProduct ChangeOfRings
section

private def scalarExtensionQuotientIso {R A : Type u} [CommRing R] [CommRing A]
    (σ : R →+* A) (I : Ideal R) :
    (ModuleCat.extendScalars σ).obj (ModuleCat.of R (R ⧸ I)) ≅
      ModuleCat.of A (A ⧸ I.map σ) := by
  let : Algebra R A := σ.toAlgebra
  exact (Algebra.TensorProduct.quotIdealMapEquivTensorQuot A I).symm.toLinearEquiv.toModuleIso

private theorem scalarExtensionQuotientIso_one_tmul {R A : Type u}
    [CommRing R] [CommRing A] (σ : R →+* A) (I : Ideal R) (r : R) :
    (scalarExtensionQuotientIso σ I).hom ((1 : A) ⊗ₜ[R,σ] Ideal.Quotient.mk I r) =
      Ideal.Quotient.mk (I.map σ) (σ r) := by
  let : Algebra R A := σ.toAlgebra
  change (Algebra.TensorProduct.quotIdealMapEquivTensorQuot A I).symm
    (1 ⊗ₜ[R] Ideal.Quotient.mk I r) = _
  simpa only [Algebra.smul_def, mul_one, RingHom.algebraMap_toAlgebra,
    ← Ideal.Quotient.mk_eq_mk] using
    Algebra.TensorProduct.quotIdealMapEquivTensorQuot_symm_tmul A I (1 : A) r
section Away
variable {R : Type u} [CommRing R] (I : Ideal R) (t : R)

private abbrev quotientAwayMap : Localization.Away t →+*
    Localization.Away (Ideal.Quotient.mk I t) :=
  IsLocalization.Away.map (Localization.Away t)
    (Localization.Away (Ideal.Quotient.mk I t)) (Ideal.Quotient.mk I) t

private theorem quotientAwayMap_surjective : Function.Surjective (quotientAwayMap I t) :=
  IsLocalization.map_surjective_of_surjective (Submonoid.powers t)
    (Localization.Away t) (Localization.Away (Ideal.Quotient.mk I t))
      Ideal.Quotient.mk_surjective

private theorem quotientAwayMap_kernel :
    RingHom.ker (quotientAwayMap I t) = I.map (algebraMap R (Localization.Away t)) := by
  have h := CommRingCat.ker_localizationAway_map
    (CommRingCat.ofHom (Ideal.Quotient.mk I)) t
  change RingHom.ker (quotientAwayMap I t) =
    (RingHom.ker (Ideal.Quotient.mk I)).map (algebraMap R (Localization.Away t)) at h
  simpa only [Ideal.mk_ker] using h

private def quotientAwayRingEquiv :
    (Localization.Away t ⧸ I.map (algebraMap R (Localization.Away t))) ≃+*
      Localization.Away (Ideal.Quotient.mk I t) :=
  (Ideal.quotEquivOfEq (quotientAwayMap_kernel I t).symm).trans
    ((quotientAwayMap I t).quotientKerEquivOfSurjective (quotientAwayMap_surjective I t))

private theorem quotientAwayRingEquiv_mk (a : Localization.Away t) :
    quotientAwayRingEquiv I t
      (Ideal.Quotient.mk (I.map (algebraMap R (Localization.Away t))) a) =
        quotientAwayMap I t a := by
  exact RingHom.quotientKerEquivOfSurjective_apply_mk (quotientAwayMap_surjective I t) a

private def quotientAwayModuleIso :
    ModuleCat.of (Localization.Away t)
        (Localization.Away t ⧸ I.map (algebraMap R (Localization.Away t))) ≅
      (ModuleCat.restrictScalars (quotientAwayMap I t)).obj
        (ModuleCat.of (Localization.Away (Ideal.Quotient.mk I t))
          (Localization.Away (Ideal.Quotient.mk I t))) := by
  refine ModuleCat.isoMk (quotientAwayRingEquiv I t).toAddEquiv.toAddCommGrpIso ?_
  intro a
  ext x
  change quotientAwayMap I t a * quotientAwayRingEquiv I t x =
    quotientAwayRingEquiv I t
      (Ideal.Quotient.mk (I.map (algebraMap R (Localization.Away t))) a * x)
  rw [map_mul, quotientAwayRingEquiv_mk]

private def scalarExtensionQuotientAwayIso :
    (ModuleCat.extendScalars (algebraMap R (Localization.Away t))).obj
        (ModuleCat.of R (R ⧸ I)) ≅
      (ModuleCat.restrictScalars (quotientAwayMap I t)).obj
        (ModuleCat.of (Localization.Away (Ideal.Quotient.mk I t))
          (Localization.Away (Ideal.Quotient.mk I t))) :=
  scalarExtensionQuotientIso (algebraMap R (Localization.Away t)) I ≪≫
    quotientAwayModuleIso I t

private theorem scalarExtensionQuotientAwayIso_one_tmul (r : R) :
    (scalarExtensionQuotientAwayIso I t).hom
      ((1 : Localization.Away t) ⊗ₜ[R,algebraMap R (Localization.Away t)] Ideal.Quotient.mk I r) =
      algebraMap (R ⧸ I) (Localization.Away (Ideal.Quotient.mk I t))
        (Ideal.Quotient.mk I r) := by
  change (quotientAwayModuleIso I t).hom
    ((scalarExtensionQuotientIso (algebraMap R (Localization.Away t)) I).hom _) = _
  rw [scalarExtensionQuotientIso_one_tmul]
  change quotientAwayRingEquiv I t
    (Ideal.Quotient.mk (I.map (algebraMap R (Localization.Away t))) _) = _
  rw [quotientAwayRingEquiv_mk]
  exact IsLocalization.map_eq (M := Submonoid.powers t)
    (T := Submonoid.powers (Ideal.Quotient.mk I t)) (S := Localization.Away t)
    (Q := Localization.Away (Ideal.Quotient.mk I t)) (g := Ideal.Quotient.mk I)
    (by rintro x ⟨n, rfl⟩; exact ⟨n, (map_pow (Ideal.Quotient.mk I) t n).symm⟩) r
end Away
end

section

section
namespace AlgebraicGeometry.Scheme.Modules
variable {W U V X : Scheme.{u}}
  (a : W ⟶ U) (b : W ⟶ V) (f : U ⟶ X) (j : V ⟶ X)
  [IsOpenImmersion a] [IsOpenImmersion j]
  [IsClosedImmersion f] [IsClosedImmersion b] (h : IsPullback a b f j)

private theorem closedRightOpenIso_hom_mate (N : X.Modules) :
    (closedImmersionRightAdjointOpenIso a b f j h).hom.app N =
      (closedImmersionRightAdjunction b).homEquiv _ _
        ((cartesianOpenBaseChange a b f j h).inv.app
          ((closedImmersionRightAdjoint f).obj N) ≫
            (restrictFunctor j).map ((closedImmersionRightAdjunction f).counit.app N)) := by
  let D := closedImmersionRightAdjunction f
  let A := extensionByZeroRestrictAdjunction a
  let J := extensionByZeroRestrictAdjunction j
  let C := A.comp D
  let E := (closedImmersionRightAdjoint f).obj N
  let M := (restrictFunctor a).obj E
  let p := C.counit.app N
  have h₀ : C.homEquiv M N p = 𝟙 M := by
    rw [Adjunction.homEquiv_unit]
    exact C.right_triangle_components N
  have he := closedImmersionRightAdjointOpenIso_homEquiv a b f j h M N p
  rw [h₀, Category.id_comp] at he
  rw [Adjunction.comp_homEquiv] at he
  change _ = (closedImmersionRightAdjunction b).homEquiv M ((restrictFunctor j).obj N)
    (J.homEquiv ((pushforward b).obj M) N
      ((closedPushforwardExtensionByZeroIso a b f j h).hom.app M ≫ p)) at he
  have hb : J.homEquiv ((pushforward b).obj M) N
      ((closedPushforwardExtensionByZeroIso a b f j h).hom.app M ≫ p) =
    (pushforward b).map (A.unit.app M) ≫
      (cartesianOpenBaseChange a b f j h).inv.app ((extensionByZero a).obj M) ≫
        (restrictFunctor j).map p := by
    rw [Adjunction.homEquiv_naturality_right]
    change J.homEquiv _ _ ((J.homEquiv _ _).symm _) ≫ _ = _
    rw [Equiv.apply_symm_apply]
    rfl
  rw [hb] at he
  have hn := (cartesianOpenBaseChange a b f j h).inv.naturality (A.counit.app E)
  change (pushforward b).map ((restrictFunctor a).map (A.counit.app E)) ≫
      (cartesianOpenBaseChange a b f j h).inv.app E =
    (cartesianOpenBaseChange a b f j h).inv.app ((extensionByZero a).obj M) ≫
      (restrictFunctor j).map ((pushforward f).map (A.counit.app E)) at hn
  have hp : (pushforward b).map (A.unit.app M) ≫
      (cartesianOpenBaseChange a b f j h).inv.app ((extensionByZero a).obj M) ≫
        (restrictFunctor j).map p =
    (cartesianOpenBaseChange a b f j h).inv.app E ≫
      (restrictFunctor j).map (D.counit.app N) := by
    change (pushforward b).map (A.unit.app M) ≫
        (cartesianOpenBaseChange a b f j h).inv.app ((extensionByZero a).obj M) ≫
          (restrictFunctor j).map
            ((pushforward f).map (A.counit.app E) ≫ D.counit.app N) = _
    rw [Functor.map_comp, ← Category.assoc
      ((cartesianOpenBaseChange a b f j h).inv.app ((extensionByZero a).obj M)), ← hn]
    simp only [Category.assoc]
    rw [← Functor.map_comp_assoc]
    have ht := A.right_triangle_components E
    change A.unit.app M ≫ (restrictFunctor a).map (A.counit.app E) = 𝟙 M at ht
    rw [ht]
    erw [(pushforward b).map_id M]
    exact Category.id_comp _
  rw [hp] at he
  exact he

private theorem closedRightOpenIso_counit_mate (N : X.Modules) :
    (pushforward b).map ((closedImmersionRightAdjointOpenIso a b f j h).hom.app N) ≫
      (closedImmersionRightAdjunction b).counit.app ((restrictFunctor j).obj N) =
    (cartesianOpenBaseChange a b f j h).inv.app
      ((closedImmersionRightAdjoint f).obj N) ≫
        (restrictFunctor j).map ((closedImmersionRightAdjunction f).counit.app N) := by
  let p := (cartesianOpenBaseChange a b f j h).inv.app
    ((closedImmersionRightAdjoint f).obj N) ≫
      (restrictFunctor j).map ((closedImmersionRightAdjunction f).counit.app N)
  let e := (closedImmersionRightAdjunction b).homEquiv
    ((restrictFunctor a).obj ((closedImmersionRightAdjoint f).obj N))
    ((restrictFunctor j).obj N)
  have he : e.symm ((closedImmersionRightAdjointOpenIso a b f j h).hom.app N) = p :=
    (congrArg e.symm (closedRightOpenIso_hom_mate a b f j h N)).trans
      (e.symm_apply_apply p)
  change ((closedImmersionRightAdjunction b).homEquiv _ _).symm
    ((closedImmersionRightAdjointOpenIso a b f j h).hom.app N) = p at he
  rw [Adjunction.homEquiv_counit] at he
  exact he
end AlgebraicGeometry.Scheme.Modules
end

section
namespace AlgebraicGeometry.Scheme.Modules
variable {R S : CommRingCat.{u}} (φ : R ⟶ S) [IsClosedImmersion (Spec.map φ)]

private theorem closedAffine_counit_sections (N : (Spec R).Modules) :
    (ModuleCat.restrictScalars φ.hom).map
        ((closedImmersionRightAdjointAffineIso φ).hom.app N) ≫
      (ModuleCat.restrictCoextendScalarsAdj φ.hom).counit.app (moduleSpecΓFunctor.obj N) =
    (pushforwardGlobalSectionsIso φ).inv.app
      ((closedImmersionRightAdjoint (Spec.map φ)).obj N) ≫
        moduleSpecΓFunctor.map ((closedImmersionRightAdjunction (Spec.map φ)).counit.app N) := by
  let D := closedImmersionRightAdjunction (Spec.map φ)
  let A := tilde.adjunction (R := S)
  let B := tilde.adjunction (R := R)
  let C := A.comp D
  let E := (closedImmersionRightAdjoint (Spec.map φ)).obj N
  let M := moduleSpecΓFunctor.obj E
  let p := C.counit.app N
  let T := ModuleCat.restrictCoextendScalarsAdj φ.hom
  have h₀ : C.homEquiv M N p = 𝟙 M := by
    rw [Adjunction.homEquiv_unit]
    exact C.right_triangle_components N
  have h := closedImmersionRightAdjointAffineIso_homEquiv φ M N p
  rw [h₀, Category.id_comp, Adjunction.comp_homEquiv] at h
  let g := B.homEquiv _ _ ((tildePushforwardIso φ).inv.app M ≫ p)
  have he : (T.homEquiv M (moduleSpecΓFunctor.obj N)).symm
      ((closedImmersionRightAdjointAffineIso φ).hom.app N) = g :=
    (congrArg (T.homEquiv M (moduleSpecΓFunctor.obj N)).symm h).trans
      ((T.homEquiv M (moduleSpecΓFunctor.obj N)).symm_apply_apply g)
  rw [Adjunction.homEquiv_counit] at he
  refine he.trans ?_
  change B.homEquiv _ _ ((tildePushforwardIso φ).inv.app M ≫
      ((pushforward (Spec.map φ)).map E.fromTildeΓ ≫ D.counit.app N)) = _
  rw [Adjunction.homEquiv_naturality_right]
  erw [tildePushforwardIso_inv_homEquiv φ M]
  rw [Functor.map_comp]
  have hn := (pushforwardGlobalSectionsIso φ).inv.naturality E.fromTildeΓ
  change (ModuleCat.restrictScalars φ.hom).map (moduleSpecΓFunctor.map E.fromTildeΓ) ≫
      (pushforwardGlobalSectionsIso φ).inv.app E =
    (pushforwardGlobalSectionsIso φ).inv.app (tilde M) ≫
      moduleSpecΓFunctor.map ((pushforward (Spec.map φ)).map E.fromTildeΓ) at hn
  simp only [Category.assoc]
  erw [← Category.assoc ((pushforwardGlobalSectionsIso φ).inv.app (tilde M)), ← hn]
  simp only [Category.assoc]
  rw [← Functor.map_comp_assoc]
  have ht := A.right_triangle_components E
  change (tilde.isoTop M).hom ≫ moduleSpecΓFunctor.map E.fromTildeΓ = 𝟙 M at ht
  rw [ht, CategoryTheory.Functor.map_id, Category.id_comp]

private theorem closedAffine_hom_one (N : (Spec R).Modules)
    (m : (moduleSpecΓFunctor (R := S)).obj
      ((closedImmersionRightAdjoint (Spec.map φ)).obj N)) :
    closedImmersionRightAdjointSectionsLinearEquiv φ N m (1 : S) =
      (moduleSpecΓFunctor.map ((closedImmersionRightAdjunction (Spec.map φ)).counit.app N))
        (((pushforwardGlobalSectionsIso φ).inv.app
          ((closedImmersionRightAdjoint (Spec.map φ)).obj N)) m) := by
  have h := ConcreteCategory.congr_hom (closedAffine_counit_sections φ N) m
  exact h
end AlgebraicGeometry.Scheme.Modules
end

section
namespace AlgebraicGeometry.Scheme.Modules
private def openGlobalRestriction {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j]
    (M : X.Modules) : Γ(M, ⊤) →+ Γ(M.restrict j, ⊤) :=
  (((restrictAdjunction j).unit.app M).app ⊤).hom
variable {W U V X : Scheme.{u}}
  (a : W ⟶ U) (b : W ⟶ V) (f : U ⟶ X) (j : V ⟶ X)
  (h : IsPullback a b f j)

private theorem cartesianPushforwardSquare_top (M : W.Modules) (m : Γ(M, ⊤)) :
    ((cartesianPushforwardSquare a b f j h).hom.app M).app ⊤ m = m := by
  simp only [cartesianPushforwardSquare, Iso.trans_hom, NatTrans.comp_app,
    Hom.comp_app, pushforwardComp_hom_app_app, Iso.symm_hom,
    pushforwardComp_inv_app_app, pushforwardCongr_hom_app_app,
    ConcreteCategory.comp_apply]
  change M.presheaf.map (𝟙 (op (⊤ : W.Opens))) m = m
  exact ConcreteCategory.congr_hom (M.presheaf.map_id (op ⊤)) m
variable [IsOpenImmersion a] [IsOpenImmersion j]

private theorem cartesianOpenBaseChange_globalRestriction (M : U.Modules) (m : Γ(M, ⊤)) :
    ((cartesianOpenBaseChange a b f j h).hom.app M).app ⊤
      (openGlobalRestriction j ((pushforward f).obj M) m) =
      openGlobalRestriction a M m := by
  have hc := cartesianOpenBaseChange_unit a b f j h M
  have hv := congrArg (fun k => (k.app ⊤).hom m) hc
  change ((cartesianPushforwardSquare a b f j h).hom.app (M.restrict a)).app ⊤
      (openGlobalRestriction a M m) =
    ((cartesianOpenBaseChange a b f j h).hom.app M).app ⊤
      (openGlobalRestriction j ((pushforward f).obj M) m) at hv
  rw [cartesianPushforwardSquare_top] at hv
  exact hv.symm

private theorem cartesianOpenBaseChange_inv_globalRestriction (M : U.Modules)
    (m : Γ(M, ⊤)) :
    ((cartesianOpenBaseChange a b f j h).inv.app M).app ⊤
      (openGlobalRestriction a M m) =
      openGlobalRestriction j ((pushforward f).obj M) m := by
  rw [← cartesianOpenBaseChange_globalRestriction a b f j h M m]
  exact Iso.hom_inv_id_apply
    ((TwoOpen.sectionsFunctor V ⊤).mapIso ((cartesianOpenBaseChange a b f j h).app M)) _
end AlgebraicGeometry.Scheme.Modules
end

section
namespace AlgebraicGeometry.Scheme.Modules
variable {W U V X : Scheme.{u}}
  (a : W ⟶ U) (b : W ⟶ V) (f : U ⟶ X) (j : V ⟶ X)
  [IsOpenImmersion a] [IsOpenImmersion j]
  [IsClosedImmersion f] [IsClosedImmersion b] (h : IsPullback a b f j)
end AlgebraicGeometry.Scheme.Modules
end

section
namespace AlgebraicGeometry.Scheme.Modules
private theorem openGlobalRestriction_naturality {U X : Scheme.{u}}
    (j : U ⟶ X) [IsOpenImmersion j] {M N : X.Modules} (p : M ⟶ N) (m : Γ(M, ⊤)) :
    ((restrictFunctor j).map p).app ⊤ (openGlobalRestriction j M m) =
      openGlobalRestriction j N (p.app ⊤ m) := by
  have h := congrArg (fun k => (k.app ⊤).hom m) ((restrictAdjunction j).unit.naturality p)
  change openGlobalRestriction j N (p.app ⊤ m) =
    ((restrictFunctor j).map p).app ⊤ (openGlobalRestriction j M m) at h
  exact h.symm
variable {W U V X : Scheme.{u}}
  (a : W ⟶ U) (b : W ⟶ V) (f : U ⟶ X) (j : V ⟶ X)
  [IsOpenImmersion a] [IsOpenImmersion j]
  [IsClosedImmersion f] [IsClosedImmersion b] (h : IsPullback a b f j)

private theorem closedRightOpenIso_global_counit (N : X.Modules)
    (m : Γ((closedImmersionRightAdjoint f).obj N, ⊤)) :
    ((closedImmersionRightAdjunction b).counit.app ((restrictFunctor j).obj N)).app ⊤
      (((closedImmersionRightAdjointOpenIso a b f j h).hom.app N).app ⊤
        (openGlobalRestriction a ((closedImmersionRightAdjoint f).obj N) m)) =
      openGlobalRestriction j N
        (((closedImmersionRightAdjunction f).counit.app N).app ⊤ m) := by
  let E := (closedImmersionRightAdjoint f).obj N
  have hv := congrArg (fun k => (k.app ⊤).hom (openGlobalRestriction a E m))
    (closedRightOpenIso_counit_mate a b f j h N)
  change ((closedImmersionRightAdjunction b).counit.app ((restrictFunctor j).obj N)).app ⊤
      (((closedImmersionRightAdjointOpenIso a b f j h).hom.app N).app ⊤
        (openGlobalRestriction a E m)) =
    ((restrictFunctor j).map ((closedImmersionRightAdjunction f).counit.app N)).app ⊤
      (((cartesianOpenBaseChange a b f j h).inv.app E).app ⊤
        (openGlobalRestriction a E m)) at hv
  rw [cartesianOpenBaseChange_inv_globalRestriction] at hv
  exact hv.trans (openGlobalRestriction_naturality j
    ((closedImmersionRightAdjunction f).counit.app N) m)
end AlgebraicGeometry.Scheme.Modules
end

end

section
namespace AlgebraicGeometry.Scheme.Modules
section Pushforward
variable {R A : CommRingCat.{u}} (σ : R ⟶ A)

private theorem pushforwardΓ_inv_apply (N : (Spec A).Modules)
    (m : (moduleSpecΓFunctor (R := A)).obj N) :
    (pushforwardGlobalSectionsIso σ).inv.app N m = m := rfl
end Pushforward
variable {R A : CommRingCat.{u}} (σ : R ⟶ A) [IsOpenImmersion (Spec.map σ)]

/-- The original open-restriction unit on affine global sections. -/
@[expose] public def affineOpenRestrictionSectionsMap (N : (Spec R).Modules) :
    (moduleSpecΓFunctor (R := R)).obj N ⟶
      (ModuleCat.restrictScalars σ.hom).obj
        ((moduleSpecΓFunctor (R := A)).obj ((restrictFunctor (Spec.map σ)).obj N)) :=
  moduleSpecΓFunctor.map ((restrictAdjunction (Spec.map σ)).unit.app N) ≫
    (pushforwardGlobalSectionsIso σ).hom.app ((restrictFunctor (Spec.map σ)).obj N)

public theorem affineOpenRestrictionSectionsMap_apply (N : (Spec R).Modules)
    (m : (moduleSpecΓFunctor (R := R)).obj N) :
    affineOpenRestrictionSectionsMap σ N m = ((restrictAdjunction (Spec.map σ)).unit.app N).app ⊤
      m := rfl

/-- The original open-restriction unit, as its native natural transformation. -/
@[expose] public def affineOpenRestrictionSectionsNat :
    moduleSpecΓFunctor (R := R) ⟶
      restrictFunctor (Spec.map σ) ⋙ moduleSpecΓFunctor (R := A) ⋙
        ModuleCat.restrictScalars σ.hom :=
  (Functor.leftUnitor (moduleSpecΓFunctor (R := R))).inv ≫
    Functor.whiskerRight (restrictAdjunction (Spec.map σ)).unit
      (moduleSpecΓFunctor (R := R)) ≫
    (Functor.associator (restrictFunctor (Spec.map σ)) (pushforward (Spec.map σ))
      (moduleSpecΓFunctor (R := R))).hom ≫
    Functor.whiskerLeft (restrictFunctor (Spec.map σ)) (pushforwardGlobalSectionsIso σ).hom

public theorem affineOpenRestrictionSectionsNat_app (N : (Spec R).Modules) :
    (affineOpenRestrictionSectionsNat σ).app N = affineOpenRestrictionSectionsMap σ N := rfl

private def openSpecRestrictionMate :
    moduleSpecΓFunctor (R := R) ⋙ ModuleCat.extendScalars σ.hom ⟶
      restrictFunctor (Spec.map σ) ⋙ moduleSpecΓFunctor (R := A) where
  app N := ((ModuleCat.extendRestrictScalarsAdj σ.hom).homEquiv _ _).symm
    ((affineOpenRestrictionSectionsNat σ).app N)
  naturality {M N} p := by
    dsimp only [CategoryTheory.Functor.comp_map]
    apply ((ModuleCat.extendRestrictScalarsAdj σ.hom).homEquiv _ _).injective
    rw [Adjunction.homEquiv_naturality_left, Adjunction.homEquiv_naturality_right,
      Equiv.apply_symm_apply, Equiv.apply_symm_apply]
    exact (affineOpenRestrictionSectionsNat σ).naturality p

private theorem openSpecRestrictionMate_unit (N : (Spec R).Modules) :
    (ModuleCat.extendRestrictScalarsAdj σ.hom).unit.app (moduleSpecΓFunctor.obj N) ≫
      (ModuleCat.restrictScalars σ.hom).map ((openSpecRestrictionMate σ).app N) =
    affineOpenRestrictionSectionsMap σ N := by
  have h := ((ModuleCat.extendRestrictScalarsAdj σ.hom).homEquiv _ _).apply_symm_apply
    ((affineOpenRestrictionSectionsNat σ).app N)
  rw [Adjunction.homEquiv_unit] at h
  exact h.trans (affineOpenRestrictionSectionsNat_app σ N)
end AlgebraicGeometry.Scheme.Modules
end

section
namespace AlgebraicGeometry.Scheme.Modules
variable {R A : CommRingCat.{u}} (σ : R ⟶ A) [IsOpenImmersion (Spec.map σ)]

private theorem openSpecRestrictionMate_eq_affineRestrictGlobalSectionsIso
    (N : (Spec R).Modules) [N.IsQuasicoherent] :
    (openSpecRestrictionMate σ).app N = (affineRestrictGlobalSectionsIso σ N).hom := by
  apply ((ModuleCat.extendRestrictScalarsAdj σ.hom).homEquiv _ _).injective
  simpa only [Adjunction.homEquiv_unit] using
    (openSpecRestrictionMate_unit σ N).trans (affineRestrictGlobalSectionsIso_unit σ N).symm

private theorem openSpecRestrictionMate_isIso
    (N : (Spec R).Modules) [N.IsQuasicoherent] :
    IsIso ((openSpecRestrictionMate σ).app N) := by
  rw [openSpecRestrictionMate_eq_affineRestrictGlobalSectionsIso]
  infer_instance
end AlgebraicGeometry.Scheme.Modules
end

section
namespace AlgebraicGeometry.Scheme.Modules
section QuotientLocalization
variable {R : CommRingCat.{u}} (I : Ideal R) (t : R)

private abbrev quotientSpecRing : CommRingCat.{u} := .of (R ⧸ I)
private abbrev ambientAwayRing : CommRingCat.{u} := .of (Localization.Away t)
private abbrev quotientAwaySpecRing : CommRingCat.{u} :=
  .of (Localization.Away (Ideal.Quotient.mk I t))
private abbrev quotientSpecMap : R ⟶ quotientSpecRing I :=
  CommRingCat.ofHom (Ideal.Quotient.mk I)
private abbrev ambientAwayUnit : R ⟶ ambientAwayRing t :=
  CommRingCat.ofHom (algebraMap R (Localization.Away t))
private abbrev quotientAwayUnit : quotientSpecRing I ⟶ quotientAwaySpecRing I t :=
  CommRingCat.ofHom
    (algebraMap (R ⧸ I) (Localization.Away (Ideal.Quotient.mk I t)))
private abbrev localizedQuotientSpecMap : ambientAwayRing t ⟶ quotientAwaySpecRing I t :=
  CommRingCat.ofHom (quotientAwayMap I t)
local instance : IsClosedImmersion (Spec.map (localizedQuotientSpecMap I t)) :=
  Scheme.isClosedImmersion_specMap_localizationAway (quotientSpecMap I) t

private theorem quotientLocalizationSquare :
    IsPullback (Spec.map (quotientAwayUnit I t)) (Spec.map (localizedQuotientSpecMap I t))
      (Spec.map (quotientSpecMap I)) (Spec.map (ambientAwayUnit t)) :=
  (Scheme.isPullback_specMap_localizationAway (quotientSpecMap I) t).flip

private def quotientLocalizationGeoMap (N : (Spec R).Modules) :
    (moduleSpecΓFunctor (R := quotientSpecRing I)).obj
        ((closedImmersionRightAdjoint (Spec.map (quotientSpecMap I))).obj N) ⟶
      (ModuleCat.restrictScalars (quotientAwayUnit I t).hom).obj
        ((moduleSpecΓFunctor (R := quotientAwaySpecRing I t)).obj
          ((closedImmersionRightAdjoint (Spec.map (localizedQuotientSpecMap I t))).obj
            ((restrictFunctor (Spec.map (ambientAwayUnit t))).obj N))) :=
  affineOpenRestrictionSectionsMap (quotientAwayUnit I t)
      ((closedImmersionRightAdjoint (Spec.map (quotientSpecMap I))).obj N) ≫
    (ModuleCat.restrictScalars (quotientAwayUnit I t).hom).map
      ((moduleSpecΓFunctor (R := quotientAwaySpecRing I t)).map
        ((closedImmersionRightAdjointOpenIso (Spec.map (quotientAwayUnit I t))
          (Spec.map (localizedQuotientSpecMap I t)) (Spec.map (quotientSpecMap I))
          (Spec.map (ambientAwayUnit t)) (quotientLocalizationSquare I t)).hom.app N))

private theorem quotientLocalizationGeoMap_apply (N : (Spec R).Modules)
    (m : (moduleSpecΓFunctor (R := quotientSpecRing I)).obj
      ((closedImmersionRightAdjoint (Spec.map (quotientSpecMap I))).obj N)) :
    quotientLocalizationGeoMap I t N m =
      ((closedImmersionRightAdjointOpenIso (Spec.map (quotientAwayUnit I t))
        (Spec.map (localizedQuotientSpecMap I t)) (Spec.map (quotientSpecMap I))
        (Spec.map (ambientAwayUnit t)) (quotientLocalizationSquare I t)).hom.app N).app ⊤
          (openGlobalRestriction (Spec.map (quotientAwayUnit I t))
            ((closedImmersionRightAdjoint (Spec.map (quotientSpecMap I))).obj N) m) := rfl

private theorem quotient_hom_ext_one {T : ModuleCat.{u} R}
    (f g : ModuleCat.of R (R ⧸ I) ⟶ T)
    (h₁ : f (1 : R ⧸ I) = g (1 : R ⧸ I)) : f = g := by
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  obtain ⟨r, rfl⟩ := Ideal.Quotient.mk_surjective x
  have hr : Ideal.Quotient.mk I r = r • (1 : R ⧸ I) := by simp [Algebra.smul_def]
  rw [hr]
  exact (f.hom.map_smul r (1 : R ⧸ I)).trans
    ((congrArg (fun y => r • y) h₁).trans (g.hom.map_smul r (1 : R ⧸ I)).symm)

private theorem scalarExtensionQuotientAwayIso_one :
    (scalarExtensionQuotientAwayIso I t).hom
      ((1 : Localization.Away t) ⊗ₜ[R,algebraMap R (Localization.Away t)] (1 : R ⧸ I)) =
        (1 : Localization.Away (Ideal.Quotient.mk I t)) := by
  simpa only [map_one] using scalarExtensionQuotientAwayIso_one_tmul I t (1 : R)

private def quotientLocalizationHomMap (N : (Spec R).Modules)
    (m : (moduleSpecΓFunctor (R := quotientAwaySpecRing I t)).obj
      ((closedImmersionRightAdjoint (Spec.map (localizedQuotientSpecMap I t))).obj
        ((restrictFunctor (Spec.map (ambientAwayUnit t))).obj N))) :
    (ModuleCat.restrictScalars (localizedQuotientSpecMap I t).hom).obj
        (ModuleCat.of (quotientAwaySpecRing I t) (quotientAwaySpecRing I t)) ⟶
      (moduleSpecΓFunctor (R := ambientAwayRing t)).obj
        ((restrictFunctor (Spec.map (ambientAwayUnit t))).obj N) where
  hom' := closedImmersionRightAdjointSectionsLinearEquiv (localizedQuotientSpecMap I t)
    ((restrictFunctor (Spec.map (ambientAwayUnit t))).obj N) m

private def quotientGlobalHomMap (N : (Spec R).Modules)
    (m : (moduleSpecΓFunctor (R := quotientSpecRing I)).obj
      ((closedImmersionRightAdjoint (Spec.map (quotientSpecMap I))).obj N)) :
    ModuleCat.of R (R ⧸ I) ⟶ (moduleSpecΓFunctor (R := R)).obj N where
  hom' := closedImmersionRightAdjointSectionsLinearEquiv (quotientSpecMap I) N m

private theorem quotientLocalization_hom_square (N : (Spec R).Modules)
    (m : (moduleSpecΓFunctor (R := quotientSpecRing I)).obj
      ((closedImmersionRightAdjoint (Spec.map (quotientSpecMap I))).obj N)) :
    (ModuleCat.extendRestrictScalarsAdj (ambientAwayUnit t).hom).homEquiv _ _
      ((scalarExtensionQuotientAwayIso I t).hom ≫
        quotientLocalizationHomMap I t N (quotientLocalizationGeoMap I t N m)) =
      quotientGlobalHomMap I N m ≫
        affineOpenRestrictionSectionsMap (ambientAwayUnit t) N := by
  apply quotient_hom_ext_one I
  change closedImmersionRightAdjointSectionsLinearEquiv (localizedQuotientSpecMap I t)
      ((restrictFunctor (Spec.map (ambientAwayUnit t))).obj N)
      (quotientLocalizationGeoMap I t N m)
      ((scalarExtensionQuotientAwayIso I t).hom
        ((1 : Localization.Away t) ⊗ₜ[R,algebraMap R (Localization.Away t)] (1 : R ⧸ I))) =
    affineOpenRestrictionSectionsMap (ambientAwayUnit t) N
      (closedImmersionRightAdjointSectionsLinearEquiv (quotientSpecMap I) N m (1 : R ⧸ I))
  rw [scalarExtensionQuotientAwayIso_one]
  have hl := closedAffine_hom_one (localizedQuotientSpecMap I t)
    ((restrictFunctor (Spec.map (ambientAwayUnit t))).obj N) (quotientLocalizationGeoMap I t N m)
  have hg := closedAffine_hom_one (quotientSpecMap I) N m
  have hl' := hl.trans (congrArg
    ((moduleSpecΓFunctor (R := ambientAwayRing t)).map
      ((closedImmersionRightAdjunction (Spec.map (localizedQuotientSpecMap I t))).counit.app
        ((restrictFunctor (Spec.map (ambientAwayUnit t))).obj N)))
    (pushforwardΓ_inv_apply (localizedQuotientSpecMap I t) _ (quotientLocalizationGeoMap I t N m)))
  have hg' := hg.trans (congrArg
    ((moduleSpecΓFunctor (R := R)).map
      ((closedImmersionRightAdjunction (Spec.map (quotientSpecMap I))).counit.app N))
    (pushforwardΓ_inv_apply (quotientSpecMap I) _ m))
  rw [hl', hg', affineOpenRestrictionSectionsMap_apply, quotientLocalizationGeoMap_apply]
  exact closedRightOpenIso_global_counit (Spec.map (quotientAwayUnit I t))
    (Spec.map (localizedQuotientSpecMap I t)) (Spec.map (quotientSpecMap I))
    (Spec.map (ambientAwayUnit t)) (quotientLocalizationSquare I t) N m

private theorem quotientLocalization_cycle_square (N : (Spec R).Modules)
    (m : (moduleSpecΓFunctor (R := quotientSpecRing I)).obj
      ((closedImmersionRightAdjoint (Spec.map (quotientSpecMap I))).obj N)) :
    quotientLocalizationHomMap I t N (quotientLocalizationGeoMap I t N m) =
      (scalarExtensionQuotientAwayIso I t).inv ≫
        (ModuleCat.extendScalars (ambientAwayUnit t).hom).map (quotientGlobalHomMap I N m) ≫
          (openSpecRestrictionMate (ambientAwayUnit t)).app N := by
  apply (cancel_epi (scalarExtensionQuotientAwayIso I t).hom).mp
  rw [← Category.assoc, (scalarExtensionQuotientAwayIso I t).hom_inv_id, Category.id_comp]
  apply ((ModuleCat.extendRestrictScalarsAdj (ambientAwayUnit t).hom).homEquiv _ _).injective
  rw [Adjunction.homEquiv_naturality_left]
  have hu : (ModuleCat.extendRestrictScalarsAdj (ambientAwayUnit t).hom).homEquiv _ _
      ((openSpecRestrictionMate (ambientAwayUnit t)).app N) =
    affineOpenRestrictionSectionsMap (ambientAwayUnit t) N := by
    simpa only [Adjunction.homEquiv_unit] using
      openSpecRestrictionMate_unit (ambientAwayUnit t) N
  erw [hu]
  exact quotientLocalization_hom_square I t N m
end QuotientLocalization
end AlgebraicGeometry.Scheme.Modules
end

section
namespace AlgebraicGeometry.Scheme.Modules
variable {R A : CommRingCat.{u}} (σ : R ⟶ A) [IsOpenImmersion (Spec.map σ)]
  {L : (Spec R).Modules}

/-- The supplied original resolution restricted along the same open immersion. -/
@[expose] public def affineOpenRestrictedInjectiveResolution (I : InjectiveResolution L) :
    InjectiveResolution ((restrictFunctor (Spec.map σ)).obj L) := by
  let F := restrictFunctor (Spec.map σ)
  letI : QuasiIso (I.mapAugmentation F) := by
    rw [InjectiveResolution.mapAugmentation_eq]
    infer_instance
  exact {
    cocomplex := (F.mapHomologicalComplex (.up ℕ)).obj I.cocomplex
    injective n := by
      change Injective (F.obj (I.cocomplex.X n))
      infer_instance
    ι := I.mapAugmentation F }

private theorem openRestricted_quasicoherent (L : (Spec R).Modules) [L.IsQuasicoherent] :
    ((restrictFunctor (Spec.map σ)).obj L).IsQuasicoherent :=
  (SheafOfModules.isQuasicoherent (Spec A).ringCatSheaf).prop_of_iso
    ((restrictFunctorIsoPullback (Spec.map σ)).symm.app L) (isQuasicoherent_pullback σ L)
variable [L.IsQuasicoherent]

private def localΓResolution (I : InjectiveResolution L) :
    InjectiveResolution ((moduleSpecΓFunctor (R := A)).obj
      ((restrictFunctor (Spec.map σ)).obj L)) := by
  letI := openRestricted_quasicoherent σ L
  exact AffineDerived.globalSectionsInjectiveResolution (affineOpenRestrictedInjectiveResolution σ
    I)

private def actualSectionResolutionLift (I : InjectiveResolution L) :
    ((ModuleCat.extendScalars σ.hom).mapHomologicalComplex (.up ℕ)).obj
        (AffineDerived.globalSectionsInjectiveResolution I).cocomplex ⟶
      (localΓResolution σ I).cocomplex where
  f n := (openSpecRestrictionMate σ).app (I.cocomplex.X n)
  comm' n m _ := by
    change (openSpecRestrictionMate σ).app (I.cocomplex.X n) ≫
        moduleSpecΓFunctor.map ((restrictFunctor (Spec.map σ)).map (I.cocomplex.d n m)) =
      (ModuleCat.extendScalars σ.hom).map (moduleSpecΓFunctor.map (I.cocomplex.d n m)) ≫
        (openSpecRestrictionMate σ).app (I.cocomplex.X m)
    exact ((openSpecRestrictionMate σ).naturality (I.cocomplex.d n m)).symm

private theorem actualSectionResolutionLift_augmentation (I : InjectiveResolution L) :
    (ModuleCat.extendScalars σ.hom).map
        ((AffineDerived.globalSectionsInjectiveResolution I).ι.f 0) ≫
      (actualSectionResolutionLift σ I).f 0 =
    (openSpecRestrictionMate σ).app L ≫ (localΓResolution σ I).ι.f 0 := by
  change (ModuleCat.extendScalars σ.hom).map
      ((AffineDerived.globalSectionsAugmentation I).f 0) ≫
      (openSpecRestrictionMate σ).app (I.cocomplex.X 0) =
    (openSpecRestrictionMate σ).app L ≫
      (AffineDerived.globalSectionsAugmentation (affineOpenRestrictedInjectiveResolution σ I)).f 0
  rw [AffineDerived.globalSectionsAugmentation_f_zero,
    AffineDerived.globalSectionsAugmentation_f_zero]
  change (ModuleCat.extendScalars σ.hom).map (moduleSpecΓFunctor.map (I.ι.f 0)) ≫
      (openSpecRestrictionMate σ).app (I.cocomplex.X 0) =
    (openSpecRestrictionMate σ).app L ≫ moduleSpecΓFunctor.map
      ((I.mapAugmentation (restrictFunctor (Spec.map σ))).f 0)
  rw [InjectiveResolution.mapAugmentation_f_zero]
  exact (openSpecRestrictionMate σ).naturality (I.ι.f 0)
end AlgebraicGeometry.Scheme.Modules
end

section
open CategoryTheory.Abelian HomologicalComplex
namespace AlgebraicGeometry.Scheme.Modules
section GeometricExt
variable {R : CommRingCat.{u}} (I : Ideal R) (t : R)
  {L : (Spec R).Modules} [L.IsQuasicoherent] (J : InjectiveResolution L)

private theorem ambientAway_flat : (ambientAwayUnit t).hom.Flat :=
  RingHom.flat_algebraMap_iff.mpr
    (IsLocalization.flat (Localization.Away t) (Submonoid.powers t))
local instance : PreservesFiniteLimits (ModuleCat.extendScalars (ambientAwayUnit t).hom) :=
  ModuleCat.extendScalars_preservesFiniteLimits_of_flat _ (ambientAway_flat t)
local instance : PreservesFiniteColimits (ModuleCat.extendScalars (ambientAwayUnit t).hom) :=
  ModuleCat.extendScalars_preservesFiniteColimits_of_flat _ (ambientAway_flat t)

private theorem quotientLocalization_mapped_cycle (n : ℕ)
    (m : (moduleSpecΓFunctor (R := quotientSpecRing I)).obj
      ((closedImmersionRightAdjoint (Spec.map (quotientSpecMap I))).obj (J.cocomplex.X n)))
    (hf : quotientGlobalHomMap I (J.cocomplex.X n) m ≫
      (AffineDerived.globalSectionsInjectiveResolution J).cocomplex.d n (n + 1) = 0) :
    quotientLocalizationHomMap I t (J.cocomplex.X n)
        (quotientLocalizationGeoMap I t (J.cocomplex.X n) m) ≫
      (localΓResolution (ambientAwayUnit t) J).cocomplex.d n (n + 1) = 0 := by
  have hc := CategoryTheory.InjectiveResolution.ExactFunctor.mappedCycle_comp_d
    (F := ModuleCat.extendScalars (ambientAwayUnit t).hom)
    (R := AffineDerived.globalSectionsInjectiveResolution J)
    (S := localΓResolution (ambientAwayUnit t) J)
    (actualSectionResolutionLift (ambientAwayUnit t) J) n
    (quotientGlobalHomMap I (J.cocomplex.X n) m) hf
  rw [quotientLocalization_cycle_square]
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  exact ConcreteCategory.congr_hom hc ((scalarExtensionQuotientAwayIso I t).inv x)
variable [HasExt.{w} (ModuleCat.{u} R)]
  [HasExt.{z} (ModuleCat.{u} (ambientAwayRing t))]

private theorem quotientLocalization_extMk_square (n : ℕ)
    (m : (moduleSpecΓFunctor (R := quotientSpecRing I)).obj
      ((closedImmersionRightAdjoint (Spec.map (quotientSpecMap I))).obj (J.cocomplex.X n)))
    (hf : quotientGlobalHomMap I (J.cocomplex.X n) m ≫
      (AffineDerived.globalSectionsInjectiveResolution J).cocomplex.d n (n + 1) = 0) :
    ((Ext.mk₀ (scalarExtensionQuotientAwayIso I t).inv).comp
      (((AffineDerived.globalSectionsInjectiveResolution J).extMk
        (quotientGlobalHomMap I (J.cocomplex.X n) m) (n + 1) rfl hf :
          Ext.{w} (ModuleCat.of R (R ⧸ I)) (moduleSpecΓFunctor.obj L) n).mapExactFunctor
            (ModuleCat.extendScalars (ambientAwayUnit t).hom)) (Nat.zero_add n)).comp
      (Ext.mk₀ ((openSpecRestrictionMate (ambientAwayUnit t)).app L)) (Nat.add_zero n) =
    ((localΓResolution (ambientAwayUnit t) J).extMk
      (quotientLocalizationHomMap I t (J.cocomplex.X n)
        (quotientLocalizationGeoMap I t (J.cocomplex.X n) m)) (n + 1) rfl
      (quotientLocalization_mapped_cycle I t J n m hf) :
        Ext.{z}
          ((ModuleCat.restrictScalars (localizedQuotientSpecMap I t).hom).obj
            (ModuleCat.of (quotientAwaySpecRing I t) (quotientAwaySpecRing I t)))
          ((moduleSpecΓFunctor (R := ambientAwayRing t)).obj
            ((restrictFunctor (Spec.map (ambientAwayUnit t))).obj L)) n) := by
  have h := CategoryTheory.InjectiveResolution.ExactFunctor.mk₀_comp_extMk_mapExactFunctor_comp_mk₀
    (ModuleCat.extendScalars (ambientAwayUnit t).hom)
    (AffineDerived.globalSectionsInjectiveResolution J)
    (localΓResolution (ambientAwayUnit t) J)
    ((openSpecRestrictionMate (ambientAwayUnit t)).app L)
    (actualSectionResolutionLift (ambientAwayUnit t) J)
    (actualSectionResolutionLift_augmentation (ambientAwayUnit t) J)
    (quotientGlobalHomMap I (J.cocomplex.X n) m) hf
    (scalarExtensionQuotientAwayIso I t).inv
  have he := quotientLocalization_cycle_square I t (J.cocomplex.X n) m
  change _ = (scalarExtensionQuotientAwayIso I t).inv ≫
      (ModuleCat.extendScalars (ambientAwayUnit t).hom).map
        (quotientGlobalHomMap I (J.cocomplex.X n) m) ≫
      (actualSectionResolutionLift (ambientAwayUnit t) J).f n at he
  simpa only [← he] using h
end GeometricExt
end AlgebraicGeometry.Scheme.Modules
end
open CategoryTheory.Abelian HomologicalComplex CochainComplex CochainComplex.HomComplex
namespace AlgebraicGeometry.Scheme.Modules
section AffineResolutionComplex
variable {R S : CommRingCat.{u}} (φ : R ⟶ S) [IsClosedImmersion (Spec.map φ)]
  {L : (Spec R).Modules} [L.IsQuasicoherent] (J : InjectiveResolution L)

/-- Original affine closed-adjoint sections and native extension of the supplied resolution. -/
@[expose] public def affineClosedRightAdjointResolutionSectionsIso :
    ((moduleSpecΓFunctor (R := S)).mapHomologicalComplex (.up ℤ)).obj
      (((closedImmersionRightAdjoint (Spec.map φ)).mapHomologicalComplex (.up ℤ)).obj
        J.cochainComplex) ≅
      ((ModuleCat.coextendScalars φ.hom).mapHomologicalComplex (.up ℤ)).obj
        (AffineDerived.globalSectionsInjectiveResolution J).cochainComplex :=
  (Functor.mapHomologicalComplexCompIso (closedImmersionRightAdjointAffineIso φ)
      (.up ℤ)).app J.cochainComplex ≪≫
    ((Functor.mapHomologicalComplexCompIso
      (Iso.refl (moduleSpecΓFunctor (R := R) ⋙ ModuleCat.coextendScalars φ.hom))
        (.up ℤ)).app J.cochainComplex).symm ≪≫
    ((ModuleCat.coextendScalars φ.hom).mapHomologicalComplex (.up ℤ)).mapIso
      (J.cocomplex.mapExtendIso (moduleSpecΓFunctor (R := R)) ComplexShape.embeddingUpNat)

public theorem affineClosedRightAdjointResolutionSectionsIso_hom_f (n : ℕ) :
    (affineClosedRightAdjointResolutionSectionsIso φ J).hom.f (n : ℤ) ≫
      (ModuleCat.coextendScalars φ.hom).map
        ((AffineDerived.globalSectionsInjectiveResolution J).cochainComplexXIso n n rfl).hom =
    (closedImmersionRightAdjointAffineIso φ).hom.app (J.cochainComplex.X (n : ℤ)) ≫
      (ModuleCat.coextendScalars φ.hom).map
        (moduleSpecΓFunctor.map (J.cochainComplexXIso n n rfl).hom) := by
  change (closedImmersionRightAdjointAffineIso φ).hom.app (J.cochainComplex.X (n : ℤ)) ≫
      (ModuleCat.coextendScalars φ.hom).map
        ((J.cocomplex.mapExtendIso (moduleSpecΓFunctor (R := R))
          ComplexShape.embeddingUpNat).hom.f (n : ℤ)) ≫
      (ModuleCat.coextendScalars φ.hom).map
        ((((moduleSpecΓFunctor (R := R)).mapHomologicalComplex (.up ℕ)).obj
          J.cocomplex).extendXIso ComplexShape.embeddingUpNat (show (n : ℤ) = n from rfl)).hom = _
  rw [← Functor.map_comp]
  exact congrArg (fun p =>
    (closedImmersionRightAdjointAffineIso φ).hom.app (J.cochainComplex.X (n : ℤ)) ≫
      (ModuleCat.coextendScalars φ.hom).map p)
    (J.cocomplex.mapExtendIso_hom_f_extendXIso (moduleSpecΓFunctor (R := R))
      ComplexShape.embeddingUpNat (i := n) (j := (n : ℤ)) rfl)
variable [HasExt.{w} (ModuleCat.{u} R)]

/-- Native Ext computed by the original closed-adjoint resolution sections. -/
@[expose] public def affineClosedRightAdjointResolutionExtAddEquiv (n : ℕ) :
    (((moduleSpecΓFunctor (R := S)).mapHomologicalComplex (.up ℤ)).obj
      (((closedImmersionRightAdjoint (Spec.map φ)).mapHomologicalComplex (.up ℤ)).obj
        J.cochainComplex)).homology (n : ℤ) ≃+
      Ext.{w} ((ModuleCat.restrictScalars φ.hom).obj (ModuleCat.of S S))
        (moduleSpecΓFunctor.obj L) n :=
  ((homologyFunctor (ModuleCat.{u} S) (.up ℤ) (n : ℤ)).mapIso
    (affineClosedRightAdjointResolutionSectionsIso φ J)).toLinearEquiv.toAddEquiv.trans
      (ModuleCat.coextendScalarsResolutionExtAddEquiv φ.hom
        (AffineDerived.globalSectionsInjectiveResolution J) n)

/-- The original Ext comparison with its native source-ring scalar action. -/
@[expose] public def affineClosedRightAdjointResolutionExtLinearEquiv (n : ℕ) :
    (ModuleCat.restrictScalars φ.hom).obj
      ((((moduleSpecΓFunctor (R := S)).mapHomologicalComplex (.up ℤ)).obj
        (((closedImmersionRightAdjoint (Spec.map φ)).mapHomologicalComplex (.up ℤ)).obj
          J.cochainComplex)).homology (n : ℤ)) ≃ₗ[R]
      Ext.{w} ((ModuleCat.restrictScalars φ.hom).obj (ModuleCat.of S S))
        (moduleSpecΓFunctor.obj L) n where
  __ := affineClosedRightAdjointResolutionExtAddEquiv φ J n
  map_smul' r x := by
    let E := ModuleCat.coextendScalarsResolutionExtAddEquiv φ.hom
      (AffineDerived.globalSectionsInjectiveResolution J) n
    let e := (homologyFunctor (ModuleCat.{u} S) (.up ℤ) (n : ℤ)).mapIso
      (affineClosedRightAdjointResolutionSectionsIso φ J)
    change E (e.hom (φ.hom r • x)) = r • E (e.hom x)
    rw [e.hom.hom.map_smul, ModuleCat.coextendScalarsResolutionExtAddEquiv_smul]
    have hm : (ModuleCat.restrictScalars φ.hom).map
        (ModuleCat.ofHom (X := ModuleCat.of S S) (Y := ModuleCat.of S S)
          (LinearMap.mulRight S (φ.hom r))) =
        r • 𝟙 ((ModuleCat.restrictScalars φ.hom).obj (ModuleCat.of S S)) := by
      apply ModuleCat.hom_ext
      apply LinearMap.ext
      intro y
      change (show S from y) * φ.hom r = φ.hom r * (show S from y)
      exact mul_comm _ _
    rw [hm]
    simp only [Ext.mk₀_smul, Ext.smul_comp, Ext.mk₀_id_comp]
    rfl
end AffineResolutionComplex
end AlgebraicGeometry.Scheme.Modules
open CategoryTheory.Abelian HomologicalComplex CochainComplex CochainComplex.HomComplex
namespace AlgebraicGeometry.Scheme.Modules
section OriginalCycles
variable {R S : CommRingCat.{u}} (φ : R ⟶ S) [IsClosedImmersion (Spec.map φ)]
  {L : (Spec R).Modules} [L.IsQuasicoherent] (J : InjectiveResolution L)

private abbrev closedΓResolutionComplex :=
  ((moduleSpecΓFunctor (R := S)).mapHomologicalComplex (.up ℤ)).obj
    (((closedImmersionRightAdjoint (Spec.map φ)).mapHomologicalComplex (.up ℤ)).obj
      J.cochainComplex)

private def closedΓTermHom (N : (Spec R).Modules)
    (m : (moduleSpecΓFunctor (R := S)).obj
      ((closedImmersionRightAdjoint (Spec.map φ)).obj N)) :
    (ModuleCat.restrictScalars φ.hom).obj (ModuleCat.of S S) ⟶ moduleSpecΓFunctor.obj N where
  hom' := closedImmersionRightAdjointSectionsLinearEquiv φ N m

private theorem closedΓResolutionIso_hom_f_hom (n : ℕ)
    (m : (closedΓResolutionComplex φ J).X (n : ℤ)) :
    ModuleCat.ofHom
        (X := (ModuleCat.restrictScalars φ.hom).obj (ModuleCat.of S S))
        (Y := (AffineDerived.globalSectionsInjectiveResolution J).cochainComplex.X (n : ℤ))
        (ModuleCat.CoextendScalars.equiv φ.hom _ ((affineClosedRightAdjointResolutionSectionsIso φ
          J).hom.f n m)) ≫
      ((AffineDerived.globalSectionsInjectiveResolution J).cochainComplexXIso n n rfl).hom =
    closedΓTermHom φ (J.cocomplex.X n)
      (moduleSpecΓFunctor.map
        ((closedImmersionRightAdjoint (Spec.map φ)).map (J.cochainComplexXIso n n rfl).hom) m) := by
  have h₁ := ConcreteCategory.congr_hom (affineClosedRightAdjointResolutionSectionsIso_hom_f φ J
    n) m
  have h₂ := ConcreteCategory.congr_hom
    ((closedImmersionRightAdjointAffineIso φ).hom.naturality
      (J.cochainComplexXIso n n rfl).hom) m
  have h := h₁.trans h₂.symm
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro b
  exact congrArg (fun x => ModuleCat.CoextendScalars.equiv φ.hom
    ((AffineDerived.globalSectionsInjectiveResolution J).cocomplex.X n) x b) h

private def closedΓResolutionCycle (n : ℕ)
    (f : (ModuleCat.restrictScalars φ.hom).obj (ModuleCat.of S S) ⟶
      (AffineDerived.globalSectionsInjectiveResolution J).cocomplex.X n)
    (hf : f ≫ (AffineDerived.globalSectionsInjectiveResolution J).cocomplex.d n (n + 1) = 0) :
    (closedΓResolutionComplex φ J).cycles (n : ℤ) :=
  ((cyclesFunctor (ModuleCat.{u} S) (.up ℤ) (n : ℤ)).mapIso
      (affineClosedRightAdjointResolutionSectionsIso φ J)).inv
    ((ModuleCat.coextendScalarsCyclesIso φ.hom
      (AffineDerived.globalSectionsInjectiveResolution J).cochainComplex (n : ℤ)).inv
      (Cocycle.fromSingleMk
        (f ≫ ((AffineDerived.globalSectionsInjectiveResolution J).cochainComplexXIso n n rfl).inv)
        (zero_add _) ((n + 1 : ℕ) : ℤ) (by lia)
        (by
          rw [InjectiveResolution.cochainComplex_d _ _ _ n (n + 1) rfl rfl]
          simp only [Category.assoc, Iso.inv_hom_id_assoc, reassoc_of% hf, zero_comp])))

private theorem closedΓResolutionCycle_term (n : ℕ)
    (f : (ModuleCat.restrictScalars φ.hom).obj (ModuleCat.of S S) ⟶
      (AffineDerived.globalSectionsInjectiveResolution J).cocomplex.X n)
    (hf : f ≫ (AffineDerived.globalSectionsInjectiveResolution J).cocomplex.d n (n + 1) = 0) :
    moduleSpecΓFunctor.map
        ((closedImmersionRightAdjoint (Spec.map φ)).map (J.cochainComplexXIso n n rfl).hom)
      ((closedΓResolutionComplex φ J).iCycles (n : ℤ) (closedΓResolutionCycle φ J n f hf)) =
    (closedImmersionRightAdjointSectionsLinearEquiv φ (J.cocomplex.X n)).symm f.hom := by
  let IR := AffineDerived.globalSectionsInjectiveResolution J
  let K := closedΓResolutionComplex φ J
  let C := ((ModuleCat.coextendScalars φ.hom).mapHomologicalComplex (.up ℤ)).obj IR.cochainComplex
  let e := affineClosedRightAdjointResolutionSectionsIso φ J
  let ce := (cyclesFunctor (ModuleCat.{u} S) (.up ℤ) (n : ℤ)).mapIso e
  let cc := ModuleCat.coextendScalarsCyclesIso φ.hom IR.cochainComplex (n : ℤ)
  let c := Cocycle.fromSingleMk (f ≫ (IR.cochainComplexXIso n n rfl).inv)
    (zero_add _) ((n + 1 : ℕ) : ℤ) (by lia)
    (by
      rw [InjectiveResolution.cochainComplex_d _ _ _ n (n + 1) rfl rfl]
      simp only [Category.assoc, Iso.inv_hom_id_assoc]
      have hz := congrArg
        (fun p => p ≫ (IR.cochainComplexXIso ((n + 1 : ℕ) : ℤ) (n + 1) rfl).inv)
        (show f ≫ IR.cocomplex.d n (n + 1) = 0 from hf)
      simpa only [Category.assoc, zero_comp] using hz)
  let z := closedΓResolutionCycle φ J n f hf
  have hzc : ce.hom z = cc.inv c := Iso.inv_hom_id_apply ce (cc.inv c)
  have hp : e.hom.f (n : ℤ) (K.iCycles (n : ℤ) z) =
      C.iCycles (n : ℤ) (cc.inv c) := by
    have h := ConcreteCategory.congr_hom (cyclesMap_i e.hom (n : ℤ)) z
    exact h.symm.trans (congrArg (fun y => C.iCycles (n : ℤ) y) hzc)
  have hc := congrArg Subtype.val (Iso.inv_hom_id_apply cc c)
  change ((ModuleCat.coextendScalarsCyclesIso φ.hom IR.cochainComplex (n : ℤ)).hom
    (cc.inv c)).1 = c.1 at hc
  rw [ModuleCat.coextendScalarsCyclesIso_coe,
    ModuleCat.coextendScalarsCochainEquiv_apply] at hc
  have hc' : ModuleCat.ofHom
      (X := (ModuleCat.restrictScalars φ.hom).obj (ModuleCat.of S S))
      (Y := IR.cochainComplex.X (n : ℤ))
      (ModuleCat.CoextendScalars.equiv φ.hom _ (C.iCycles (n : ℤ) (cc.inv c))) =
      f ≫ (IR.cochainComplexXIso n n rfl).inv :=
    (Cochain.fromSingleEquiv (zero_add (n : ℤ))).symm.injective hc
  have hterm := closedΓResolutionIso_hom_f_hom φ J n (K.iCycles (n : ℤ) z)
  change ModuleCat.ofHom
      (X := (ModuleCat.restrictScalars φ.hom).obj (ModuleCat.of S S))
      (Y := IR.cochainComplex.X (n : ℤ))
      (ModuleCat.CoextendScalars.equiv φ.hom _ (e.hom.f (n : ℤ) (K.iCycles (n : ℤ) z))) ≫
      (IR.cochainComplexXIso n n rfl).hom = _ at hterm
  rw [hp, hc'] at hterm
  simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id] at hterm
  apply (closedImmersionRightAdjointSectionsLinearEquiv φ (J.cocomplex.X n)).injective
  rw [LinearEquiv.apply_symm_apply]
  exact congrArg ModuleCat.Hom.hom hterm.symm
variable [HasExt.{w} (ModuleCat.{u} R)]

private theorem closedΓResolutionCycle_class (n : ℕ)
    (f : (ModuleCat.restrictScalars φ.hom).obj (ModuleCat.of S S) ⟶
      (AffineDerived.globalSectionsInjectiveResolution J).cocomplex.X n)
    (hf : f ≫ (AffineDerived.globalSectionsInjectiveResolution J).cocomplex.d n (n + 1) = 0) :
    affineClosedRightAdjointResolutionExtAddEquiv φ J n
        ((closedΓResolutionComplex φ J).homologyπ (n : ℤ)
          (closedΓResolutionCycle φ J n f hf)) =
      (AffineDerived.globalSectionsInjectiveResolution J).extMk f (n + 1) rfl hf := by
  let K := closedΓResolutionComplex φ J
  let C := ((ModuleCat.coextendScalars φ.hom).mapHomologicalComplex (.up ℤ)).obj
    (AffineDerived.globalSectionsInjectiveResolution J).cochainComplex
  let e := (affineClosedRightAdjointResolutionSectionsIso φ J)
  let ce := (cyclesFunctor (ModuleCat.{u} S) (.up ℤ) (n : ℤ)).mapIso e
  let c := Cocycle.fromSingleMk
    (f ≫ ((AffineDerived.globalSectionsInjectiveResolution J).cochainComplexXIso n n rfl).inv)
    (zero_add _) ((n + 1 : ℕ) : ℤ) (by lia)
    (by
      rw [InjectiveResolution.cochainComplex_d _ _ _ n (n + 1) rfl rfl]
      simp only [Category.assoc, Iso.inv_hom_id_assoc, reassoc_of% hf, zero_comp])
  let z := (ModuleCat.coextendScalarsCyclesIso φ.hom
    (AffineDerived.globalSectionsInjectiveResolution J).cochainComplex (n : ℤ)).inv c
  have hp : homologyMap e.hom (n : ℤ) (K.homologyπ (n : ℤ) (ce.inv z)) =
      C.homologyπ (n : ℤ) z := by
    have h := ConcreteCategory.congr_hom (homologyπ_naturality e.hom (n : ℤ)) (ce.inv z)
    exact h.trans (congrArg (fun y => C.homologyπ (n : ℤ) y)
      (Iso.inv_hom_id_apply ce z))
  change ModuleCat.coextendScalarsResolutionExtAddEquiv φ.hom
    (AffineDerived.globalSectionsInjectiveResolution J) n
      (homologyMap e.hom (n : ℤ) (K.homologyπ (n : ℤ) (ce.inv z))) = _
  rw [hp, ModuleCat.coextendScalarsResolutionExtAddEquiv_homologyπ,
    Iso.inv_hom_id_apply]
  rfl
end OriginalCycles
end AlgebraicGeometry.Scheme.Modules
open CategoryTheory.Abelian HomologicalComplex CochainComplex
namespace AlgebraicGeometry.Scheme.Modules
section GeometricComplex
variable {R : CommRingCat.{u}} (I : Ideal R) (t : R)
  {L : (Spec R).Modules} [L.IsQuasicoherent] (J : InjectiveResolution L)
local instance : IsClosedImmersion (Spec.map (localizedQuotientSpecMap I t)) :=
  Scheme.isClosedImmersion_specMap_localizationAway (quotientSpecMap I) t
local instance : (moduleSpecΓFunctor (R := quotientAwaySpecRing I t)).Additive :=
  moduleSpecΓFunctor_additive (quotientAwaySpecRing I t)

private def quotientLocalizationGeoNat :
    closedImmersionRightAdjoint (Spec.map (quotientSpecMap I)) ⋙
        moduleSpecΓFunctor (R := quotientSpecRing I) ⟶
      (restrictFunctor (Spec.map (ambientAwayUnit t)) ⋙
        closedImmersionRightAdjoint (Spec.map (localizedQuotientSpecMap I t))) ⋙
        (moduleSpecΓFunctor (R := quotientAwaySpecRing I t) ⋙
          ModuleCat.restrictScalars (quotientAwayUnit I t).hom) :=
  Functor.whiskerLeft (closedImmersionRightAdjoint (Spec.map (quotientSpecMap I)))
      (affineOpenRestrictionSectionsNat (quotientAwayUnit I t)) ≫
    (Functor.associator (closedImmersionRightAdjoint (Spec.map (quotientSpecMap I)))
      (restrictFunctor (Spec.map (quotientAwayUnit I t)))
      (moduleSpecΓFunctor (R := quotientAwaySpecRing I t) ⋙
        ModuleCat.restrictScalars (quotientAwayUnit I t).hom)).inv ≫
    Functor.whiskerRight
      (closedImmersionRightAdjointOpenIso (Spec.map (quotientAwayUnit I t))
        (Spec.map (localizedQuotientSpecMap I t)) (Spec.map (quotientSpecMap I))
        (Spec.map (ambientAwayUnit t)) (quotientLocalizationSquare I t)).hom
      (moduleSpecΓFunctor (R := quotientAwaySpecRing I t) ⋙
        ModuleCat.restrictScalars (quotientAwayUnit I t).hom)

private theorem quotientLocalizationGeoNat_app (N : (Spec R).Modules) :
    (quotientLocalizationGeoNat I t).app N = quotientLocalizationGeoMap I t N := by
  simp only [quotientLocalizationGeoNat, NatTrans.comp_app, Functor.whiskerLeft_app,
    Functor.associator_inv_app, Functor.whiskerRight_app, Category.id_comp,
    affineOpenRestrictionSectionsNat_app]
  rfl

private def openRestrictedCochainIso :
    ((restrictFunctor (Spec.map (ambientAwayUnit t))).mapHomologicalComplex (.up ℤ)).obj
        J.cochainComplex ≅
      (affineOpenRestrictedInjectiveResolution (ambientAwayUnit t) J).cochainComplex :=
  J.cocomplex.mapExtendIso (restrictFunctor (Spec.map (ambientAwayUnit t)))
    ComplexShape.embeddingUpNat

omit [L.IsQuasicoherent] in
private theorem openRestrictedCochainIso_f (n : ℕ) :
    (openRestrictedCochainIso t J).hom.f (n : ℤ) ≫
        ((affineOpenRestrictedInjectiveResolution (ambientAwayUnit t) J).cochainComplexXIso n n
          rfl).hom =
      (restrictFunctor (Spec.map (ambientAwayUnit t))).map (J.cochainComplexXIso n n rfl).hom := by
  exact J.cocomplex.mapExtendIso_hom_f_extendXIso
    (restrictFunctor (Spec.map (ambientAwayUnit t))) ComplexShape.embeddingUpNat
      (i := n) (j := (n : ℤ)) rfl

private def quotientLocalizationGeoRawComplex :
    closedΓResolutionComplex (quotientSpecMap I) J ⟶
      ((ModuleCat.restrictScalars (quotientAwayUnit I t).hom).mapHomologicalComplex (.up ℤ)).obj
        (((moduleSpecΓFunctor (R := quotientAwaySpecRing I t)).mapHomologicalComplex (.up ℤ)).obj
          (((closedImmersionRightAdjoint (Spec.map (localizedQuotientSpecMap I
            t))).mapHomologicalComplex
            (.up ℤ)).obj
            (((restrictFunctor (Spec.map (ambientAwayUnit t))).mapHomologicalComplex (.up ℤ)).obj
              J.cochainComplex))) where
  f n := quotientLocalizationGeoMap I t (J.cochainComplex.X n)
  comm' n m _ := by
    have h := (quotientLocalizationGeoNat I t).naturality (J.cochainComplex.d n m)
    simp only [quotientLocalizationGeoNat_app] at h
    exact h.symm

private def quotientLocalizationGeoComplex :
    closedΓResolutionComplex (quotientSpecMap I) J ⟶
      ((ModuleCat.restrictScalars (quotientAwayUnit I t).hom).mapHomologicalComplex (.up ℤ)).obj
        (closedΓResolutionComplex (localizedQuotientSpecMap I t)
          (affineOpenRestrictedInjectiveResolution (ambientAwayUnit t) J)) :=
  quotientLocalizationGeoRawComplex I t J ≫
    ((ModuleCat.restrictScalars (quotientAwayUnit I t).hom).mapHomologicalComplex (.up ℤ)).map
      (((moduleSpecΓFunctor (R := quotientAwaySpecRing I t)).mapHomologicalComplex (.up ℤ)).map
        (((closedImmersionRightAdjoint (Spec.map (localizedQuotientSpecMap I
          t))).mapHomologicalComplex
          (.up ℤ)).map (openRestrictedCochainIso t J).hom))

omit [L.IsQuasicoherent] in
private theorem quotientLocalizationGeoComplex_term (n : ℕ)
    (m : (closedΓResolutionComplex (quotientSpecMap I) J).X (n : ℤ)) :
    moduleSpecΓFunctor.map
        ((closedImmersionRightAdjoint (Spec.map (localizedQuotientSpecMap I t))).map
          ((affineOpenRestrictedInjectiveResolution (ambientAwayUnit t) J).cochainComplexXIso n n
            rfl).hom)
      ((quotientLocalizationGeoComplex I t J).f (n : ℤ) m) =
    quotientLocalizationGeoMap I t (J.cocomplex.X n)
      (moduleSpecΓFunctor.map
        ((closedImmersionRightAdjoint (Spec.map (quotientSpecMap I))).map
          (J.cochainComplexXIso n n rfl).hom) m) := by
  have h := ConcreteCategory.congr_hom
    ((quotientLocalizationGeoNat I t).naturality (J.cochainComplexXIso n n rfl).hom) m
  simp only [quotientLocalizationGeoNat_app] at h
  have he := openRestrictedCochainIso_f t J n
  change moduleSpecΓFunctor.map
      ((closedImmersionRightAdjoint (Spec.map (localizedQuotientSpecMap I t))).map
        ((affineOpenRestrictedInjectiveResolution (ambientAwayUnit t) J).cochainComplexXIso n n
          rfl).hom)
    (moduleSpecΓFunctor.map
      ((closedImmersionRightAdjoint (Spec.map (localizedQuotientSpecMap I t))).map
        ((openRestrictedCochainIso t J).hom.f (n : ℤ)))
      (quotientLocalizationGeoMap I t (J.cochainComplex.X (n : ℤ)) m)) = _
  rw [← ModuleCat.comp_apply, ← Functor.map_comp, ← Functor.map_comp, he]
  exact h.symm
end GeometricComplex
end AlgebraicGeometry.Scheme.Modules
open CategoryTheory.Abelian HomologicalComplex CochainComplex
namespace AlgebraicGeometry.Scheme.Modules
section GeometricHomology
variable {R : CommRingCat.{u}} (I : Ideal R) (t : R)
  {L : (Spec R).Modules} [L.IsQuasicoherent] (J : InjectiveResolution L)
local instance : IsClosedImmersion (Spec.map (localizedQuotientSpecMap I t)) :=
  Scheme.isClosedImmersion_specMap_localizationAway (quotientSpecMap I) t
local instance : (moduleSpecΓFunctor (R := quotientAwaySpecRing I t)).Additive :=
  moduleSpecΓFunctor_additive (quotientAwaySpecRing I t)
local instance : ((restrictFunctor (Spec.map (ambientAwayUnit t))).obj L).IsQuasicoherent :=
  openRestricted_quasicoherent (ambientAwayUnit t) L

private abbrev quotientLocalΓComplex :=
  closedΓResolutionComplex (localizedQuotientSpecMap I t)
    (affineOpenRestrictedInjectiveResolution (ambientAwayUnit t) J)

private def quotientLocalizationGeoCycles (n : ℤ)
    (z : (closedΓResolutionComplex (quotientSpecMap I) J).cycles n) :
    (quotientLocalΓComplex I t J).cycles n :=
  (((quotientLocalΓComplex I t J).sc n).mapCyclesIso
      (ModuleCat.restrictScalars (quotientAwayUnit I t).hom)).hom
    (cyclesMap (quotientLocalizationGeoComplex I t J) n z)

private def quotientLocalizationGeoHomology (n : ℤ) :
    (closedΓResolutionComplex (quotientSpecMap I) J).homology n ⟶
      (ModuleCat.restrictScalars (quotientAwayUnit I t).hom).obj
        ((quotientLocalΓComplex I t J).homology n) :=
  homologyMap (quotientLocalizationGeoComplex I t J) n ≫
    (((quotientLocalΓComplex I t J).sc n).mapHomologyIso
      (ModuleCat.restrictScalars (quotientAwayUnit I t).hom)).hom

omit [L.IsQuasicoherent] in
private theorem quotientLocalizationGeoCycles_i (n : ℤ)
    (z : (closedΓResolutionComplex (quotientSpecMap I) J).cycles n) :
    (quotientLocalΓComplex I t J).iCycles n (quotientLocalizationGeoCycles I t J n z) =
      (quotientLocalizationGeoComplex I t J).f n
        ((closedΓResolutionComplex (quotientSpecMap I) J).iCycles n z) := by
  have h₁ := ConcreteCategory.congr_hom
    (((quotientLocalΓComplex I t J).sc n).mapCyclesIso_hom_iCycles
      (ModuleCat.restrictScalars (quotientAwayUnit I t).hom))
    (cyclesMap (quotientLocalizationGeoComplex I t J) n z)
  have h₂ := ConcreteCategory.congr_hom
    (cyclesMap_i (quotientLocalizationGeoComplex I t J) n) z
  exact h₁.trans h₂

omit [L.IsQuasicoherent] in
private theorem quotientLocalizationGeoHomology_π (n : ℤ)
    (z : (closedΓResolutionComplex (quotientSpecMap I) J).cycles n) :
    quotientLocalizationGeoHomology I t J n
        ((closedΓResolutionComplex (quotientSpecMap I) J).homologyπ n z) =
      (quotientLocalΓComplex I t J).homologyπ n
        (quotientLocalizationGeoCycles I t J n z) := by
  have h₁ := ConcreteCategory.congr_hom
    (homologyπ_naturality (quotientLocalizationGeoComplex I t J) n) z
  have h₂ := ConcreteCategory.congr_hom
    (ShortComplex.homologyπ_mapHomologyIso_hom
      (ModuleCat.restrictScalars (quotientAwayUnit I t).hom)
      ((quotientLocalΓComplex I t J).sc n))
    (cyclesMap (quotientLocalizationGeoComplex I t J) n z)
  exact (congrArg
    (fun y => (((quotientLocalΓComplex I t J).sc n).mapHomologyIso
      (ModuleCat.restrictScalars (quotientAwayUnit I t).hom)).hom y) h₁).trans h₂

private theorem quotientLocalizationGeoCycles_class (n : ℕ)
    (m : (moduleSpecΓFunctor (R := quotientSpecRing I)).obj
      ((closedImmersionRightAdjoint (Spec.map (quotientSpecMap I))).obj (J.cocomplex.X n)))
    (hf : quotientGlobalHomMap I (J.cocomplex.X n) m ≫
      (AffineDerived.globalSectionsInjectiveResolution J).cocomplex.d n (n + 1) = 0) :
    quotientLocalizationGeoCycles I t J (n : ℤ)
        (closedΓResolutionCycle (quotientSpecMap I) J n
          (quotientGlobalHomMap I (J.cocomplex.X n) m) hf) =
      closedΓResolutionCycle (localizedQuotientSpecMap I t)
        (affineOpenRestrictedInjectiveResolution (ambientAwayUnit t) J) n
        (quotientLocalizationHomMap I t (J.cocomplex.X n)
          (quotientLocalizationGeoMap I t (J.cocomplex.X n) m))
        (quotientLocalization_mapped_cycle I t J n m hf) := by
  apply (ModuleCat.mono_iff_injective ((quotientLocalΓComplex I t J).iCycles (n : ℤ))).mp
    inferInstance
  apply (ConcreteCategory.bijective_of_isIso
    (moduleSpecΓFunctor.map
      ((closedImmersionRightAdjoint (Spec.map (localizedQuotientSpecMap I t))).map
        ((affineOpenRestrictedInjectiveResolution (ambientAwayUnit t) J).cochainComplexXIso n n
          rfl).hom))).1
  rw [quotientLocalizationGeoCycles_i, quotientLocalizationGeoComplex_term,
    closedΓResolutionCycle_term, closedΓResolutionCycle_term]
  change quotientLocalizationGeoMap I t (J.cocomplex.X n)
      ((closedImmersionRightAdjointSectionsLinearEquiv (quotientSpecMap I)
        (J.cocomplex.X n)).symm
          (closedImmersionRightAdjointSectionsLinearEquiv (quotientSpecMap I)
            (J.cocomplex.X n) m)) =
    (closedImmersionRightAdjointSectionsLinearEquiv (localizedQuotientSpecMap I t)
      ((restrictFunctor (Spec.map (ambientAwayUnit t))).obj (J.cocomplex.X n))).symm
      (closedImmersionRightAdjointSectionsLinearEquiv (localizedQuotientSpecMap I t)
        ((restrictFunctor (Spec.map (ambientAwayUnit t))).obj (J.cocomplex.X n))
        (quotientLocalizationGeoMap I t (J.cocomplex.X n) m))
  rw [LinearEquiv.symm_apply_apply, LinearEquiv.symm_apply_apply]
end GeometricHomology
end AlgebraicGeometry.Scheme.Modules
open CategoryTheory.Abelian HomologicalComplex CochainComplex
namespace AlgebraicGeometry.Scheme.Modules
section GeometricHomologyExt
variable {R : CommRingCat.{u}} (I : Ideal R) (t : R)
  {L : (Spec R).Modules} [L.IsQuasicoherent] (J : InjectiveResolution L)
local instance : IsClosedImmersion (Spec.map (localizedQuotientSpecMap I t)) :=
  Scheme.isClosedImmersion_specMap_localizationAway (quotientSpecMap I) t
local instance : (moduleSpecΓFunctor (R := quotientAwaySpecRing I t)).Additive :=
  moduleSpecΓFunctor_additive (quotientAwaySpecRing I t)
local instance : ((restrictFunctor (Spec.map (ambientAwayUnit t))).obj L).IsQuasicoherent :=
  openRestricted_quasicoherent (ambientAwayUnit t) L
local instance : PreservesFiniteLimits (ModuleCat.extendScalars (ambientAwayUnit t).hom) :=
  ModuleCat.extendScalars_preservesFiniteLimits_of_flat _ (ambientAway_flat t)
local instance : PreservesFiniteColimits (ModuleCat.extendScalars (ambientAwayUnit t).hom) :=
  ModuleCat.extendScalars_preservesFiniteColimits_of_flat _ (ambientAway_flat t)
variable [HasExt.{w} (ModuleCat.{u} R)]
  [HasExt.{z} (ModuleCat.{u} (ambientAwayRing t))]

private theorem quotientLocalizationGeoHomology_ext (n : ℕ)
    (x : (closedΓResolutionComplex (quotientSpecMap I) J).homology (n : ℤ)) :
    affineClosedRightAdjointResolutionExtAddEquiv (localizedQuotientSpecMap I t)
        (affineOpenRestrictedInjectiveResolution (ambientAwayUnit t) J) n
        (quotientLocalizationGeoHomology I t J (n : ℤ) x) =
      ((Ext.mk₀ (scalarExtensionQuotientAwayIso I t).inv).comp
        ((affineClosedRightAdjointResolutionExtAddEquiv (quotientSpecMap I) J n x).mapExactFunctor
          (ModuleCat.extendScalars (ambientAwayUnit t).hom)) (Nat.zero_add n)).comp
        (Ext.mk₀ ((openSpecRestrictionMate (ambientAwayUnit t)).app L)) (Nat.add_zero n) := by
  let E := affineClosedRightAdjointResolutionExtAddEquiv (quotientSpecMap I) J n
  obtain ⟨f, hf, hfx⟩ := (AffineDerived.globalSectionsInjectiveResolution J).extMk_surjective
    (E x) (n + 1) rfl
  let m := (closedImmersionRightAdjointSectionsLinearEquiv (quotientSpecMap I)
    (J.cocomplex.X n)).symm f.hom
  have hfm : quotientGlobalHomMap I (J.cocomplex.X n) m = f := by
    apply ModuleCat.hom_ext
    exact (closedImmersionRightAdjointSectionsLinearEquiv (quotientSpecMap I)
      (J.cocomplex.X n)).apply_symm_apply f.hom
  have hf' : quotientGlobalHomMap I (J.cocomplex.X n) m ≫
      (AffineDerived.globalSectionsInjectiveResolution J).cocomplex.d n (n + 1) = 0 := by
    rw [hfm]
    exact hf
  let ζ := closedΓResolutionCycle (quotientSpecMap I) J n
    (quotientGlobalHomMap I (J.cocomplex.X n) m) hf'
  have hx : (closedΓResolutionComplex (quotientSpecMap I) J).homologyπ (n : ℤ) ζ = x := by
    apply E.injective
    change affineClosedRightAdjointResolutionExtAddEquiv (quotientSpecMap I) J n
      ((closedΓResolutionComplex (quotientSpecMap I) J).homologyπ (n : ℤ) ζ) = E x
    rw [closedΓResolutionCycle_class]
    calc
      _ = (AffineDerived.globalSectionsInjectiveResolution J).extMk f (n + 1) rfl hf := by
        congr 1
      _ = E x := hfx
  rw [← hx, quotientLocalizationGeoHomology_π, quotientLocalizationGeoCycles_class,
    closedΓResolutionCycle_class, closedΓResolutionCycle_class]
  exact (quotientLocalization_extMk_square I t J n m hf').symm
end GeometricHomologyExt
end AlgebraicGeometry.Scheme.Modules
public section
namespace AlgebraicGeometry.Scheme.Modules
section LocalizationPublic
variable {R : CommRingCat.{u}}

/-- The native quotient scalar extension, retaining the original localized quotient action. -/
def closedImmersionQuotientLocalizationSourceIso (I : Ideal R) (t : R) :
    (ModuleCat.extendScalars (algebraMap R (Localization.Away t))).obj (ModuleCat.of R (R ⧸ I)) ≅
      (ModuleCat.restrictScalars
        (IsLocalization.Away.map (Localization.Away t)
          (Localization.Away (Ideal.Quotient.mk I t)) (Ideal.Quotient.mk I) t)).obj
        (ModuleCat.of (Localization.Away (Ideal.Quotient.mk I t))
          (Localization.Away (Ideal.Quotient.mk I t))) :=
  scalarExtensionQuotientAwayIso I t
variable (I : Ideal R) (t : R) {L : (Spec R).Modules}
local instance : (moduleSpecΓFunctor (R := CommRingCat.of (R ⧸ I))).Additive :=
  moduleSpecΓFunctor_additive _
local instance : IsClosedImmersion (Spec.map (CommRingCat.ofHom
    (IsLocalization.Away.map (Localization.Away t)
      (Localization.Away (Ideal.Quotient.mk I t)) (Ideal.Quotient.mk I) t))) :=
  Scheme.isClosedImmersion_specMap_localizationAway (CommRingCat.ofHom (Ideal.Quotient.mk I)) t
local instance : (moduleSpecΓFunctor
    (R := CommRingCat.of (Localization.Away (Ideal.Quotient.mk I t)))).Additive :=
  moduleSpecΓFunctor_additive _

/-- The actual geometric principal restriction on the supplied original resolution. -/
def closedImmersionQuotientLocalizationResolutionMap (J : InjectiveResolution L) :
    let S : CommRingCat := .of (R ⧸ I)
    let A : CommRingCat := .of (Localization.Away t)
    let T : CommRingCat := .of (Localization.Away (Ideal.Quotient.mk I t))
    let q : R ⟶ S := CommRingCat.ofHom (Ideal.Quotient.mk I)
    let σ : R ⟶ A := CommRingCat.ofHom (algebraMap R (Localization.Away t))
    let ψ : S ⟶ T := CommRingCat.ofHom (algebraMap (R ⧸ I) T)
    let q' : A ⟶ T := CommRingCat.ofHom (IsLocalization.Away.map A T (Ideal.Quotient.mk I) t)
    ((moduleSpecΓFunctor (R := S)).mapHomologicalComplex (.up ℤ)).obj
        (((closedImmersionRightAdjoint (Spec.map q)).mapHomologicalComplex (.up ℤ)).obj
          J.cochainComplex) ⟶
      ((ModuleCat.restrictScalars ψ.hom).mapHomologicalComplex (.up ℤ)).obj
        (((moduleSpecΓFunctor (R := T)).mapHomologicalComplex (.up ℤ)).obj
          (((closedImmersionRightAdjoint (Spec.map q')).mapHomologicalComplex (.up ℤ)).obj
            (affineOpenRestrictedInjectiveResolution σ J).cochainComplex)) :=
  quotientLocalizationGeoComplex I t J

/-- Original cochain homology followed by the native scalar-restriction homology comparison. -/
def closedImmersionQuotientLocalizationHomologyMap (J : InjectiveResolution L) (n : ℤ) :
    let S : CommRingCat := .of (R ⧸ I)
    let A : CommRingCat := .of (Localization.Away t)
    let T : CommRingCat := .of (Localization.Away (Ideal.Quotient.mk I t))
    let q : R ⟶ S := CommRingCat.ofHom (Ideal.Quotient.mk I)
    let σ : R ⟶ A := CommRingCat.ofHom (algebraMap R (Localization.Away t))
    let ψ : S ⟶ T := CommRingCat.ofHom (algebraMap (R ⧸ I) T)
    let q' : A ⟶ T := CommRingCat.ofHom (IsLocalization.Away.map A T (Ideal.Quotient.mk I) t)
    (((moduleSpecΓFunctor (R := S)).mapHomologicalComplex (.up ℤ)).obj
        (((closedImmersionRightAdjoint (Spec.map q)).mapHomologicalComplex (.up ℤ)).obj
          J.cochainComplex)).homology n ⟶
      (ModuleCat.restrictScalars ψ.hom).obj
        ((((moduleSpecΓFunctor (R := T)).mapHomologicalComplex (.up ℤ)).obj
          (((closedImmersionRightAdjoint (Spec.map q')).mapHomologicalComplex (.up ℤ)).obj
            (affineOpenRestrictedInjectiveResolution σ J).cochainComplex)).homology n) :=
  quotientLocalizationGeoHomology I t J n
end LocalizationPublic
end AlgebraicGeometry.Scheme.Modules
namespace AlgebraicGeometry.Scheme.Modules
section LocalizationReductions
variable {R : CommRingCat.{u}} (I : Ideal R) (t : R) {L : (Spec R).Modules}
local instance : (moduleSpecΓFunctor (R := CommRingCat.of (R ⧸ I))).Additive :=
  moduleSpecΓFunctor_additive _
local instance : IsClosedImmersion (Spec.map (CommRingCat.ofHom
    (IsLocalization.Away.map (Localization.Away t)
      (Localization.Away (Ideal.Quotient.mk I t)) (Ideal.Quotient.mk I) t))) :=
  Scheme.isClosedImmersion_specMap_localizationAway (CommRingCat.ofHom (Ideal.Quotient.mk I)) t
local instance : (moduleSpecΓFunctor
    (R := CommRingCat.of (Localization.Away (Ideal.Quotient.mk I t)))).Additive :=
  moduleSpecΓFunctor_additive _
private theorem quotientLocalizationResolutionMap_f_aux
    (J : InjectiveResolution L) (n : ℤ) :
    let S : CommRingCat := .of (R ⧸ I)
    let A : CommRingCat := .of (Localization.Away t)
    let T : CommRingCat := .of (Localization.Away (Ideal.Quotient.mk I t))
    let q : R ⟶ S := CommRingCat.ofHom (Ideal.Quotient.mk I)
    let σ : R ⟶ A := CommRingCat.ofHom (algebraMap R (Localization.Away t))
    let ψ : S ⟶ T := CommRingCat.ofHom (algebraMap (R ⧸ I) T)
    let q' : A ⟶ T := CommRingCat.ofHom (IsLocalization.Away.map A T (Ideal.Quotient.mk I) t)
    let h := (Scheme.isPullback_specMap_localizationAway q t).flip
    (closedImmersionQuotientLocalizationResolutionMap I t J).f n =
      (affineOpenRestrictionSectionsMap ψ
          ((closedImmersionRightAdjoint (Spec.map q)).obj (J.cochainComplex.X n)) ≫
        (ModuleCat.restrictScalars ψ.hom).map
          ((moduleSpecΓFunctor (R := T)).map
            ((closedImmersionRightAdjointOpenIso (Spec.map ψ) (Spec.map q')
              (Spec.map q) (Spec.map σ) h).hom.app (J.cochainComplex.X n)))) ≫
        (ModuleCat.restrictScalars ψ.hom).map
          ((moduleSpecΓFunctor (R := T)).map
            ((closedImmersionRightAdjoint (Spec.map q')).map
              ((J.cocomplex.mapExtendIso (restrictFunctor (Spec.map σ))
                ComplexShape.embeddingUpNat).hom.f n))) := rfl

private theorem quotientLocalizationHomologyMap_eq_aux (J : InjectiveResolution L) (n : ℤ) :
    let S : CommRingCat := .of (R ⧸ I)
    let A : CommRingCat := .of (Localization.Away t)
    let T : CommRingCat := .of (Localization.Away (Ideal.Quotient.mk I t))
    let σ : R ⟶ A := CommRingCat.ofHom (algebraMap R (Localization.Away t))
    let ψ : S ⟶ T := CommRingCat.ofHom (algebraMap (R ⧸ I) T)
    let q' : A ⟶ T := CommRingCat.ofHom (IsLocalization.Away.map A T (Ideal.Quotient.mk I) t)
    let C := ((moduleSpecΓFunctor (R := T)).mapHomologicalComplex (.up ℤ)).obj
      (((closedImmersionRightAdjoint (Spec.map q')).mapHomologicalComplex (.up ℤ)).obj
        (affineOpenRestrictedInjectiveResolution σ J).cochainComplex)
    closedImmersionQuotientLocalizationHomologyMap I t J n =
      homologyMap (closedImmersionQuotientLocalizationResolutionMap I t J) n ≫
        ((C.sc n).mapHomologyIso (ModuleCat.restrictScalars ψ.hom)).hom := rfl
local instance : PreservesFiniteLimits
    (ModuleCat.extendScalars (algebraMap R (Localization.Away t))) :=
  ModuleCat.extendScalars_preservesFiniteLimits_of_flat _ (ambientAway_flat t)
local instance : PreservesFiniteColimits
    (ModuleCat.extendScalars (algebraMap R (Localization.Away t))) :=
  ModuleCat.extendScalars_preservesFiniteColimits_of_flat _ (ambientAway_flat t)
variable [L.IsQuasicoherent] [HasExt.{w} (ModuleCat.{u} R)]
  [HasExt.{z} (ModuleCat.{u} (Localization.Away t))]
private theorem quotientLocalizationHomologyMap_ext_aux
    (J : InjectiveResolution L) (n : ℕ)
    (x : ((((moduleSpecΓFunctor (R := CommRingCat.of (R ⧸ I))).mapHomologicalComplex (.up ℤ)).obj
      (((closedImmersionRightAdjoint (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk
        I)))).mapHomologicalComplex (.up ℤ)).obj J.cochainComplex)).homology (n : ℤ))) :
    affineClosedRightAdjointResolutionExtAddEquiv
        (CommRingCat.ofHom (IsLocalization.Away.map (Localization.Away t)
          (Localization.Away (Ideal.Quotient.mk I t)) (Ideal.Quotient.mk I) t))
        (affineOpenRestrictedInjectiveResolution
          (CommRingCat.ofHom (algebraMap R (Localization.Away t))) J) n
        (closedImmersionQuotientLocalizationHomologyMap I t J (n : ℤ) x) =
      ((Ext.mk₀ (closedImmersionQuotientLocalizationSourceIso I t).inv).comp
        ((affineClosedRightAdjointResolutionExtAddEquiv
          (CommRingCat.ofHom (Ideal.Quotient.mk I)) J n x).mapExactFunctor
            (ModuleCat.extendScalars (algebraMap R (Localization.Away t)))) (Nat.zero_add n)).comp
        (Ext.mk₀ (affineRestrictGlobalSectionsIso
          (CommRingCat.ofHom (algebraMap R (Localization.Away t))) L).hom) (Nat.add_zero n) := by
  simpa only [closedImmersionQuotientLocalizationHomologyMap,
    closedImmersionQuotientLocalizationSourceIso, quotientSpecRing, ambientAwayRing,
    quotientAwaySpecRing, quotientSpecMap, ambientAwayUnit, quotientAwayUnit,
    localizedQuotientSpecMap, quotientAwayMap, CommRingCat.hom_ofHom,
    openSpecRestrictionMate_eq_affineRestrictGlobalSectionsIso] using
    quotientLocalizationGeoHomology_ext I t J n x
end LocalizationReductions
end AlgebraicGeometry.Scheme.Modules
@[expose] public section
namespace AlgebraicGeometry.Scheme.Modules
section LocalizationPublicLaws
variable {R : CommRingCat.{u}}

/-- A pure quotient tensor retains its original localized representative. -/
theorem closedImmersionQuotientLocalizationSourceIso_one_tmul (I : Ideal R) (t r : R) :
    (closedImmersionQuotientLocalizationSourceIso I t).hom
      ((1 : Localization.Away t) ⊗ₜ[R,algebraMap R (Localization.Away t)] Ideal.Quotient.mk I r) =
      algebraMap (R ⧸ I) (Localization.Away (Ideal.Quotient.mk I t)) (Ideal.Quotient.mk I r) :=
  scalarExtensionQuotientAwayIso_one_tmul I t r
variable (I : Ideal R) (t : R) {L : (Spec R).Modules}
local instance : (moduleSpecΓFunctor (R := CommRingCat.of (R ⧸ I))).Additive :=
  moduleSpecΓFunctor_additive _
local instance : IsClosedImmersion (Spec.map (CommRingCat.ofHom
    (IsLocalization.Away.map (Localization.Away t)
      (Localization.Away (Ideal.Quotient.mk I t)) (Ideal.Quotient.mk I) t))) :=
  Scheme.isClosedImmersion_specMap_localizationAway (CommRingCat.ofHom (Ideal.Quotient.mk I)) t
local instance : (moduleSpecΓFunctor
    (R := CommRingCat.of (Localization.Away (Ideal.Quotient.mk I t)))).Additive :=
  moduleSpecΓFunctor_additive _

/-- The original homology map has exactly the native cochain/scalar comparison factors. -/
theorem closedImmersionQuotientLocalizationHomologyMap_eq (J : InjectiveResolution L) (n : ℤ) :
    let S : CommRingCat := .of (R ⧸ I)
    let A : CommRingCat := .of (Localization.Away t)
    let T : CommRingCat := .of (Localization.Away (Ideal.Quotient.mk I t))
    let σ : R ⟶ A := CommRingCat.ofHom (algebraMap R (Localization.Away t))
    let ψ : S ⟶ T := CommRingCat.ofHom (algebraMap (R ⧸ I) T)
    let q' : A ⟶ T := CommRingCat.ofHom (IsLocalization.Away.map A T (Ideal.Quotient.mk I) t)
    let C := ((moduleSpecΓFunctor (R := T)).mapHomologicalComplex (.up ℤ)).obj
      (((closedImmersionRightAdjoint (Spec.map q')).mapHomologicalComplex (.up ℤ)).obj
        (affineOpenRestrictedInjectiveResolution σ J).cochainComplex)
    closedImmersionQuotientLocalizationHomologyMap I t J n =
      homologyMap (closedImmersionQuotientLocalizationResolutionMap I t J) n ≫
        ((C.sc n).mapHomologyIso (ModuleCat.restrictScalars ψ.hom)).hom := by
  exact quotientLocalizationHomologyMap_eq_aux I t J n

/-- Every component retains the original open unit, closed-adjoint comparison and extension map. -/
theorem closedImmersionQuotientLocalizationResolutionMap_f
    (J : InjectiveResolution L) (n : ℤ) :
    let S : CommRingCat := .of (R ⧸ I)
    let A : CommRingCat := .of (Localization.Away t)
    let T : CommRingCat := .of (Localization.Away (Ideal.Quotient.mk I t))
    let q : R ⟶ S := CommRingCat.ofHom (Ideal.Quotient.mk I)
    let σ : R ⟶ A := CommRingCat.ofHom (algebraMap R (Localization.Away t))
    let ψ : S ⟶ T := CommRingCat.ofHom (algebraMap (R ⧸ I) T)
    let q' : A ⟶ T := CommRingCat.ofHom (IsLocalization.Away.map A T (Ideal.Quotient.mk I) t)
    let h := (Scheme.isPullback_specMap_localizationAway q t).flip
    (closedImmersionQuotientLocalizationResolutionMap I t J).f n =
      (affineOpenRestrictionSectionsMap ψ
          ((closedImmersionRightAdjoint (Spec.map q)).obj (J.cochainComplex.X n)) ≫
        (ModuleCat.restrictScalars ψ.hom).map
          ((moduleSpecΓFunctor (R := T)).map
            ((closedImmersionRightAdjointOpenIso (Spec.map ψ) (Spec.map q')
              (Spec.map q) (Spec.map σ) h).hom.app (J.cochainComplex.X n)))) ≫
        (ModuleCat.restrictScalars ψ.hom).map
          ((moduleSpecΓFunctor (R := T)).map
            ((closedImmersionRightAdjoint (Spec.map q')).map
              ((J.cocomplex.mapExtendIso (restrictFunctor (Spec.map σ))
                ComplexShape.embeddingUpNat).hom.f n))) := by
  exact quotientLocalizationResolutionMap_f_aux I t J n
local instance : PreservesFiniteLimits
    (ModuleCat.extendScalars (algebraMap R (Localization.Away t))) :=
  ModuleCat.extendScalars_preservesFiniteLimits_of_flat _ (ambientAway_flat t)
local instance : PreservesFiniteColimits
    (ModuleCat.extendScalars (algebraMap R (Localization.Away t))) :=
  ModuleCat.extendScalars_preservesFiniteColimits_of_flat _ (ambientAway_flat t)
variable [L.IsQuasicoherent] [HasExt.{w} (ModuleCat.{u} R)]
  [HasExt.{z} (ModuleCat.{u} (Localization.Away t))]

/-- Original geometric restriction equals the original exact-functor Ext map and its unit maps. -/
theorem closedImmersionQuotientLocalizationHomologyMap_ext
    (J : InjectiveResolution L) (n : ℕ)
    (x : ((((moduleSpecΓFunctor (R := CommRingCat.of (R ⧸ I))).mapHomologicalComplex (.up ℤ)).obj
      (((closedImmersionRightAdjoint (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk
        I)))).mapHomologicalComplex (.up ℤ)).obj J.cochainComplex)).homology (n : ℤ))) :
    affineClosedRightAdjointResolutionExtAddEquiv
        (CommRingCat.ofHom (IsLocalization.Away.map (Localization.Away t)
          (Localization.Away (Ideal.Quotient.mk I t)) (Ideal.Quotient.mk I) t))
        (affineOpenRestrictedInjectiveResolution
          (CommRingCat.ofHom (algebraMap R (Localization.Away t))) J) n
        (closedImmersionQuotientLocalizationHomologyMap I t J (n : ℤ) x) =
      ((Ext.mk₀ (closedImmersionQuotientLocalizationSourceIso I t).inv).comp
        ((affineClosedRightAdjointResolutionExtAddEquiv
          (CommRingCat.ofHom (Ideal.Quotient.mk I)) J n x).mapExactFunctor
            (ModuleCat.extendScalars (algebraMap R (Localization.Away t)))) (Nat.zero_add n)).comp
        (Ext.mk₀ (affineRestrictGlobalSectionsIso
          (CommRingCat.ofHom (algebraMap R (Localization.Away t))) L).hom) (Nat.add_zero n) := by
  exact quotientLocalizationHomologyMap_ext_aux I t J n x
end LocalizationPublicLaws
end AlgebraicGeometry.Scheme.Modules
