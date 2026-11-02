/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.QuasiCoherent.EtalePullback
public import Aglib.AlgebraicGeometry.EtaleCohomology.QuasiCoherent.BaseRestrictionValues
public import Aglib.AlgebraicGeometry.EtaleCohomology.QuasiCoherent.CoefficientMaps
public import Aglib.AlgebraicGeometry.EtaleCohomology.Stalk.EtaleRestrictionCoherence
public import Aglib.AlgebraicGeometry.Modules.Pullback.Triangle
public import Aglib.AlgebraicGeometry.EtaleCohomology.Continuity.PullbackCohomologySystem

/-! # Composition of the original module coefficient pullback

Literal étale restriction reduces composition to native module pullback
associativity on each test scheme. The original inverse-image comparison then
transports the entire square; neither coefficient maps nor compositors are
reselected.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory Opposite
open AlgebraicGeometry.Scheme.Modules

universe u

namespace AlgebraicGeometry.Scheme.EtaleCohomology.QuasiCoherent

attribute [local instance] hasSheafifyLarge

/-- An identity over-map retains the original equality transport on modules. -/
theorem additiveSectionsPresheaf_map_identity_down
    {X W : Scheme.{u}} (M : X.Modules) [M.IsQuasicoherent]
    (a b : W ⟶ X) (h : a = b)
    (s : ULift.{u + 1} Γ((pullback b).obj M, ⊤)) :
    ((additiveSectionsPresheaf X M).map
      (Over.homMk (𝟙 W) (by simpa using h.symm) : Over.mk a ⟶ Over.mk b).op s).down =
    Scheme.Modules.Hom.app ((pullbackCongr h.symm).hom.app M) ⊤ s.down := by
  subst b
  change ((additiveSectionsPresheaf X M).map (𝟙 (op (Over.mk a))) s).down = _
  have hi := (additiveSectionsPresheaf X M).map_id (op (Over.mk a))
  exact congrArg (fun k : (additiveSectionsPresheaf X M).obj (op (Over.mk a)) ⟶
    (additiveSectionsPresheaf X M).obj (op (Over.mk a)) => (k s).down) hi

/-- The original module compositor equation in the inverse orientation used by
literal restriction of section coefficients. -/
theorem modulePullbackComp_sections_square
    {X S T W : Scheme.{u}} (f : S ⟶ X) (g : T ⟶ S) (a : W ⟶ T) (M : X.Modules) :
    (pullbackCongr (Category.assoc a g f)).inv.app M ≫
      (pullbackComp (a ≫ g) f).inv.app M ≫
      (pullbackComp a g).inv.app ((pullback f).obj M) ≫
      (pullback a).map ((pullbackComp g f).hom.app M) =
    (pullbackComp a (g ≫ f)).inv.app M := by
  apply (cancel_mono ((pullbackComp a (g ≫ f)).hom.app M)).mp
  simp only [Category.assoc]
  rw [pullbackComp_assoc_hom]
  simp only [Iso.inv_hom_id_app_assoc, Iso.inv_hom_id_app]

variable {X S T : Scheme.{u}} (f : S ⟶ X) (g : T ⟶ S) [Etale f] [Etale g]
  (M : X.Modules) [M.IsQuasicoherent]

/-- The original restriction compositor is the presheaf map of its native
postcomposition isomorphism, before specializing the coefficient carrier. -/
theorem etaleRestrictionComp_hom_app (F : AbelianSheaf.{u, u + 1} X) (U : T.Etale) :
    ((etaleRestrictionComp f g).hom.app F).hom.app (op U) =
      F.obj.map ((siteEtalePostcomposeComp f g).inv.app U).op := rfl

/-- The original compositor transports sections by the native equality of
composite structural morphisms. -/
theorem etaleRestrictionComp_additive_down (U : T.Etale)
    (s : ((etaleRestriction (g ≫ f)).obj (additiveCoefficient X M)).obj.obj (op U)) :
    (((etaleRestrictionComp f g).hom.app (additiveCoefficient X M)).hom.app (op U) s).down =
      Scheme.Modules.Hom.app ((pullbackCongr (Category.assoc U.hom g f)).inv.app M)
        ⊤ s.down := by
  have he := etaleRestrictionComp_hom_app f g (additiveCoefficient X M) U
  have hs := congrArg (fun k => (k s).down) he
  refine hs.trans ?_
  exact additiveSectionsPresheaf_map_identity_down M
    ((U.hom ≫ g) ≫ f) (U.hom ≫ (g ≫ f)) (Category.assoc U.hom g f) s

/-- Literal chart restriction retains native module composition on every test. -/
theorem additiveCoefficientEtaleRestrictionIso_comp :
    (etaleRestrictionComp f g).hom.app (additiveCoefficient X M) ≫
      (etaleRestriction g).map (additiveCoefficientEtaleRestrictionIso f M).hom ≫
      (additiveCoefficientEtaleRestrictionIso g ((pullback f).obj M)).hom ≫
      additiveCoefficientMap T ((pullbackComp g f).hom.app M) =
    (additiveCoefficientEtaleRestrictionIso (g ≫ f) M).hom := by
  let : ((pullback f ⋙ pullback g).obj M).IsQuasicoherent :=
    show ((pullback g).obj ((pullback f).obj M)).IsQuasicoherent from inferInstance
  apply Sheaf.hom_ext
  apply NatTrans.ext
  funext U
  change ((etaleRestrictionComp f g).hom.app (additiveCoefficient X M)).hom.app U ≫
    (additiveBaseRestrictionIso f M).hom.app
      (op ((Over.map g).obj ((Scheme.Etale.forget T).obj U.unop))) ≫
    (additiveBaseRestrictionIso g ((pullback f).obj M)).hom.app
      (op ((Scheme.Etale.forget T).obj U.unop)) ≫
    (additiveCoefficientMap T ((pullbackComp g f).hom.app M)).hom.app U =
    (additiveBaseRestrictionIso (g ≫ f) M).hom.app
      (op ((Scheme.Etale.forget T).obj U.unop))
  apply AddCommGrpCat.hom_ext
  apply AddMonoidHom.ext
  intro s
  let s₀ : ULift.{u + 1} Γ((pullback (U.unop.hom ≫ (g ≫ f))).obj M, ⊤) := s
  let s₁ : ULift.{u + 1} Γ((pullback ((U.unop.hom ≫ g) ≫ f)).obj M, ⊤) :=
    ((etaleRestrictionComp f g).hom.app (additiveCoefficient X M)).hom.app U s₀
  let s₂ : ULift.{u + 1} Γ((pullback (U.unop.hom ≫ g)).obj ((pullback f).obj M), ⊤) :=
    (additiveBaseRestrictionIso f M).hom.app (op (Over.mk (U.unop.hom ≫ g))) s₁
  let s₃ : ULift.{u + 1}
      Γ((pullback U.unop.hom).obj ((pullback g).obj ((pullback f).obj M)), ⊤) :=
    (additiveBaseRestrictionIso g ((pullback f).obj M)).hom.app
      (op (Over.mk U.unop.hom)) s₂
  let s₄ : ULift.{u + 1} Γ((pullback U.unop.hom).obj ((pullback (g ≫ f)).obj M), ⊤) :=
    (additiveBaseRestrictionIso (g ≫ f) M).hom.app (op (Over.mk U.unop.hom)) s₀
  have h₁ : s₁.down = Scheme.Modules.Hom.app
      ((pullbackCongr (Category.assoc U.unop.hom g f)).inv.app M) ⊤ s₀.down :=
    etaleRestrictionComp_additive_down f g M U.unop s₀
  have h₂ : s₂.down = baseRestrictionSectionsAddEquiv f M
      (Over.mk (U.unop.hom ≫ g)) s₁.down :=
    additiveBaseRestrictionIso_hom_down f M (Over.mk (U.unop.hom ≫ g)) s₁
  have h₃ : s₃.down = baseRestrictionSectionsAddEquiv g ((pullback f).obj M)
      (Over.mk U.unop.hom) s₂.down :=
    additiveBaseRestrictionIso_hom_down g ((pullback f).obj M) (Over.mk U.unop.hom) s₂
  have h₄ : s₄.down = baseRestrictionSectionsAddEquiv (g ≫ f) M
      (Over.mk U.unop.hom) s₀.down :=
    additiveBaseRestrictionIso_hom_down (g ≫ f) M (Over.mk U.unop.hom) s₀
  apply ULift.ext
  let κ : (pullback g).obj ((pullback f).obj M) ⟶ (pullback (g ≫ f)).obj M :=
    (pullbackComp g f).hom.app M
  change Scheme.Modules.Hom.app ((pullback U.unop.hom).map κ) ⊤ s₃.down = s₄.down
  rw [h₃, h₂, h₁, h₄]
  simp only [baseRestrictionSectionsAddEquiv_apply]
  exact congrArg (fun k => Scheme.Modules.Hom.app k ⊤ s₀.down)
    (modulePullbackComp_sections_square f g U.unop.hom M)

/-- The original inverse-image coefficient maps compose with the original
inverse-image compositor and the native module compositor. -/
theorem additiveCoefficientPullback_comp :
    (inverseImage g).map (additiveCoefficientPullback f M) ≫
      additiveCoefficientPullback g ((pullback f).obj M) ≫
      additiveCoefficientMap T ((pullbackComp g f).hom.app M) =
    (inverseImageComp f g).inv.app (additiveCoefficient X M) ≫
      additiveCoefficientPullback (g ≫ f) M := by
  apply (cancel_epi ((inverseImageComp f g).hom.app (additiveCoefficient X M))).mp
  rw [Iso.hom_inv_id_app_assoc]
  rw [additiveCoefficientPullback_eq_etaleRestriction,
    additiveCoefficientPullback_eq_etaleRestriction,
    additiveCoefficientPullback_eq_etaleRestriction, Functor.map_comp]
  simp only [Category.assoc]
  rw [(inverseImageEtaleIso g).hom.naturality_assoc
    (additiveCoefficientEtaleRestrictionIso f M).hom]
  rw [reassoc_of% (inverseImageEtaleIso_comp f g (additiveCoefficient X M))]
  rw [additiveCoefficientEtaleRestrictionIso_comp]

/-- The actual coefficient square for a commuting triangle of étale charts. -/
theorem additiveCoefficientPullback_triangle (a : T ⟶ X) (h : g ≫ f = a) :
    (inverseImage g).map (additiveCoefficientPullback f M) ≫
      additiveCoefficientPullback g ((pullback f).obj M) ≫
      additiveCoefficientMap T
        ((Scheme.Modules.pullbackTriangleIso g f a h).hom.app M) =
    (EtaleCohomology.pullbackTriangleIso a f g h).inv.app (additiveCoefficient X M) ≫
      additiveCoefficientPullback a M := by
  subst a
  simpa only [Scheme.Modules.pullbackTriangleIso, pullbackCongr, eqToIso_refl,
    Iso.trans_hom, NatTrans.comp_app, Iso.refl_hom, NatTrans.id_app,
    Category.comp_id, EtaleCohomology.pullbackTriangleIso, Iso.refl_trans]
    using additiveCoefficientPullback_comp f g M

end AlgebraicGeometry.Scheme.EtaleCohomology.QuasiCoherent
