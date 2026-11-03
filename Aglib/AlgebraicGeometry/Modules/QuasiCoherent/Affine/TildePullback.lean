/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Modules.QuasiCoherent.Affine.Pullback
public import Aglib.CategoryTheory.Adjunction.Mates

/-!
# The affine pullback comparison is compatible with composition

For a ring map `φ : R ⟶ S`, Aglib's `Scheme.Modules.tildePullbackIso φ` identifies the pullback
along `Spec.map φ` of the sheaf `M^~` with `(S ⊗_R M)^~`. It is defined by uniqueness of left
adjoints, so it is the conjugate (in the sense of Mathlib's `conjugateEquiv`) of the
global-sections comparison `pushforwardGlobalSectionsIso φ` of the right adjoints
(`conjugateEquiv_tildePullbackIso_hom`). Since Mathlib's `pullbackComp` and `extendScalarsComp`
are the conjugates of `pushforwardComp` and `restrictScalarsComp`, the compatibility of
`tildePullbackIso` with composition (`tildePullbackIso_comp_hom`, and its componentwise form
`tildePullbackIso_comp_hom_app`) reduces to an identity of right-adjoint transformations, which
holds on sections. This is the pseudonaturality of the tilde construction with respect to
Mathlib's `pullbackComp` and `extendScalarsComp`; it is the coherence needed to compare descent
data of quasi-coherent sheaves on affine schemes with descent data of modules.

Kernel note: proofs in this file avoid closing goals whose statement differs from the available
term only by the proof argument of `pullbackCongr` or by the presentation of objects of composite
functors; such kernel conversions exhausted memory in development. The componentwise lemmas
are obtained from the natural-transformation statement through `rfl` identifications and a
syntactic substitution of the proof argument.
-/

@[expose] public section

noncomputable section

universe u

open CategoryTheory Functor

namespace CategoryTheory.Adjunction

variable {C D : Type*} [Category C] [Category D] {F : C ⥤ D} {G H : D ⥤ C}

/-- The conjugate of the identity along `Adjunction.ofNatIsoRight` is the given isomorphism of
right adjoints. -/
lemma conjugateEquiv_ofNatIsoRight_id (adj : F ⊣ G) (e : G ≅ H) :
    conjugateEquiv adj (adj.ofNatIsoRight e) (𝟙 F) = e.hom := by
  ext X
  simp only [conjugateEquiv_apply_app, ofNatIsoRight_unit, NatTrans.comp_app, id_obj, comp_obj,
    whiskerLeft_app, NatTrans.id_app, Functor.map_id, Category.id_comp, Category.assoc]
  rw [← e.hom.naturality, adj.right_triangle_components_assoc]

end CategoryTheory.Adjunction

namespace AlgebraicGeometry.Scheme.Modules

variable {R S T : CommRingCat.{u}}

/-- `tildePullbackIso φ` is the conjugate of the global-sections comparison of the right
adjoints. -/
lemma conjugateEquiv_tildePullbackIso_hom (φ : R ⟶ S) :
    conjugateEquiv ((ModuleCat.extendRestrictScalarsAdj φ.hom).comp (tilde.adjunction (R := S)))
      ((tilde.adjunction (R := R)).comp (pullbackPushforwardAdjunction (Spec.map φ)))
      (tildePullbackIso φ).hom = (pushforwardGlobalSectionsIso φ).inv := by
  have h₁ : conjugateEquiv
      ((ModuleCat.extendRestrictScalarsAdj φ.hom).comp (tilde.adjunction (R := S)))
      (((tilde.adjunction (R := R)).comp
        (pullbackPushforwardAdjunction (Spec.map φ))).ofNatIsoRight
          (pushforwardGlobalSectionsIso φ))
      (tildePullbackIso φ).hom = 𝟙 _ := by
    simp [tildePullbackIso, Adjunction.leftAdjointUniq]
  have h₂ := conjugateEquiv_comp
    ((ModuleCat.extendRestrictScalarsAdj φ.hom).comp (tilde.adjunction (R := S)))
    ((tilde.adjunction (R := R)).comp (pullbackPushforwardAdjunction (Spec.map φ)))
    (((tilde.adjunction (R := R)).comp
        (pullbackPushforwardAdjunction (Spec.map φ))).ofNatIsoRight
          (pushforwardGlobalSectionsIso φ))
    (tildePullbackIso φ).hom (𝟙 _)
  rw [Category.id_comp, h₁, Adjunction.conjugateEquiv_ofNatIsoRight_id] at h₂
  exact (Iso.comp_hom_eq_id _).mp h₂

/-- The conjugate of `pullbackCongr` is `pushforwardCongr`. -/
lemma conjugateEquiv_pullbackCongr_hom {X Y : Scheme.{u}} {x y : X ⟶ Y} (h : x = y) :
    conjugateEquiv (pullbackPushforwardAdjunction y) (pullbackPushforwardAdjunction x)
      (pullbackCongr h).hom = (pushforwardCongr h).inv := by
  subst h
  ext M U : 3
  simp [pullbackCongr]

/-- **Compatibility of `tildePullbackIso` with composition**, as natural transformations. -/
theorem tildePullbackIso_comp_hom (a : R ⟶ S) (b : S ⟶ T) :
    whiskerLeft (tilde.functor R) ((pullbackCongr (Spec.map_comp a b)).hom ≫
        (pullbackComp (Spec.map b) (Spec.map a)).inv) ≫
      (associator _ _ _).inv ≫ whiskerRight (tildePullbackIso a).hom (pullback (Spec.map b)) ≫
      (associator _ _ _).hom ≫
        whiskerLeft (ModuleCat.extendScalars a.hom) (tildePullbackIso b).hom =
    (tildePullbackIso (a ≫ b)).hom ≫
      whiskerRight (ModuleCat.extendScalarsComp a.hom b.hom).hom (tilde.functor T) ≫
      (associator _ _ _).hom := by
  apply (conjugateEquiv
    ((ModuleCat.extendRestrictScalarsAdj a.hom).comp
      ((ModuleCat.extendRestrictScalarsAdj b.hom).comp (tilde.adjunction (R := T))))
    ((tilde.adjunction (R := R)).comp (pullbackPushforwardAdjunction (Spec.map (a ≫ b))))).injective
  rw [← conjugateEquiv_comp _
      ((tilde.adjunction (R := R)).comp ((pullbackPushforwardAdjunction (Spec.map a)).comp
        (pullbackPushforwardAdjunction (Spec.map b)))),
    ← conjugateEquiv_comp _
      (((tilde.adjunction (R := R)).comp (pullbackPushforwardAdjunction (Spec.map a))).comp
        (pullbackPushforwardAdjunction (Spec.map b))),
    ← conjugateEquiv_comp _
      (((ModuleCat.extendRestrictScalarsAdj a.hom).comp (tilde.adjunction (R := S))).comp
        (pullbackPushforwardAdjunction (Spec.map b))),
    ← conjugateEquiv_comp _
      ((ModuleCat.extendRestrictScalarsAdj a.hom).comp
        ((tilde.adjunction (R := S)).comp (pullbackPushforwardAdjunction (Spec.map b))))]
  rw [← conjugateEquiv_comp _
      ((ModuleCat.extendRestrictScalarsAdj (a ≫ b).hom).comp (tilde.adjunction (R := T))),
    ← conjugateEquiv_comp _
      (((ModuleCat.extendRestrictScalarsAdj a.hom).comp
        (ModuleCat.extendRestrictScalarsAdj b.hom)).comp (tilde.adjunction (R := T)))]
  rw [conjugateEquiv_whiskerLeft, conjugateEquiv_tildePullbackIso_hom,
    conjugateEquiv_associator_hom, conjugateEquiv_whiskerRight, conjugateEquiv_tildePullbackIso_hom,
    conjugateEquiv_associator_inv, conjugateEquiv_whiskerLeft, ← conjugateEquiv_comp _
      (pullbackPushforwardAdjunction (Spec.map b ≫ Spec.map a)), conjugateEquiv_pullbackComp_inv,
    conjugateEquiv_pullbackCongr_hom]
  rw [conjugateEquiv_associator_hom, conjugateEquiv_whiskerRight,
    conjugateEquiv_tildePullbackIso_hom,
    show conjugateEquiv ((ModuleCat.extendRestrictScalarsAdj a.hom).comp
        (ModuleCat.extendRestrictScalarsAdj b.hom)) (ModuleCat.extendRestrictScalarsAdj (a ≫ b).hom)
        (ModuleCat.extendScalarsComp a.hom b.hom).hom =
      (ModuleCat.restrictScalarsComp a.hom b.hom).inv from (conjugateEquiv _ _).apply_symm_apply _]
  ext M x
  simp only [NatTrans.comp_app, Functor.whiskerRight_app, Functor.whiskerLeft_app,
    Functor.associator_hom_app, Functor.associator_inv_app, Category.id_comp, Category.comp_id,
    Functor.map_comp, ModuleCat.hom_comp, LinearMap.comp_apply]
  change (ConcreteCategory.hom (Hom.app ((pushforwardCongr (Spec.map_comp a b)).inv.app M) ⊤))
    _ = _
  rw [pushforwardCongr_inv_app_app, eqToHom_op, eqToHom_map]
  rfl

/-- Componentwise form of `tildePullbackIso_comp_hom`, with the components of the associators
kept. The two sides are definitionally the components of the two sides of
`tildePullbackIso_comp_hom`; the proof states these identifications by `rfl`, which keeps the
kernel check small. -/
theorem tildePullbackIso_comp_hom_app_aux (a : R ⟶ S) (b : S ⟶ T) (N : ModuleCat.{u} R) :
    ((pullbackCongr (Spec.map_comp a b)).hom.app ((tilde.functor R).obj N) ≫
        (pullbackComp (Spec.map b) (Spec.map a)).inv.app ((tilde.functor R).obj N)) ≫ 𝟙 _ ≫
        (pullback (Spec.map b)).map ((tildePullbackIso a).hom.app N) ≫ 𝟙 _ ≫
        (tildePullbackIso b).hom.app ((ModuleCat.extendScalars a.hom).obj N) =
      (tildePullbackIso (a ≫ b)).hom.app N ≫
        (tilde.functor T).map ((ModuleCat.extendScalarsComp a.hom b.hom).hom.app N) ≫ 𝟙 _ := by
  have h₁ : ((pullbackCongr (Spec.map_comp a b)).hom.app ((tilde.functor R).obj N) ≫
        (pullbackComp (Spec.map b) (Spec.map a)).inv.app ((tilde.functor R).obj N)) ≫ 𝟙 _ ≫
        (pullback (Spec.map b)).map ((tildePullbackIso a).hom.app N) ≫ 𝟙 _ ≫
        (tildePullbackIso b).hom.app ((ModuleCat.extendScalars a.hom).obj N) =
      (whiskerLeft (tilde.functor R) ((pullbackCongr (Spec.map_comp a b)).hom ≫
        (pullbackComp (Spec.map b) (Spec.map a)).inv) ≫
      (associator _ _ _).inv ≫ whiskerRight (tildePullbackIso a).hom (pullback (Spec.map b)) ≫
      (associator _ _ _).hom ≫
        whiskerLeft (ModuleCat.extendScalars a.hom) (tildePullbackIso b).hom).app N := rfl
  have h₂ : (tildePullbackIso (a ≫ b)).hom.app N ≫
        (tilde.functor T).map ((ModuleCat.extendScalarsComp a.hom b.hom).hom.app N) ≫ 𝟙 _ =
      ((tildePullbackIso (a ≫ b)).hom ≫
        whiskerRight (ModuleCat.extendScalarsComp a.hom b.hom).hom (tilde.functor T) ≫
        (associator _ _ _).hom).app N := rfl
  rw [h₁, h₂]
  exact congr_app (tildePullbackIso_comp_hom a b) N

/-- **Compatibility of `tildePullbackIso` with composition**, at a module `N`, for an arbitrary
proof `h` of `Spec.map (a ≫ b) = Spec.map b ≫ Spec.map a`. -/
theorem tildePullbackIso_comp_hom_app (a : R ⟶ S) (b : S ⟶ T)
    (h : Spec.map (a ≫ b) = Spec.map b ≫ Spec.map a) (N : ModuleCat.{u} R) :
    (pullbackCongr h).hom.app ((tilde.functor R).obj N) ≫
        (pullbackComp (Spec.map b) (Spec.map a)).inv.app ((tilde.functor R).obj N) ≫
        (pullback (Spec.map b)).map ((tildePullbackIso a).hom.app N) ≫
        (tildePullbackIso b).hom.app ((ModuleCat.extendScalars a.hom).obj N) =
      (tildePullbackIso (a ≫ b)).hom.app N ≫
        (tilde.functor T).map ((ModuleCat.extendScalarsComp a.hom b.hom).hom.app N) := by
  -- Replace the proof `h` by `Spec.map_comp a b` syntactically: the kernel check of the
  -- final step then involves no comparison of the two proofs inside `pullbackCongr`.
  obtain rfl : h = Spec.map_comp a b := rfl
  have := tildePullbackIso_comp_hom_app_aux a b N
  rw [Category.id_comp, Category.id_comp, Category.comp_id, Category.assoc] at this
  exact this

end AlgebraicGeometry.Scheme.Modules
