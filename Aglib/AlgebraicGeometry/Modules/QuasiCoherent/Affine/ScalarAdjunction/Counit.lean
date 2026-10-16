/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Modules.QuasiCoherent.Affine.ScalarAdjunction

/-!
# The original affine scalar adjunction and tilde counits

For arbitrary affine module sheaves P and Q, the scalar adjoint of the
sections of a geometric pullback adjoint agrees with the original tilde
counit square. Neither P nor Q is assumed quasicoherent, and the ring map
need not be flat. Applied to resolution terms, this identifies the actual
resolved base-change map with tilde of its scalar map followed by the same
original counit; it does not assume quasicoherence of injective terms.
-/

@[expose] public section

noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u

namespace AlgebraicGeometry.Scheme.Modules

variable {R S : CommRingCat.{u}} (φ : R ⟶ S)

/-- The original affine pullback comparison identifies the original
composed Hom adjoints, for every target sheaf. -/
theorem tildePullbackIso_homEquiv_inv (M : ModuleCat R) (Q : (Spec S).Modules)
    (k : (pullback (Spec.map φ)).obj ((tilde.functor R).obj M) ⟶ Q) :
    ((ModuleCat.extendRestrictScalarsAdj φ.hom).comp
      (tilde.adjunction (R := S))).homEquiv M Q ((tildePullbackIso φ).inv.app M ≫ k) =
    (tilde.adjunction (R := R)).unit.app M ≫
      moduleSpecΓFunctor.map
        ((pullbackPushforwardAdjunction (Spec.map φ)).homEquiv _ _ k) ≫
      (pushforwardGlobalSectionsIso φ).hom.app Q := by
  let adj₁ := ((tilde.adjunction (R := R)).comp
    (pullbackPushforwardAdjunction (Spec.map φ))).ofNatIsoRight (pushforwardGlobalSectionsIso φ)
  let adj₂ := (ModuleCat.extendRestrictScalarsAdj φ.hom).comp (tilde.adjunction (R := S))
  have hu := Adjunction.unit_leftAdjointUniq_hom_app adj₂ adj₁ M
  change adj₂.unit.app M ≫
    (moduleSpecΓFunctor (R := S) ⋙ ModuleCat.restrictScalars φ.hom).map
      ((tildePullbackIso φ).inv.app M) = adj₁.unit.app M at hu
  have hh : adj₂.homEquiv M Q ((tildePullbackIso φ).inv.app M ≫ k) =
      adj₁.homEquiv M Q k := by
    rw [Adjunction.homEquiv_unit, Functor.map_comp, ← Category.assoc, hu]
    rfl
  calc
    _ = adj₁.homEquiv M Q k := hh
    _ = _ := by
      dsimp only [adj₁]
      rw [Adjunction.homEquiv_ofNatIsoRight_apply, Adjunction.comp_homEquiv]
      change (tilde.adjunction (R := R)).homEquiv M ((pushforward (Spec.map φ)).obj Q)
        ((pullbackPushforwardAdjunction (Spec.map φ)).homEquiv _ _ k) ≫
          (pushforwardGlobalSectionsIso φ).hom.app Q = _
      rw [Adjunction.homEquiv_unit, Category.assoc]

/-- The scalar adjoint of the original geometric sections map retains the
original tilde counit square, without quasicoherence or flatness. -/
theorem tildePullbackIso_counit (P : (Spec R).Modules) (Q : (Spec S).Modules)
    (k : (pullback (Spec.map φ)).obj P ⟶ Q) :
    let D := ((ModuleCat.extendRestrictScalarsAdj φ.hom).homEquiv
      (moduleSpecΓFunctor.obj P) (moduleSpecΓFunctor.obj Q)).symm
        (moduleSpecΓFunctor.map
          ((pullbackPushforwardAdjunction (Spec.map φ)).unit.app P ≫
            (pushforward (Spec.map φ)).map k) ≫
          (pushforwardGlobalSectionsIso φ).hom.app Q)
    (tilde.functor S).map D ≫ Q.fromTildeΓ =
      (tildePullbackIso φ).inv.app (moduleSpecΓFunctor.obj P) ≫
        (pullback (Spec.map φ)).map P.fromTildeΓ ≫ k := by
  let adj := pullbackPushforwardAdjunction (Spec.map φ)
  let u := moduleSpecΓFunctor.map (adj.homEquiv P Q k) ≫
    (pushforwardGlobalSectionsIso φ).hom.app Q
  let D := ((ModuleCat.extendRestrictScalarsAdj φ.hom).homEquiv
    (moduleSpecΓFunctor.obj P) (moduleSpecΓFunctor.obj Q)).symm u
  change (tilde.functor S).map D ≫ Q.fromTildeΓ = _
  apply (((ModuleCat.extendRestrictScalarsAdj φ.hom).comp
    (tilde.adjunction (R := S))).homEquiv (moduleSpecΓFunctor.obj P) Q).injective
  have hleft : ((ModuleCat.extendRestrictScalarsAdj φ.hom).comp
      (tilde.adjunction (R := S))).homEquiv (moduleSpecΓFunctor.obj P) Q
        ((tilde.functor S).map D ≫ Q.fromTildeΓ) = u := by
    rw [Adjunction.comp_homEquiv]
    change ((ModuleCat.extendRestrictScalarsAdj φ.hom).homEquiv _ _)
      (((tilde.adjunction (R := S)).homEquiv _ _)
        (((tilde.adjunction (R := S)).homEquiv _ _).symm D)) = u
    rw [Equiv.apply_symm_apply]
    exact ((ModuleCat.extendRestrictScalarsAdj φ.hom).homEquiv _ _).apply_symm_apply u
  rw [hleft, tildePullbackIso_homEquiv_inv]
  let c : (tilde.functor R).obj (moduleSpecΓFunctor.obj P) ⟶ P := P.fromTildeΓ
  have hg : adj.homEquiv ((tilde.functor R).obj (moduleSpecΓFunctor.obj P)) Q
      ((pullback (Spec.map φ)).map c ≫ k) = c ≫ adj.homEquiv P Q k :=
    adj.homEquiv_naturality_left c k
  change u = (tilde.adjunction (R := R)).unit.app (moduleSpecΓFunctor.obj P) ≫
    moduleSpecΓFunctor.map (adj.homEquiv _ _ ((pullback (Spec.map φ)).map c ≫ k)) ≫
      (pushforwardGlobalSectionsIso φ).hom.app Q
  have ht := (tilde.adjunction (R := R)).right_triangle_components P
  change (tilde.adjunction (R := R)).unit.app (moduleSpecΓFunctor.obj P) ≫
    moduleSpecΓFunctor.map c = 𝟙 (moduleSpecΓFunctor.obj P) at ht
  rw [hg, Functor.map_comp]
  simp only [← Category.assoc, ht, u]
  exact (congrArg (fun q => q ≫ (pushforwardGlobalSectionsIso φ).hom.app Q)
    (Category.id_comp (moduleSpecΓFunctor.map ((adj.homEquiv P Q) k)))).symm

end AlgebraicGeometry.Scheme.Modules
