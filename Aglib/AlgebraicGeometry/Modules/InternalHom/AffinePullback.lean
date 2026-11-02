/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Modules.InternalHom.AffineSections
public import Aglib.AlgebraicGeometry.Modules.QuasiCoherent.Affine.ScalarAdjunction.Counit

/-!
# Original affine Hom reconstruction under pullback

The original inverse affine Hom comparison is reconstructed after the original tilde
counit. A square of genuine scalar-adjoint coefficient maps then gives the whole
pullback square of the same inverse Hom maps. Only their sources are quasicoherent;
the target sheaves, ring map and presentation arrows are arbitrary.
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry

universe v₁ v₂ u₁ u₂ u

namespace AlgebraicGeometry.Scheme.Modules.InternalHom

/-- The original inverse counit Hom equivalence reconstructs its supplied map
through the same source and target counits. -/
theorem counitHomEquiv_symm_counit
    {C : Type u₁} {D : Type u₂} [Category.{v₁} C] [Category.{v₂} D]
    {L : C ⥤ D} {G : D ⥤ C} (adj : L ⊣ G) (M N : D)
    [IsIso (adj.counit.app M)] (q : G.obj M ⟶ G.obj N) :
    adj.counit.app M ≫ (counitHomEquiv adj M N).symm q =
      L.map q ≫ adj.counit.app N := by
  change adj.counit.app M ≫
    (inv (adj.counit.app M) ≫ (adj.homEquiv (G.obj M) N).symm q ≫ 𝟙 N) = _
  rw [Category.comp_id, ← Category.assoc, IsIso.hom_inv_id, Category.id_comp,
    Adjunction.homEquiv_counit]

/-- The same inverse affine Hom comparison retains the original tilde-counit
reconstruction. Its target need not be quasicoherent. -/
theorem affineGlobalHomEquiv_symm_counit (R : CommRingCat.{u})
    (M N : (Spec R).Modules) [M.IsQuasicoherent]
    (q : moduleSpecΓFunctor.obj M ⟶ moduleSpecΓFunctor.obj N) :
    M.fromTildeΓ ≫ (affineGlobalHomEquiv R M N).symm q.hom =
      (tilde.functor R).map q ≫ N.fromTildeΓ := by
  let : IsIso ((tilde.adjunction (R := R)).counit.app M) :=
    show IsIso M.fromTildeΓ from inferInstance
  change (tilde.adjunction (R := R)).counit.app M ≫
    (counitHomEquiv (tilde.adjunction (R := R)) M N).symm q = _
  exact counitHomEquiv_symm_counit (tilde.adjunction (R := R)) M N q

/-- A genuine scalar-adjoint coefficient square gives the original pullback
square of inverse affine Hom maps. Only the two sources are quasicoherent;
there is no flatness or invertibility assumption on either presentation arrow. -/
theorem affineGlobalHomEquiv_symm_pullback
    {R S : CommRingCat.{u}} (φ : R ⟶ S)
    (P Q : (Spec R).Modules) (P' Q' : (Spec S).Modules)
    [P.IsQuasicoherent] [P'.IsQuasicoherent]
    (u : (pullback (Spec.map φ)).obj P ⟶ P')
    (v : (pullback (Spec.map φ)).obj Q ⟶ Q')
    (q : moduleSpecΓFunctor.obj P ⟶ moduleSpecΓFunctor.obj Q)
    (q' : moduleSpecΓFunctor.obj P' ⟶ moduleSpecΓFunctor.obj Q')
    (h : q ≫
        (moduleSpecΓFunctor.map
          ((pullbackPushforwardAdjunction (Spec.map φ)).unit.app Q ≫
            (pushforward (Spec.map φ)).map v) ≫
          (pushforwardGlobalSectionsIso φ).hom.app Q') =
      (moduleSpecΓFunctor.map
          ((pullbackPushforwardAdjunction (Spec.map φ)).unit.app P ≫
            (pushforward (Spec.map φ)).map u) ≫
          (pushforwardGlobalSectionsIso φ).hom.app P') ≫
        (ModuleCat.restrictScalars φ.hom).map q') :
    (pullback (Spec.map φ)).map ((affineGlobalHomEquiv R P Q).symm q.hom) ≫ v =
      u ≫ (affineGlobalHomEquiv S P' Q').symm q'.hom := by
  let F := pullback (Spec.map φ)
  let A := ModuleCat.extendRestrictScalarsAdj φ.hom
  let T_u := moduleSpecΓFunctor.map
      ((pullbackPushforwardAdjunction (Spec.map φ)).unit.app P ≫
        (pushforward (Spec.map φ)).map u) ≫
    (pushforwardGlobalSectionsIso φ).hom.app P'
  let T_v := moduleSpecΓFunctor.map
      ((pullbackPushforwardAdjunction (Spec.map φ)).unit.app Q ≫
        (pushforward (Spec.map φ)).map v) ≫
    (pushforwardGlobalSectionsIso φ).hom.app Q'
  let D_u := (A.homEquiv (moduleSpecΓFunctor.obj P)
    (moduleSpecΓFunctor.obj P')).symm T_u
  let D_v := (A.homEquiv (moduleSpecΓFunctor.obj Q)
    (moduleSpecΓFunctor.obj Q')).symm T_v
  let t := (affineGlobalHomEquiv R P Q).symm q.hom
  let t' := (affineGlobalHomEquiv S P' Q').symm q'.hom
  let cP : (tilde.functor R).obj (moduleSpecΓFunctor.obj P) ⟶ P := P.fromTildeΓ
  let cQ : (tilde.functor R).obj (moduleSpecΓFunctor.obj Q) ⟶ Q := Q.fromTildeΓ
  let cP' : (tilde.functor S).obj (moduleSpecΓFunctor.obj P') ⟶ P' := P'.fromTildeΓ
  let cQ' : (tilde.functor S).obj (moduleSpecΓFunctor.obj Q') ⟶ Q' := Q'.fromTildeΓ
  let aP : (tilde.functor S).obj
      ((ModuleCat.extendScalars φ.hom).obj (moduleSpecΓFunctor.obj P)) ⟶
      F.obj ((tilde.functor R).obj (moduleSpecΓFunctor.obj P)) :=
    (tildePullbackIso φ).inv.app (moduleSpecΓFunctor.obj P)
  let aQ : (tilde.functor S).obj
      ((ModuleCat.extendScalars φ.hom).obj (moduleSpecΓFunctor.obj Q)) ⟶
      F.obj ((tilde.functor R).obj (moduleSpecΓFunctor.obj Q)) :=
    (tildePullbackIso φ).inv.app (moduleSpecΓFunctor.obj Q)
  let c := aP ≫ F.map cP
  change q ≫ T_v = T_u ≫ (ModuleCat.restrictScalars φ.hom).map q' at h
  have hD : (ModuleCat.extendScalars φ.hom).map q ≫ D_v = D_u ≫ q' :=
    A.homEquiv_naturality_right_square q T_v T_u q' h
  have hu : (tilde.functor S).map D_u ≫ cP' = aP ≫ F.map cP ≫ u :=
    tildePullbackIso_counit φ P P' u
  have hv : (tilde.functor S).map D_v ≫ cQ' = aQ ≫ F.map cQ ≫ v :=
    tildePullbackIso_counit φ Q Q' v
  have hP : cP ≫ t = (tilde.functor R).map q ≫ cQ :=
    affineGlobalHomEquiv_symm_counit R P Q q
  have hP' : cP' ≫ t' = (tilde.functor S).map q' ≫ cQ' :=
    affineGlobalHomEquiv_symm_counit S P' Q' q'
  have hn : (tilde.functor S).map ((ModuleCat.extendScalars φ.hom).map q) ≫ aQ =
      aP ≫ F.map ((tilde.functor R).map q) :=
    (tildePullbackIso φ).inv.naturality q
  let : IsIso cP := show IsIso P.fromTildeΓ from inferInstance
  let : IsIso aP :=
    show IsIso ((tildePullbackIso φ).inv.app (moduleSpecΓFunctor.obj P)) from inferInstance
  let : IsIso c := inferInstanceAs (IsIso (aP ≫ F.map cP))
  change F.map t ≫ v = u ≫ t'
  apply (cancel_epi c).mp
  calc
    c ≫ F.map t ≫ v = aP ≫ F.map (cP ≫ t) ≫ v := by
      simp only [c, Functor.map_comp, Category.assoc]
    _ = aP ≫ F.map ((tilde.functor R).map q) ≫ F.map cQ ≫ v := by
      rw [hP, Functor.map_comp, Category.assoc]
    _ = (tilde.functor S).map ((ModuleCat.extendScalars φ.hom).map q) ≫
          aQ ≫ F.map cQ ≫ v := by
      simpa only [Category.assoc] using
        congrArg (fun k => k ≫ F.map cQ ≫ v) hn.symm
    _ = (tilde.functor S).map ((ModuleCat.extendScalars φ.hom).map q) ≫
          (tilde.functor S).map D_v ≫ cQ' := by
      rw [← hv]
    _ = (tilde.functor S).map
          ((ModuleCat.extendScalars φ.hom).map q ≫ D_v) ≫ cQ' := by
      rw [Functor.map_comp, Category.assoc]
    _ = (tilde.functor S).map (D_u ≫ q') ≫ cQ' := by rw [hD]
    _ = (tilde.functor S).map D_u ≫ cP' ≫ t' := by
      rw [Functor.map_comp, Category.assoc, ← hP']
    _ = c ≫ u ≫ t' := by
      simpa only [c, Category.assoc] using
        congrArg (fun k => k ≫ t') hu

end AlgebraicGeometry.Scheme.Modules.InternalHom
