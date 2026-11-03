/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Modules.QuasiCoherent.Affine.PullbackSections
public import Aglib.AlgebraicGeometry.Cohomology.BaseChange.HigherDirectImage.Nonflat.AffineFunctor

/-!
# The native affine sheaf map attached to a small scalar mate

The associated-sheaf counit and the installed pullback comparison turn a map
on scalar-extended section modules into a sheaf map. Its naturality retains
the original coefficient arrows and associated-sheaf counits.
-/

@[expose] public section

noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

open CategoryTheory AlgebraicGeometry

namespace AlgebraicGeometry.Scheme.Modules.Nonflat

variable {R S : CommRingCat.{u}}

/-- The affine sheaf map with explicitly typed associated-sheaf comparisons. -/
def affineMapOfTilde (σ : R ⟶ S)
    {P : ModuleCat R} {Q : ModuleCat S} {E : (Spec R).Modules} {F : (Spec S).Modules}
    (e : (tilde.functor R).obj P ≅ E) (d : (tilde.functor S).obj Q ⟶ F)
    (t : (ModuleCat.extendScalars σ.hom).obj P ⟶ Q) :
    (pullback (Spec.map σ)).obj E ⟶ F :=
  affineFunctorMap (tilde.functor R) (tilde.functor S)
    (ModuleCat.extendScalars σ.hom) (pullback (Spec.map σ)) (tildePullbackIso σ).hom e d t

/-- Explicitly typed associated-sheaf comparisons retain coefficient naturality. -/
theorem affineMapOfTilde_naturality (σ : R ⟶ S)
    {P P' : ModuleCat R} {Q Q' : ModuleCat S}
    {E E' : (Spec R).Modules} {F F' : (Spec S).Modules}
    (e : (tilde.functor R).obj P ≅ E) (e' : (tilde.functor R).obj P' ≅ E')
    (d : (tilde.functor S).obj Q ⟶ F) (d' : (tilde.functor S).obj Q' ⟶ F')
    (r : P ⟶ P') (s : Q ⟶ Q') (μ : E ⟶ E') (ν : F ⟶ F')
    (he : (tilde.functor R).map r ≫ e'.hom = e.hom ≫ μ)
    (hd : (tilde.functor S).map s ≫ d' = d ≫ ν)
    (t : (ModuleCat.extendScalars σ.hom).obj P ⟶ Q)
    (t' : (ModuleCat.extendScalars σ.hom).obj P' ⟶ Q')
    (h : (ModuleCat.extendScalars σ.hom).map r ≫ t' = t ≫ s) :
    (pullback (Spec.map σ)).map μ ≫ affineMapOfTilde σ e' d' t' =
      affineMapOfTilde σ e d t ≫ ν := by
  let A := pullback (Spec.map σ)
  have hE : μ ≫ e'.inv = e.inv ≫ (tilde.functor R).map r := by
    apply (cancel_epi e.hom).mp
    rw [← Category.assoc, ← he]
    simp only [Category.assoc, Iso.hom_inv_id_assoc, Iso.hom_inv_id, Category.comp_id]
  have hp := congrArg A.map hE
  simp only [Functor.map_comp] at hp
  have ht := (tildePullbackIso σ).hom.naturality r
  have hm : (tilde.functor S).map ((ModuleCat.extendScalars σ.hom).map r) ≫
      (tilde.functor S).map t' =
        (tilde.functor S).map t ≫ (tilde.functor S).map s := by
    rw [← Functor.map_comp, h, Functor.map_comp]
  simp only [affineMapOfTilde, affineFunctorMap, Category.assoc]
  change A.map μ ≫ A.map e'.inv ≫ _ = _
  rw [reassoc_of% hp, reassoc_of% ht, reassoc_of% hm, hd]

/-- The actual associated-sheaf comparison used by the native affine pullback section iso. -/
def affinePullbackTildeIso (σ : R ⟶ S) (E : (Spec R).Modules) [E.IsQuasicoherent] :
    (tilde.functor S).obj ((ModuleCat.extendScalars σ.hom).obj (moduleSpecΓFunctor.obj E)) ≅
      (pullback (Spec.map σ)).obj E :=
  (tildePullbackIso σ).symm.app (moduleSpecΓFunctor.obj E) ≪≫
    (pullback (Spec.map σ)).mapIso (asIso E.fromTildeΓ)

/-- The native affine sheaf map attached to an actual map on scalar-extended sections. -/
def affineMapFromTensor (σ : R ⟶ S) (E : (Spec R).Modules) (F : (Spec S).Modules)
    [E.IsQuasicoherent]
    (t : (ModuleCat.extendScalars σ.hom).obj (moduleSpecΓFunctor.obj E) ⟶
      moduleSpecΓFunctor.obj F) : (pullback (Spec.map σ)).obj E ⟶ F :=
  (affinePullbackTildeIso σ E).inv ≫ (tilde.functor S).map t ≫ F.fromTildeΓ

/-- The shared native comparison expands to the original associated-sheaf factors. -/
theorem affineMapFromTensor_eq (σ : R ⟶ S)
    (E : (Spec R).Modules) (F : (Spec S).Modules) [E.IsQuasicoherent]
    (t : (ModuleCat.extendScalars σ.hom).obj (moduleSpecΓFunctor.obj E) ⟶
      moduleSpecΓFunctor.obj F) :
    affineMapFromTensor σ E F t =
      affineMapOfTilde σ (P := moduleSpecΓFunctor.obj E) (Q := moduleSpecΓFunctor.obj F)
        (asIso E.fromTildeΓ) F.fromTildeΓ t := by
  simp only [affineMapFromTensor, affinePullbackTildeIso, affineMapOfTilde, affineFunctorMap,
    Iso.trans_inv, Functor.mapIso_inv, Iso.symm_inv, Iso.app_inv, Category.assoc]

private theorem adjunctionIsoMate_sections
    {C D : Type*} [Category C] [Category D]
    {L : C ⥤ D} {G : D ⥤ C} (adj : L ⊣ G) {P : C} {Q F : D}
    (e : L.obj P ≅ Q) (t : P ⟶ G.obj F) :
    (adj.unit.app P ≫ G.map e.hom) ≫
        G.map (e.inv ≫ L.map t ≫ adj.counit.app F) = t := by
  rw [Category.assoc, ← G.map_comp]
  simp only [Iso.hom_inv_id_assoc]
  exact Equiv.apply_symm_apply (adj.homEquiv _ _) t

/-- On global sections the native affine sheaf construction is exactly the supplied small
scalar mate, through the same installed affine pullback comparison. -/
theorem affineMapFromTensor_sections
    (σ : R ⟶ S) (E : (Spec R).Modules) (F : (Spec S).Modules) [E.IsQuasicoherent]
    (t : (ModuleCat.extendScalars σ.hom).obj (moduleSpecΓFunctor.obj E) ⟶
      moduleSpecΓFunctor.obj F) :
    (affinePullbackGlobalSectionsIso σ E).hom ≫
      moduleSpecΓFunctor.map (affineMapFromTensor σ E F t) = t :=
  adjunctionIsoMate_sections (tilde.adjunction (R := S)) (affinePullbackTildeIso σ E) t

/-- An actual commutative square on scalar-extended sections yields the corresponding
square of native affine sheaf maps. -/
theorem affineMapFromTensor_naturality
    (σ : R ⟶ S) {E E' : (Spec R).Modules} {F F' : (Spec S).Modules}
    [E.IsQuasicoherent] [E'.IsQuasicoherent] (μ : E ⟶ E') (ν : F ⟶ F')
    (t : (ModuleCat.extendScalars σ.hom).obj (moduleSpecΓFunctor.obj E) ⟶
      moduleSpecΓFunctor.obj F)
    (t' : (ModuleCat.extendScalars σ.hom).obj (moduleSpecΓFunctor.obj E') ⟶
      moduleSpecΓFunctor.obj F')
    (h : (ModuleCat.extendScalars σ.hom).map (moduleSpecΓFunctor.map μ) ≫ t' =
      t ≫ moduleSpecΓFunctor.map ν) :
    (pullback (Spec.map σ)).map μ ≫ affineMapFromTensor σ E' F' t' =
      affineMapFromTensor σ E F t ≫ ν := by
  simp only [affineMapFromTensor_eq]
  exact affineMapOfTilde_naturality σ
    (P := moduleSpecΓFunctor.obj E) (P' := moduleSpecΓFunctor.obj E')
    (Q := moduleSpecΓFunctor.obj F) (Q' := moduleSpecΓFunctor.obj F')
    (asIso E.fromTildeΓ) (asIso E'.fromTildeΓ)
    F.fromTildeΓ F'.fromTildeΓ (moduleSpecΓFunctor.map μ) (moduleSpecΓFunctor.map ν) μ ν
    (fromTildeΓNatTrans.naturality μ) (fromTildeΓNatTrans.naturality ν) t t' h

end AlgebraicGeometry.Scheme.Modules.Nonflat
