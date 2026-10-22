/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Cohomology.GrothendieckExistence.OpenIdealPullback
public import Aglib.AlgebraicGeometry.Modules.Coherent.AdicSystem.Completion
public import Aglib.AlgebraicGeometry.Modules.QuasiCoherent.Limits

/-! # Native open restriction of arbitrary-ideal formal systems

The underlying diagram and every morphism are the actual ordinary pullbacks.
The reduction law uses the original geometric units, including stage zero.
-/

@[expose] public noncomputable section

open CategoryTheory Opposite
namespace AlgebraicGeometry.Scheme.Modules.Coherent

universe u
variable {X Y : Scheme.{u}}
  [IsLocallyNoetherian X] [IsLocallyNoetherian Y]
  (p : Y ⟶ X) [IsOpenImmersion p] (K : X.IdealSheafData)

omit [IsLocallyNoetherian Y] in
/-- The ordinary stagewise pullback satisfies the native formal conditions. -/
theorem openIdealPullback_isAdicSystem
    (F : AdicSystem X K) :
    IsAdicSystem Y (K.comap p) (F.obj ⋙ pullback p) where
  coherent n := QuasiCoherent.affineLocallyFiniteType_pullback p (F.property.coherent n)
  annihilated n := by
    let : (F.obj.obj (op n)).IsQuasicoherent :=
      QuasiCoherent.quasicoherent_of_affineCharts _
        (fun R j _ => (F.property.coherent n R j).1)
    exact killedByOpenIdeal_pullback p K _ n (F.property.annihilated n)
  reduction n := by
    let M := F.obj.obj (op (n + 1))
    let : M.IsQuasicoherent :=
      QuasiCoherent.quasicoherent_of_affineCharts _
        (fun R j _ => (F.property.coherent (n + 1) R j).1)
    let e := openIdealPullbackQuotientIso p K M n
    refine ⟨e.symm ≪≫ (pullback p).mapIso (F.reductionIso n), ?_⟩
    change (idealSheafQuotientUnit Y (K.comap p ^ n)).app
      ((pullback p).obj M) ≫ e.inv ≫ (pullback p).map (F.reductionIso n).hom = _
    rw [← openIdealPullbackQuotientIso_unit p K M n]
    dsimp only [e]
    simp only [Category.assoc, Iso.hom_inv_id_assoc]
    rw [← Functor.map_comp, F.unit_reductionIso_hom]
    rfl

/-- Formal pullback keeps the original coefficient diagram. -/
def openIdealPullbackFunctor :
    AdicSystem X K ⥤
      AdicSystem Y (K.comap p) where
  obj F := ⟨F.obj ⋙ pullback p, openIdealPullback_isAdicSystem p K F⟩
  map g := ObjectProperty.homMk (Functor.whiskerRight g.hom (pullback p))
  map_id F := by
    apply ObjectProperty.hom_ext
    apply NatTrans.ext
    funext n
    exact (pullback p).map_id _
  map_comp g h := by
    apply ObjectProperty.hom_ext
    apply NatTrans.ext
    funext n
    exact (pullback p).map_comp _ _

@[simp]
theorem openIdealPullbackFunctor_map_app
    {F G : AdicSystem X K} (g : F ⟶ G) (n : ℕ) :
    ((openIdealPullbackFunctor p K).map g).hom.app (op n) =
      (pullback p).map (g.hom.app (op n)) := rfl

end AlgebraicGeometry.Scheme.Modules.Coherent
