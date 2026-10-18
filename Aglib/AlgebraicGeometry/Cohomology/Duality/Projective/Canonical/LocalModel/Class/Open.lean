/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Cohomology.Duality.Projective.Canonical.LocalModel.Class

/-!
# The original model class on an actual affine open

The original top model frame restricts to a unit frame. Its original
class-one section on the image of the total open therefore detects maps
from the actual restricted homology sheaf.
-/

@[expose] public section
noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory AlgebraicGeometry Opposite

universe u w
namespace AlgebraicGeometry.Scheme.Modules

/-- The same original class-one section detects actual arrows from restricted model homology. -/
theorem regularListModelTopClass_hom_ext_open
    {A D : CommRingCat.{u}} (s : List A) (hs : RingTheory.Sequence.IsWeaklyRegular A s)
    {L : (Spec A).Modules} [L.IsQuasicoherent] (J : InjectiveResolution L)
    (e : moduleSpecΓFunctor.obj L ≅ ModuleCat.of A A) [HasExt.{w} (ModuleCat.{u} A)]
    (j : Spec D ⟶ Spec (regularListQuotientRing s)) [IsOpenImmersion j]
    {N : (Spec D).Modules}
    {f g : ((closedImmersionRightAdjointRegularListResolutionComplex s J).homology
      (s.length : ℤ)).restrict j ⟶ N}
    (h : f.val.app (op ⊤)
        (regularListModelTopClass s hs J e (1 : A) (j ''ᵁ (⊤ : (Spec D).Opens))) =
      g.val.app (op ⊤)
        (regularListModelTopClass s hs J e (1 : A) (j ''ᵁ (⊤ : (Spec D).Opens)))) : f = g := by
  let U : (Spec D).Opens := ⊤
  let W := j ''ᵁ U
  let E := closedImmersionRightAdjointRegularListResolutionTopHomologyIso s hs J e
  let E' := (restrictFunctor j).mapIso E ≪≫ restrictUnitIso j
  let ξ := regularListModelTopClass s hs J e (1 : A) W
  have hξ : E'.hom.val.app (op U) ξ = (1 : Γ(Spec D, U)) :=
    (congrArg (j.appIso U).hom.hom (regularListModelTopClass_one s hs J e W)).trans
      (map_one (j.appIso U).hom.hom)
  have hi : E'.inv.val.app (op U) (1 : Γ(Spec D, U)) = ξ :=
    (congrArg (E'.inv.val.app (op U)) hξ.symm).trans
      (congrArg (fun k => k.val.app (op U) ξ) E'.hom_inv_id)
  apply (cancel_epi E'.inv).mp
  apply (unitHomGlobalSectionsEquiv (Spec D) N).injective
  change f.val.app (op U) (E'.inv.val.app (op U) (1 : Γ(Spec D, U))) =
    g.val.app (op U) (E'.inv.val.app (op U) (1 : Γ(Spec D, U)))
  exact (congrArg (f.val.app (op U)) hi).trans
    (h.trans (congrArg (g.val.app (op U)) hi).symm)

end AlgebraicGeometry.Scheme.Modules
