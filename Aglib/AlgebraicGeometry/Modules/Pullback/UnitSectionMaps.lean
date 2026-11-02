/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Modules.Pullback.Tensor.RightUnit
public import Aglib.AlgebraicGeometry.Modules.StructureSheaf.Hom

/-!
# Global sections of pulled-back section maps

For a morphism of schemes `q : Y ⟶ X`, the inverse of the unit comparison
`pullbackUnitIso q : q^* 𝒪_X ≅ 𝒪_Y` sends the global section `1` to the image of `1` under the
adjunction unit `𝒪_X ⟶ q_* q^* 𝒪_X` (`pullbackUnitIso_inv_one`). Consequently, for a global
section `s` of a module `F` on `X`, the global section of
`(pullbackUnitIso q).inv ≫ q^*(𝒪_X ⟶ F)`, where `𝒪_X ⟶ F` corresponds to `s` under
`unitHomGlobalSectionsEquiv`, is the image of `s` under the adjunction unit
`F ⟶ q_* q^* F` (`unitHomGlobalSectionsEquiv_pullbackUnitIso_inv_comp`).

No hypothesis on `q` or `F` is needed. The second statement restates the private lemma
`unitHomGlobalSectionsEquiv_pullback` of `Cohomology/DirectImage/ResolutionSections/Pullback`
(there for an arbitrary `k : 𝒪_X ⟶ F`, here for `k = (unitHomGlobalSectionsEquiv X F).symm s`);
it is public here for the monomial sections of `HilbertScheme/DirectImageSheafEpi`.
-/

@[expose] public section

noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory Opposite

universe u

namespace AlgebraicGeometry.Scheme.Modules

variable {X Y : Scheme.{u}}

/-- The inverse of `pullbackUnitIso` sends `1` to the adjunction-unit image of `1`. -/
theorem pullbackUnitIso_inv_one (q : Y ⟶ X) :
    (pullbackUnitIso q).inv.val.app (op ⊤) (1 : Γ(Y, ⊤)) =
      ((pullbackPushforwardAdjunction q).unit.app (SheafOfModules.unit X.ringCatSheaf)).val.app
        (op ⊤) (1 : Γ(X, ⊤)) := by
  have h := pullbackUnitIso_hom_unit_one q ⊤
  have hi := congrArg (fun k => k.val.app (op (q ⁻¹ᵁ ⊤))
    (((pullbackPushforwardAdjunction q).unit.app (SheafOfModules.unit X.ringCatSheaf)).val.app
      (op ⊤) (1 : Γ(X, ⊤)))) (pullbackUnitIso q).hom_inv_id
  dsimp only at hi
  refine Eq.trans ?_ hi
  exact congrArg ((pullbackUnitIso q).inv.val.app (op (q ⁻¹ᵁ ⊤))) h.symm

/-- **The global section of a pulled-back section map**: for `s ∈ Γ(F, ⊤)` on `X` and
`q : Y ⟶ X`, the global section of `(pullbackUnitIso q).inv ≫ q^* (𝒪 ⟶ F)` is the
adjunction-unit image of `s`. -/
theorem unitHomGlobalSectionsEquiv_pullbackUnitIso_inv_comp (q : Y ⟶ X) {F : X.Modules}
    (s : Γ(F, ⊤)) :
    unitHomGlobalSectionsEquiv Y ((Scheme.Modules.pullback q).obj F)
        ((pullbackUnitIso q).inv ≫
          (Scheme.Modules.pullback q).map ((unitHomGlobalSectionsEquiv X F).symm s)) =
      ((pullbackPushforwardAdjunction q).unit.app F).val.app (op ⊤) s := by
  rw [unitHomGlobalSectionsEquiv_apply]
  change ((Scheme.Modules.pullback q).map ((unitHomGlobalSectionsEquiv X F).symm s)).val.app
      (op ⊤) ((pullbackUnitIso q).inv.val.app (op ⊤) (1 : Γ(Y, ⊤))) = _
  rw [pullbackUnitIso_inv_one]
  have hn := congrArg (fun k => k.val.app (op ⊤) (1 : Γ(X, ⊤)))
    ((pullbackPushforwardAdjunction q).unit.naturality ((unitHomGlobalSectionsEquiv X F).symm s))
  dsimp only [Functor.id_map, Functor.comp_map] at hn
  refine hn.symm.trans ?_
  have hs : Scheme.Modules.Hom.app ((unitHomGlobalSectionsEquiv X F).symm s) ⊤ (1 : Γ(X, ⊤)) =
      s :=
    (unitHomGlobalSectionsEquiv_apply X F _).symm.trans (Equiv.apply_symm_apply _ s)
  exact congrArg (((pullbackPushforwardAdjunction q).unit.app F).val.app (op ⊤)) hs

end AlgebraicGeometry.Scheme.Modules
