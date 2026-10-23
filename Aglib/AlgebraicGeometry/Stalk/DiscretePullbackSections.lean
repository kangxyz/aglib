/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Stalk.DiscreteSections

/-!
# Original section coordinates along a discrete local-ring comparison

When the source is discrete and its original stalk maps are isomorphisms,
its global units are exactly tuples of units in the corresponding target
stalks. The original pullback is the tuple of original germs.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Scheme

universe u

variable {P U : Scheme.{u}} (f : P ⟶ U) [DiscreteTopology P]
  [∀ p : P, IsIso (f.stalkMap p)]

/-- Actual global functions expressed in the target's actual stalk rings. -/
def globalSectionsTargetStalkProduct : Γ(P, ⊤) ≃+* ∀ p : P, U.presheaf.stalk (f p) :=
  (globalSectionsStalkProduct P).trans
    (RingEquiv.piCongrRight fun p => (asIso (f.stalkMap p)).symm.commRingCatIsoToRingEquiv)

/-- The function pullback is literally the tuple of original target germs. -/
theorem globalSectionsTargetStalkProduct_appTop (a : Γ(U, ⊤)) (p : P) :
    globalSectionsTargetStalkProduct f (f.appTop a) p =
      U.presheaf.germ ⊤ (f p) trivial a := by
  have hg : (f.stalkMap p) (U.presheaf.germ ⊤ (f p) trivial a) =
      P.presheaf.germ ⊤ p trivial (f.appTop a) :=
    f.germ_stalkMap_apply ⊤ p trivial a
  have hcoord := globalSectionsStalkProduct_apply P (f.appTop a) p
  change (CategoryTheory.inv (f.stalkMap p)) ((globalSectionsStalkProduct P) (f.appTop a) p) = _
  exact (congrArg (fun b => (CategoryTheory.inv (f.stalkMap p)) b) (hcoord.trans hg.symm)).trans
    (ConcreteCategory.congr_hom (IsIso.hom_inv_id (f.stalkMap p))
      (U.presheaf.germ ⊤ (f p) trivial a))

/-- Actual global units expressed in the target's actual stalk rings. -/
def globalUnitsTargetStalkProduct : Γ(P, ⊤)ˣ ≃* ∀ p : P, (U.presheaf.stalk (f p))ˣ :=
  (Units.mapEquiv (globalSectionsTargetStalkProduct f).toMulEquiv).trans MulEquiv.piUnits

/-- The unit pullback is literally the tuple of original target unit germs. -/
theorem globalUnitsTargetStalkProduct_appTop (a : Γ(U, ⊤)ˣ) (p : P) :
    globalUnitsTargetStalkProduct f (Units.map f.appTop.hom.toMonoidHom a) p =
      Units.map (U.presheaf.germ ⊤ (f p) trivial).hom.toMonoidHom a := by
  apply Units.ext
  exact globalSectionsTargetStalkProduct_appTop f (a : Γ(U, ⊤)) p

end AlgebraicGeometry.Scheme
