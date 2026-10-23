/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.Fields.SeparablyClosedRootsH2
public import Aglib.AlgebraicGeometry.EtaleCohomology.Kummer.HenselianConstant

/-! # Original cyclic degree-two cohomology over separably closed constants

The existing strictly henselian constant-root coordinate on the constant field
is pulled to the actual function-field spectrum. No new coefficient model or
primitive-root marking is introduced.
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry
open GroupCohomology.Kummer.CoefficientBaseChange

namespace AlgebraicGeometry.Scheme.EtaleCohomology.Fields

universe u w

variable (K E : Type u) [Field K] [IsSepClosed K] [Field E]
  [Algebra (RatFunc K) E] [Algebra.IsAlgebraic (RatFunc K) E]
  [HasExt.{w} (AbelianSheaf.{u, u + 1} (Spec (.of E)))]

attribute [local instance] hasSheafifyLarge

/-- Original constant cyclic degree-two cohomology vanishes at every positive
level invertible in the separably closed constant field. -/
theorem constantH2_subsingleton_of_separablyClosed_ratFunc
    (n : ℕ) (hn : 0 < n) (hK : IsUnit (n : Γ(Spec (.of K), ⊤))) :
    Subsingleton (Sheaf.H.{w}
      (ConstantFinite.coefficient (ULift.{u} (ZMod n)) (Spec (.of E))) 2) := by
  let : IsSepClosed (IsLocalRing.ResidueField K) :=
    Algebra.IsAlgebraic.isSepClosed (F := K) (E := IsLocalRing.ResidueField K)
  let p : Spec (.of E) ⟶ Spec (.of K) :=
    Spec.map (CommRingCat.ofHom ((algebraMap (RatFunc K) E).comp (algebraMap K (RatFunc K))))
  let e := Kummer.HenselianConstant.constantRootIsoOver K n hn hK p
  have h := rootsH2_subsingleton_of_separablyClosed_ratFunc K E n hn (levelInvertible p n hK)
  refine ⟨fun a b => ?_⟩
  have hab := congrArg (Sheaf.H.map e.inv 2)
    (h.elim (Sheaf.H.map e.hom 2 a) (Sheaf.H.map e.hom 2 b))
  simpa only [← Sheaf.H.map_comp_apply, Iso.hom_inv_id, Sheaf.H.map_id_apply] using hab

end AlgebraicGeometry.Scheme.EtaleCohomology.Fields
