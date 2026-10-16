/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Cohomology.Godement.TotalComplex.PushforwardQuasiIso
public import Aglib.AlgebraicGeometry.Modules.Complex.PlusQuasiIso

/-!
Source: `Quillen/AlgebraicGeometry/Scheme/Sheaf/GodementWeakTransformation.lean` at LOCAL Quillen
`189a8e779f0c68b2dfc6f8195daebb3e684a5905`. Selection: whole_general;
source ranges [[1, 36]]. Actual objects, maps and hypotheses are preserved.
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u v w
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open AlgebraicGeometry.Scheme.Modules.Plus

namespace AlgebraicGeometry.Scheme.Modules.Godement

variable {D : Type v} [Category.{w} D] {X : Scheme.{u}}
    {F G H : D ⥤ CochainComplex.Plus X.Modules}

lemma plus_whiskerTotalImage_quasiIso {Y : Scheme.{u}} (p : X ⟶ Y)
    (a : F ⟶ G) (ha : ∀ K, QuasiIso (a.app K).hom) (K : D) :
    QuasiIso ((Functor.whiskerRight a
      (godementTotalPlus X ⋙ (Scheme.Modules.pushforward p).mapCochainComplexPlus)).app K).hom := by
  let := ha K
  exact pushGodementPlus_map_quasiIso p (a.app K)

end AlgebraicGeometry.Scheme.Modules.Godement
