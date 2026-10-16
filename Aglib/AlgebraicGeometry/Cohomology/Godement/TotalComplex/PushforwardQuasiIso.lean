/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Cohomology.Godement.TotalComplex.QuasiIso
public import Aglib.AlgebraicGeometry.Cohomology.Flasque.Complex
public import Aglib.AlgebraicGeometry.Modules.Complex.PlusQuasiIso

/-!
Source: `Quillen/AlgebraicGeometry/Scheme/Sheaf/GodementWeakComposition.lean` at LOCAL Quillen
`189a8e779f0c68b2dfc6f8195daebb3e684a5905`. Selection: whole_general;
source ranges [[1, 41]]. Actual objects, maps and hypotheses are preserved.
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u v w
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open AlgebraicGeometry.Scheme.Modules.Plus

namespace AlgebraicGeometry.Scheme.Modules.Godement

lemma totalPushforwardPlus_quasiIso {X Y : Scheme.{u}} (p : X ⟶ Y)
    {K L : CochainComplex.Plus X.Modules} (f : K ⟶ L) [QuasiIso f.hom] :
    QuasiIso
      (((Scheme.Modules.pushforward p).mapHomologicalComplex (.up ℤ)).map
        ((godementTotal X).map f.hom)) := by
  let : QuasiIso ((godementTotal X).map f.hom) := godementTotalPlus_map_quasiIso f
  obtain ⟨a, ha⟩ := K.property
  obtain ⟨b, hb⟩ := L.property
  let := ha
  let := hb
  have hz := fun n hn => CochainComplex.isZero_of_isStrictlyGE K.obj a n hn
  have hw := fun n hn => CochainComplex.isZero_of_isStrictlyGE L.obj b n hn
  let : ((godementTotal X).obj K.obj).IsStrictlyGE a := godementTotal_isStrictlyGE K.obj a hz
  let : ((godementTotal X).obj L.obj).IsStrictlyGE b := godementTotal_isStrictlyGE L.obj b hw
  exact quasiIso_pushforward_of_flasque p ((godementTotal X).map f.hom) a b
    (fun n hn => CochainComplex.isZero_of_isStrictlyGE
      ((godementTotal X).obj K.obj) a n hn)
    (fun n hn => CochainComplex.isZero_of_isStrictlyGE
      ((godementTotal X).obj L.obj) b n hn)
    (godementTotal_isFlasque K.obj a hz) (godementTotal_isFlasque L.obj b hw)

lemma pushGodementPlus_map_quasiIso {X Y : Scheme.{u}} (p : X ⟶ Y)
    {A B : CochainComplex.Plus X.Modules} (m : A ⟶ B) [QuasiIso m.hom] :
    QuasiIso (((godementTotalPlus X ⋙
      (Scheme.Modules.pushforward p).mapCochainComplexPlus).map m).hom) := by
  change QuasiIso (((Scheme.Modules.pushforward p).mapHomologicalComplex (.up ℤ)).map
    ((godementTotal X).map m.hom))
  exact totalPushforwardPlus_quasiIso p m

end AlgebraicGeometry.Scheme.Modules.Godement
