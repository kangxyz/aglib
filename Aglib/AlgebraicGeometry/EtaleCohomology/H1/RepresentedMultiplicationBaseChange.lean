/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.H1.RepresentedEpimorphisms
public import Aglib.AlgebraicGeometry.EtaleCohomology.H1.RepresentedKernel.Native
public import Aglib.AlgebraicGeometry.Group.BaseChange.MarkedKernel

/-! Original represented multiplication after group base change. -/

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open MonoidalCategory CartesianMonoidalCategory MonObj
open scoped CategoryTheory.MonObj

@[expose] public noncomputable section

namespace AlgebraicGeometry.Scheme.Group.BaseChange

universe u

attribute [local instance] Over.cartesianMonoidalCategory

variable {S T : Scheme.{u}} (f : S ⟶ T) (G : Grp (Over T)) [IsCommMonObj G.X]

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- Pullback retains commutativity of the original group. -/
theorem groupSchemeBaseChange_isCommMonObj :
    IsCommMonObj ((groupSchemeBaseChange f).functor.obj G).X := by
  let P := Over.pullback f
  let : GrpObj (P.obj G.X) := (P.mapGrp.obj G).grp
  exact Functor.isCommMonObj_obj (F := Over.pullback f)

attribute [local instance] groupSchemeBaseChange_isCommMonObj

/-- Pullback preserves the original positive multiplication morphism. -/
theorem groupSchemeBaseChange_map_identity_pow (n : ℕ) :
    (groupSchemeBaseChange f).functor.map ((𝟙 G : G ⟶ G) ^ n) =
      (𝟙 ((groupSchemeBaseChange f).functor.obj G)) ^ n := by
  let P := Over.pullback f
  let : GrpObj (P.obj G.X) := (P.mapGrp.obj G).grp
  let : IsCommMonObj (P.mapGrp.obj G).X := groupSchemeBaseChange_isCommMonObj f G
  apply Grp.hom_ext
  change P.map (((𝟙 G : G ⟶ G) ^ n).hom.hom) =
    (((𝟙 (P.mapGrp.obj G)) ^ n).hom.hom)
  simp only [Grp.Hom.hom_pow, Mon.Hom.hom_pow]
  change P.map ((𝟙 G.X) ^ n) = (𝟙 (P.obj G.X)) ^ n
  calc
    _ = (P.map (𝟙 G.X)) ^ n := (P.homMonoidHom (X := G.X) (M := G.X)).map_pow _ _
    _ = _ := congrArg (fun (a : P.obj G.X ⟶ P.obj G.X) => a ^ n) (P.map_id G.X)

end AlgebraicGeometry.Scheme.Group.BaseChange

namespace AlgebraicGeometry.Scheme.EtaleCohomology

open Scheme.Group.BaseChange

universe u

attribute [local instance] Over.cartesianMonoidalCategory groupSchemeBaseChange_isCommMonObj

/-- The original étale-surjective multiplication remains epic on the
represented sheaf after the original base change. -/
theorem epi_nsmul_representedSheaf_groupBaseChange
    {S T : Scheme.{u}} (f : S ⟶ T) (G : Grp (Over T)) [IsCommMonObj G.X] (n : ℕ)
    (he : Etale (((𝟙 G : G ⟶ G) ^ n).hom.hom.left))
    (hs : Surjective (((𝟙 G : G ⟶ G) ^ n).hom.hom.left)) :
    Epi (n • 𝟙 (representedSheaf ((groupSchemeBaseChange f).functor.obj G))) := by
  let G' := (groupSchemeBaseChange f).functor.obj G
  let q := (𝟙 G : G ⟶ G) ^ n
  let q' := (𝟙 G' : G' ⟶ G') ^ n
  have h := groupSchemeBaseChange_map_identity_pow f G n
  have hE : Etale q'.hom.hom.left :=
    (congrArg (fun g : G' ⟶ G' => Etale g.hom.hom.left) h).mp (map_etale f q he)
  have hS : Surjective q'.hom.hom.left :=
    (congrArg (fun g : G' ⟶ G' => Surjective g.hom.hom.left) h).mp (map_surjective f q hs)
  let : Etale q'.hom.hom.left := hE
  let : Surjective q'.hom.hom.left := hS
  rw [← RepresentedKernel.Native.representedSheafMap_multiplication G' n]
  exact representedSheafMap_epi_of_etale_surjective q'

end AlgebraicGeometry.Scheme.EtaleCohomology
