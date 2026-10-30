/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Group.LineBundleCube.Basic
public import Aglib.AlgebraicGeometry.Picard.LineBundleFamily.ProjectiveCube

/-!
# The cube identity for projective geometrically integral group schemes

The projective Picard construction and scheme rigidity prove the cube identity
on the original Picard group. The universal family uses the existing right
associated product `G ⊗ (G ⊗ G)`. Pulling its equality back gives the identity
for three actual morphisms from every test scheme, including nonreduced ones.
-/

@[expose] public section

noncomputable section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open scoped CategoryTheory.MonObj

namespace AlgebraicGeometry.Scheme.Group.LineBundleCube

open Scheme.Modules.Invertible Scheme.Modules.Invertible.PullbackTensor.Local
open Scheme.RelativePicard

universe u

attribute [local instance] Over.cartesianMonoidalCategory

variable {k : Type u} [Field k]

private theorem familyScheme_map_eq_whiskerLeft (G : Over (Spec (.of k)))
    {T T' : Over (Spec (.of k))} (f : T ⟶ T') :
    (familyScheme G.hom).map f = (G ◁ f).left := rfl

set_option backward.isDefEq.respectTransparency false in
private theorem originSection_eq_lift_one (G T : Over (Spec (.of k))) [GrpObj G]
    (ho : η[G].left ≫ G.hom = 𝟙 _) :
    originSection G.hom η[G].left ho T = (lift (1 : T ⟶ G) (𝟙 T)).left := by
  apply pullback.hom_ext <;> simp [originSection, Hom.one_def]

set_option backward.isDefEq.respectTransparency false in
/-- The cube identity on the original Picard group of a projective,
geometrically integral group scheme over a field, pulled back along any three
actual morphisms. No hypothesis is imposed on the test scheme. -/
theorem cubeClass_eq_zero (G : Over (Spec (.of k))) [GrpObj G]
    [IsHProjective G.hom] [GeometricallyIntegral G.hom]
    {T : Over (Spec (.of k))} (f g h : T ⟶ G) (a : PicardGroup G.left) :
    cubeClass f g h a = 0 := by
  let q₁ : G ⊗ (G ⊗ G) ⟶ G := fst G (G ⊗ G)
  let q₂ : G ⊗ (G ⊗ G) ⟶ G := snd G (G ⊗ G) ≫ fst G G
  let q₃ : G ⊗ (G ⊗ G) ⟶ G := snd G (G ⊗ G) ≫ snd G G
  have ho : η[G].left ≫ G.hom = 𝟙 _ := by simp
  have hc : cubeClass q₁ q₂ q₃ a = 0 := by
    apply familyClass_eq_zero_of_group_axes_of_isHProjective G.hom η[G].left ho G
    · rw [originSection_eq_lift_one]
      change pullbackHom (lift (1 : G ⊗ G ⟶ G) (𝟙 (G ⊗ G))).left
        (cubeClass q₁ q₂ q₃ a) = 0
      rw [cubeClass_pullback]
      simpa only [q₁, q₂, q₃, lift_fst, lift_snd_assoc, Category.id_comp] using
        cubeClass_one_left (fst G G) (snd G G) a
    · rw [familyScheme_map_eq_whiskerLeft]
      change pullbackHom (G ◁ lift (𝟙 G) (1 : G ⟶ G)).left
        (cubeClass q₁ q₂ q₃ a) = 0
      rw [cubeClass_pullback]
      simpa only [q₁, q₂, q₃, whiskerLeft_fst, whiskerLeft_snd_assoc,
        lift_fst, lift_snd, Category.comp_id, MonObj.comp_one] using
          cubeClass_one_right (fst G G) (snd G G) a
    · rw [familyScheme_map_eq_whiskerLeft]
      change pullbackHom (G ◁ lift (1 : G ⟶ G) (𝟙 G)).left
        (cubeClass q₁ q₂ q₃ a) = 0
      rw [cubeClass_pullback]
      simpa only [q₁, q₂, q₃, whiskerLeft_fst, whiskerLeft_snd_assoc,
        lift_fst, lift_snd, Category.comp_id, MonObj.comp_one] using
          cubeClass_one_middle (fst G G) (snd G G) a
  have hp := congrArg (pullbackHom (lift f (lift g h)).left) hc
  rw [map_zero, cubeClass_pullback] at hp
  simpa only [q₁, q₂, q₃, lift_fst, lift_snd_assoc, lift_fst, lift_snd] using hp

/-- The cube identity written directly as an equality of the original
pullback classes, for all test schemes. -/
theorem pullbackClass_cube (G : Over (Spec (.of k))) [GrpObj G]
    [IsHProjective G.hom] [GeometricallyIntegral G.hom]
    {T : Over (Spec (.of k))} (f g h : T ⟶ G) (a : PicardGroup G.left) :
    pullbackClass (f * g * h).left a + pullbackClass f.left a +
        pullbackClass g.left a + pullbackClass h.left a =
      pullbackClass (f * g).left a + pullbackClass (f * h).left a +
        pullbackClass (g * h).left a := by
  apply sub_eq_zero.mp
  have hc := cubeClass_eq_zero G f g h a
  simp only [cubeClass, pullbackHom_apply] at hc
  convert hc using 1
  abel

end AlgebraicGeometry.Scheme.Group.LineBundleCube
