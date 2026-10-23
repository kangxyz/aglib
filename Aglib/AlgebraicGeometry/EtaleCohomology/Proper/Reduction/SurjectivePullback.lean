/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.GeometricPoints.InverseImage
public import Aglib.AlgebraicGeometry.EtaleCohomology.GeometricPoints.StalkUniverse
public import Aglib.AlgebraicGeometry.EtaleCohomology.DirectImage

/-! # Faithful original inverse image along a surjective morphism

The images of the existing algebraically closed geometric points upstairs
cover the underlying base. Their native standard-value site points detect
covering sieves. The published original stalk-unit and point-universe isos
therefore imply faithfulness of the original abelian inverse-image functor.
No new stalk comparison or continuity statement is constructed.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.Scheme.EtaleCohomology.Proper.Reduction

universe u

attribute [local instance] hasSheafifyLarge

variable {X S : Scheme.{u}} (f : X ⟶ S)

/-- The actual standard-value points on the base induced by the existing
algebraically closed geometric points at all original source points. -/
def surjectiveImagePointFamily :
    ObjectProperty (GrothendieckTopology.Point.{u + 1} S.smallEtaleTopology) :=
  ObjectProperty.ofObj (fun x : X =>
    FibrewiseClosed.largePoint (FibrewiseClosed.geometricPoint x ≫ f))

/-- Surjectivity makes these actual standard-value site points conservative
on every etale test object of the original base. -/
theorem surjectiveImagePointFamily_isConservative [Surjective f] :
    (surjectiveImagePointFamily f).IsConservativeFamilyOfPoints := by
  apply ObjectProperty.IsConservativeFamilyOfPoints.mk'
  intro U R hR
  obtain ⟨ι, V, a, rfl⟩ := R.exists_eq_ofArrows
  rw [ofArrows_mem_smallEtaleTopology_iff]
  ext s
  simp only [Set.mem_iUnion, Set.mem_range, Set.mem_univ, iff_true]
  obtain ⟨x, hx⟩ := f.surjective (U.hom s)
  let η := FibrewiseClosed.geometricPoint x ≫ f
  have hη : U.hom s = η default := by
    change U.hom s = f (FibrewiseClosed.geometricPoint x default)
    rw [FibrewiseClosed.geometricPoint_apply]
    exact hx.symm
  obtain ⟨l, hl, hls⟩ := exists_fac_of_etale_of_isSepClosed U.hom η s hη
  let t : (FibrewiseClosed.largePoint η).fiber.obj U := ULift.up (Over.homMk l hl)
  obtain ⟨W, g, ⟨Z, k, _, ⟨i⟩, rfl⟩, y, hy⟩ :=
    hR ⟨FibrewiseClosed.largePoint η, ⟨x⟩⟩ t
  have hraw := congrArg ULift.down hy
  have hleft := congrArg
    (fun q : Over.mk η ⟶ (Scheme.Etale.forget S).obj U => q.left) hraw
  have heq : (y.down.left ≫ k.left) ≫ (a i).left = l := by
    change y.down.left ≫ (k.left ≫ (a i).left) = l at hleft
    exact (Category.assoc _ _ _).trans hleft
  refine ⟨i, (y.down.left ≫ k.left)
    (default : Spec (.of (FibrewiseClosed.pointField x))), ?_⟩
  exact (congrArg (fun q : Spec (.of (FibrewiseClosed.pointField x)) ⟶ U.left =>
    q default) heq).trans hls

section NaturalIso

universe c d v w

/-- Equality after an actual natural isomorphism detects equality before it;
the calculation is performed on typed functors before concrete stalk substitution. -/
theorem map_eq_of_natIso
    {C : Type c} [Category.{v} C] {D : Type d} [Category.{w} D]
    {F G : C ⥤ D} (e : F ≅ G) {A B : C} {a b : A ⟶ B}
    (h : G.map a = G.map b) : F.map a = F.map b := by
  apply (cancel_mono (e.hom.app B)).mp
  rw [e.hom.naturality a, e.hom.naturality b, h]

end NaturalIso

/-- The original abelian inverse image of a surjective scheme morphism is faithful,
using only the published original stalk-unit and standard-universe bridge. -/
theorem inverseImage_faithful_of_surjective [Surjective f] :
    (inverseImage f).Faithful where
  map_injective {F G} {a b} hab := by
    apply ((surjectiveImagePointFamily_isConservative f).jointlyFaithful
      AddCommGrpCat.{u + 1}).map_injective
    rintro ⟨Φ, hΦ⟩
    obtain ⟨x⟩ := hΦ
    let η := FibrewiseClosed.geometricPoint x
    let e := StalkUniverse.sheafFiberIso (η ≫ f) ≪≫
      StalkInverseImage.stalkUnitNatIso f η ≪≫
      Functor.isoWhiskerLeft (inverseImage f) (StalkUniverse.sheafFiberIso η).symm
    exact map_eq_of_natIso e
      (congrArg (fun q => (FibrewiseClosed.largePoint η).sheafFiber.map q) hab)

/-- The actual original inverse image along a surjection detects monomorphisms. -/
theorem inverseImage_mono_iff_of_surjective [Surjective f]
    {F G : AbelianSheaf.{u, u + 1} S} (a : F ⟶ G) :
    Mono ((inverseImage f).map a) ↔ Mono a := by
  have := inverseImage_faithful_of_surjective f
  constructor
  · intro ha
    exact (inverseImage f).mono_of_mono_map ha
  · intro ha
    have : Mono a := ha
    infer_instance

end AlgebraicGeometry.Scheme.EtaleCohomology.Proper.Reduction
