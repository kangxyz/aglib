/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.GeometricPoints.FieldTerminal
public import Aglib.AlgebraicGeometry.EtaleCohomology.GeometricPoints.StalkUniverse

/-! # Original sections detect isomorphisms over a separably closed field

The actual identity geometric point alone detects covering sieves. Its original
terminal germ and the native point-universe comparison then show that original
abelian global sections reflect isomorphisms. No cohomological or properness
hypothesis is used.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry.Scheme.EtaleCohomology

attribute [local instance] hasSheafifyLarge

variable (Ω : Type u) [Field Ω] [IsSepClosed Ω]

/-- The singleton original identity point, at the native coefficient universe. -/
def fieldIdentityPointFamily :
    ObjectProperty (GrothendieckTopology.Point.{u + 1}
      (Spec (.of Ω)).smallEtaleTopology) :=
  ObjectProperty.ofObj (fun _ : Unit => FibrewiseClosed.largePoint (𝟙 (Spec (.of Ω))))

/-- The actual identity geometric point is conservative on the small etale site. -/
theorem fieldIdentityPointFamily_isConservative :
    (fieldIdentityPointFamily Ω).IsConservativeFamilyOfPoints := by
  apply ObjectProperty.IsConservativeFamilyOfPoints.mk'
  intro U R hR
  obtain ⟨ι, V, a, rfl⟩ := R.exists_eq_ofArrows
  rw [ofArrows_mem_smallEtaleTopology_iff]
  ext s
  simp only [Set.mem_iUnion, Set.mem_range, Set.mem_univ, iff_true]
  let η := 𝟙 (Spec (.of Ω))
  have hη : U.hom s = η default :=
    @Subsingleton.elim (Spec (.of Ω)) inferInstance (U.hom s) (η default)
  obtain ⟨l, hl, hls⟩ := exists_fac_of_etale_of_isSepClosed U.hom η s hη
  let t : (FibrewiseClosed.largePoint η).fiber.obj U := ULift.up (Over.homMk l hl)
  obtain ⟨W, g, ⟨Z, k, _, ⟨i⟩, rfl⟩, y, hy⟩ :=
    hR ⟨FibrewiseClosed.largePoint η, ⟨()⟩⟩ t
  have hraw := congrArg ULift.down hy
  have hleft := congrArg
    (fun q : Over.mk η ⟶ (Scheme.Etale.forget (Spec (.of Ω))).obj U => q.left) hraw
  have heq : (y.down.left ≫ k.left) ≫ (a i).left = l := by
    change y.down.left ≫ (k.left ≫ (a i).left) = l at hleft
    exact (Category.assoc _ _ _).trans hleft
  refine ⟨i, (y.down.left ≫ k.left) (default : Spec (.of Ω)), ?_⟩
  exact (congrArg (fun q : Spec (.of Ω) ⟶ U.left => q default) heq).trans hls

/-- Original global sections over a separably closed field detect isomorphisms
of actual abelian sheaves, through the original terminal germs. -/
theorem isIso_of_field_globalSections
    {F G : AbelianSheaf.{u, u + 1} (Spec (.of Ω))} (a : F ⟶ G)
    [IsIso ((globalSections (Spec (.of Ω))).map a)] : IsIso a := by
  let Φ := pointSmallEtale (𝟙 (Spec (.of Ω)))
  have hraw : IsIso (Φ.sheafFiber.map a) := by
    change IsIso (Φ.presheafFiber.map a.hom)
    apply (isIso_comp_left_iff
      (Φ.toPresheafFiber (etaleTerminal (Spec (.of Ω))) (fieldTerminalPoint Ω) F.obj) _).mp
    rw [Φ.toPresheafFiber_naturality a.hom
      (etaleTerminal (Spec (.of Ω))) (fieldTerminalPoint Ω)]
    let : IsIso (a.hom.app (op (etaleTerminal (Spec (.of Ω))))) :=
      inferInstanceAs (IsIso ((globalSections (Spec (.of Ω))).map a))
    infer_instance
  have hlarge : IsIso ((FibrewiseClosed.largePoint (𝟙 (Spec (.of Ω)))).sheafFiber.map a) :=
    (NatIso.isIso_map_iff (StalkUniverse.sheafFiberIso (𝟙 (Spec (.of Ω)))) a).mpr hraw
  rw [((fieldIdentityPointFamily_isConservative Ω).jointlyReflectIsomorphisms
    AddCommGrpCat.{u + 1}).isIso_iff]
  rintro ⟨Ψ, hΨ⟩
  obtain ⟨j⟩ := hΨ
  exact hlarge

end AlgebraicGeometry.Scheme.EtaleCohomology
