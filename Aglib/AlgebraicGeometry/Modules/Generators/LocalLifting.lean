/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Mathlib.AlgebraicGeometry.Modules.Sheaf
public import Mathlib.Topology.Sheaves.LocallySurjective
/-!
# Simultaneous local lifting of finitely many sections

For a locally surjective morphism of sheaves of modules on a scheme, finitely
many sections admit lifts on one common neighborhood of any chosen point.
The finite intersection construction also handles the empty family of sections.
-/
@[expose] public section


noncomputable section

universe u v

open CategoryTheory TopologicalSpace Opposite AlgebraicGeometry

namespace AlgebraicGeometry.Scheme.Modules

/-- Finitely many sections lift simultaneously near any point under a locally
surjective morphism of module sheaves. The common neighborhood is contained in
the original domain, including when the indexing type is empty. -/
theorem exists_finite_local_lifts {X : Scheme.{u}} {M N : X.Modules}
    (f : M ⟶ N)
    [_root_.PresheafOfModules.IsLocallySurjective (Opens.grothendieckTopology X) f.val]
    {I : Type v} [Finite I] (U : X.Opens) (t : I → N.val.obj (op U))
    (x : X) (hx : x ∈ U) :
    ∃ (V : X.Opens) (hVU : V ≤ U), x ∈ V ∧
      ∃ s : I → M.val.obj (op V),
        ∀ i, f.val.app (op V) (s i) = N.val.map (homOfLE hVU).op (t i) := by
  classical
  let g := (_root_.PresheafOfModules.toPresheaf X.ringCatSheaf.obj).map f.val
  have hg : TopCat.Presheaf.IsLocallySurjective g :=
    (inferInstance : _root_.PresheafOfModules.IsLocallySurjective
      (Opens.grothendieckTopology X) f.val)
  have hi : ∀ i : I, ∃ (W : X.Opens) (hWU : W ≤ U) (s : M.val.obj (op W)),
      f.val.app (op W) s = N.val.map (homOfLE hWU).op (t i) ∧ x ∈ W := by
    intro i
    obtain ⟨W, hWU, ⟨s, hs⟩, hxW⟩ :=
      (TopCat.Presheaf.isLocallySurjective_iff g).mp hg U (t i) x hx
    exact ⟨W, hWU, s, hs, hxW⟩
  choose W hWU s hs hxW using hi
  let V : X.Opens := U ⊓ ⨅ i, W i
  have hVU : V ≤ U := inf_le_left
  have hVW (i : I) : V ≤ W i := inf_le_right.trans (iInf_le W i)
  have hxV : x ∈ V := by
    change x ∈ ((U ⊓ ⨅ i, W i : X.Opens) : Set X)
    rw [Opens.coe_inf, Opens.coe_iInf]
    exact ⟨hx, Set.mem_iInter.mpr hxW⟩
  refine ⟨V, hVU, hxV, fun i => M.val.map (homOfLE (hVW i)).op (s i), ?_⟩
  intro i
  change f.val.app (op V) (M.val.map (homOfLE (hVW i)).op (s i)) = _
  rw [_root_.PresheafOfModules.naturality_apply]
  have hsi : f.val.app (op (W i)) (s i) =
      N.val.map (homOfLE (hWU i)).op (t i) := hs i
  rw [hsi, ← N.val.map_comp_apply]
  rfl

end AlgebraicGeometry.Scheme.Modules
