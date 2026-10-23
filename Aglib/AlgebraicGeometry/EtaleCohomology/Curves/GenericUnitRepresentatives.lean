/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.Curves.GenericArtin
public import Aglib.Topology.NoetherianCurveSupport

/-!
# Actual unit representatives around the generic Artin points

Units in the original generic stalk rings, including nilpotents, have genuine
affine unit representatives on neighborhoods containing no other generic
point. These neighborhoods cover the complement of finitely many closed
points on a Noetherian curve. No function-field substitution is made.
-/

@[expose] public noncomputable section

open CategoryTheory Opposite TopologicalSpace Set

namespace AlgebraicGeometry.Scheme.EtaleCohomology.Curves

universe u

variable (X : Scheme.{u})

private theorem exists_affine_unit_representative (x : X) (a : (X.presheaf.stalk x)ˣ)
    (O : X.Opens) (hxO : x ∈ O) :
    ∃ (W : X.Opens) (_ : IsAffineOpen W) (hxW : x ∈ W) (s : Γ(X, W)ˣ),
      W ≤ O ∧ X.presheaf.germ W x hxW (s : Γ(X, W)) = (a : X.presheaf.stalk x) := by
  obtain ⟨U, hxU, f, hf⟩ := X.presheaf.exists_germ_eq (a : X.presheaf.stalk x)
  have hu : IsUnit (X.presheaf.germ U x hxU f) := by rw [hf]; exact a.isUnit
  obtain ⟨V, i, hxV, hv⟩ := X.toRingedSpace.isUnit_res_of_isUnit_germ U f x hxU hu
  obtain ⟨W, hW, hxW, hWV⟩ := exists_isAffineOpen_mem_and_subset
    (X := X) (U := V ⊓ O) (x := x) ⟨hxV, hxO⟩
  let j : W ⟶ V := homOfLE (hWV.trans inf_le_left)
  let s : Γ(X, W)ˣ := Units.map (X.presheaf.map j.op).hom.toMonoidHom hv.unit
  refine ⟨W, hW, hxW, s, hWV.trans inf_le_right, ?_⟩
  change X.presheaf.germ W x hxW (X.presheaf.map j.op hv.unit) = _
  rw [X.presheaf.germ_res_apply j x hxW, hv.unit_spec,
    X.presheaf.germ_res_apply i x hxV, hf]

/-- Each actual generic stalk unit has an affine representative isolated from other generics. -/
theorem exists_isolated_generic_unit_representative [IsNoetherian X]
    (η : genericPoints X) (a : (X.presheaf.stalk η.val)ˣ) :
    ∃ (W : X.Opens) (_ : IsAffineOpen W) (hηW : η.val ∈ W) (s : Γ(X, W)ˣ),
      (∀ θ : genericPoints X, θ.val ∈ W → θ = η) ∧
      X.presheaf.germ W η.val hηW (s : Γ(X, W)) = (a : X.presheaf.stalk η.val) := by
  obtain ⟨O, hO, ⟨x, hx⟩, hOC⟩ :=
    NoetherianSpace.exists_isOpen_nonempty_subset_irreducibleComponent
      (closure ({η.val} : Set X)) η.property
  have hηO : η.val ∈ O :=
    (isGenericPoint_closure.mem_open_set_iff hO).2 ⟨x, hOC hx, hx⟩
  obtain ⟨W, hW, hηW, s, hWO, hs⟩ :=
    exists_affine_unit_representative X η.val a ⟨O, hO⟩ hηO
  refine ⟨W, hW, hηW, s, ?_, hs⟩
  intro θ hθW
  have h : η.val ⤳ θ.val := specializes_iff_mem_closure.mpr (hOC (hWO hθW))
  exact Subtype.ext ((h.antisymm (genericPoint_isMax X θ h)).eq.symm)

/-- A tuple of actual generic units is locally regular outside a finite closed set. -/
theorem generic_units_represented_off_finite [IsNoetherian X]
    (hdim : topologicalKrullDim X ≤ 1)
    (a : ∀ η : genericPoints X, (X.presheaf.stalk η.val)ˣ) :
    ∃ (W : genericPoints X → X.Opens) (_hW : ∀ η, IsAffineOpen (W η))
      (hηW : ∀ η, η.val ∈ W η) (s : ∀ η, Γ(X, W η)ˣ),
      (∀ η θ, θ.val ∈ W η → θ = η) ∧
      (∀ η, X.presheaf.germ (W η) η.val (hηW η) (s η : Γ(X, W η)) = a η) ∧
      ((⋃ η, (W η : Set X))ᶜ).Finite := by
  choose W hW hηW s hiso hs using fun η =>
    exists_isolated_generic_unit_representative X η (a η)
  refine ⟨W, hW, hηW, s, hiso, hs, ?_⟩
  exact TopologicalSpace.finite_compl_open_of_contains_genericPoints hdim
    (isOpen_iUnion fun η => (W η).isOpen)
    (fun x hx => mem_iUnion.mpr ⟨⟨x, hx⟩, hηW ⟨x, hx⟩⟩)

end AlgebraicGeometry.Scheme.EtaleCohomology.Curves
