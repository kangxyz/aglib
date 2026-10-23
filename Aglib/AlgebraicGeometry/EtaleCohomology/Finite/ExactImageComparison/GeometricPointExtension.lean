/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Morphisms.FormallyUnramified.Immersions
public import Mathlib.AlgebraicGeometry.Sites.EtalePoint

/-! # Actual etale points under extensions of a separably closed field

The spectrum map need not be an isomorphism. What is bijective is the map on
etale-valued points: every etale point over a separably closed field gives an
open section, through which a field-valued point with that support factors.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Scheme.EtaleCohomology

universe u

/-- A map supported on an open section is its base map followed by that section. -/
theorem eq_comp_section_of_range {T U Y : Scheme.{u}} (t : U ⟶ T) (s : T ⟶ U)
    [IsOpenImmersion s] (hs : s ≫ t = 𝟙 T) (p : Y ⟶ U) (b : Y ⟶ T)
    (hp : p ≫ t = b) (hrange : Set.range p ⊆ Set.range s) : p = b ≫ s := by
  let l := IsOpenImmersion.lift s p hrange
  have hl : l ≫ s = p := IsOpenImmersion.lift_fac s p hrange
  have hb : l = b := by
    calc
      l = l ≫ (s ≫ t) := by rw [hs, Category.comp_id]
      _ = p ≫ t := by rw [← Category.assoc, hl]
      _ = b := hp
  rw [← hl, hb]

variable {κ Ω : Type u} [Field κ] [IsSepClosed κ] [Field Ω]

omit [IsSepClosed κ] in
/-- Two rational etale sections with the same support agree as actual scheme maps. -/
theorem etale_sections_eq_of_point {U : Scheme.{u}} (t : U ⟶ Spec (.of κ)) [Etale t]
    (s r : Spec (.of κ) ⟶ U) (hs : s ≫ t = 𝟙 _) (hr : r ≫ t = 𝟙 _)
    (hpoint : s default = r default) : s = r := by
  have : IsOpenImmersion r := IsOpenImmersion.of_section_formallyUnramified r t hr
  have hrange : Set.range s ⊆ Set.range r := by
    rintro _ ⟨x, rfl⟩
    refine ⟨default, ?_⟩
    simpa only [Subsingleton.elim x default] using hpoint.symm
  simpa only [Category.id_comp] using
    eq_comp_section_of_range t r hr s (𝟙 _) hs hrange

/-- Extending the field gives a bijection on actual points of an etale scheme over
its separably closed base field. The field extension itself is not asserted invertible. -/
theorem bijective_etale_point_extension (e : Spec (.of Ω) ⟶ Spec (.of κ))
    {U : Scheme.{u}} (t : U ⟶ Spec (.of κ)) [Etale t] :
    Function.Bijective
      (fun s : Over.mk (𝟙 (Spec (.of κ))) ⟶ Over.mk t =>
        (Over.homMk e (Category.comp_id e) : Over.mk e ⟶ Over.mk (𝟙 _)) ≫ s) := by
  let : Inhabited (Over.mk e).left := inferInstanceAs (Inhabited (Spec (.of Ω)))
  let : Subsingleton (Over.mk e).left := inferInstanceAs (Subsingleton (Spec (.of Ω)))
  constructor
  · intro s r h
    apply Over.OverMorphism.ext
    apply etale_sections_eq_of_point t s.left r.left s.w r.w
    have hp := congrArg (fun k : Over.mk e ⟶ Over.mk t => k.left default) h
    change s.left (e default) = r.left (e default) at hp
    simpa only [Subsingleton.elim (e default) (default : Spec (.of κ))] using hp
  · intro p
    obtain ⟨s, hs, hpoint⟩ := Scheme.exists_fac_of_etale_of_isSepClosed t
      (𝟙 (Spec (.of κ))) (p.left default) (Subsingleton.elim _ _)
    have : IsOpenImmersion s := IsOpenImmersion.of_section_formallyUnramified s t hs
    have hrange : Set.range p.left ⊆ Set.range s := by
      rintro _ ⟨x, rfl⟩
      refine ⟨default, ?_⟩
      simpa only [Subsingleton.elim x (default : Spec (.of Ω))] using hpoint
    refine ⟨Over.homMk s hs, ?_⟩
    apply Over.OverMorphism.ext
    exact (eq_comp_section_of_range t s hs p.left e p.w hrange).symm

end AlgebraicGeometry.Scheme.EtaleCohomology
