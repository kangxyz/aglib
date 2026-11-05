/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.Topology.JacobsonSpace.OpenCover
public import Mathlib.AlgebraicGeometry.Sites.EtalePoint
public import Mathlib.AlgebraicGeometry.Morphisms.UniversallyOpen

/-! # Original geometric marks on etale covers detected at closed points

The open images of the supplied etale maps cover a Jacobson target once they
cover its closed points. The native etale point-lifting theorem then lifts
any prescribed separably closed field-valued point over the unchanged field.
The covers themselves, and any property of those covers, are retained.
-/

@[expose] public noncomputable section

open CategoryTheory

namespace AlgebraicGeometry.Scheme

universe u v

/-- Closed-point coverage by actual etale maps retains every original
separably closed geometric mark on one of those same maps. -/
theorem exists_geometricPoint_lift_of_closedPoint_etale_cover
    {X : Scheme.{u}} [JacobsonSpace X] {ι : Type v}
    (Y : ι → Scheme.{u}) (f : ∀ i, Y i ⟶ X) [∀ i, Etale (f i)]
    (hclosed : ∀ x : X, IsClosed ({x} : Set X) → ∃ i, x ∈ Set.range (f i))
    (Ω : Type u) [Field Ω] [IsSepClosed Ω] (x : Spec (.of Ω) ⟶ X) :
    ∃ (i : ι) (y : Spec (.of Ω) ⟶ Y i), y ≫ f i = x := by
  have hopen (i : ι) : IsOpen (Set.range (f i)) := by
    simpa only [Set.image_univ] using (f i).isOpenMap Set.univ isOpen_univ
  obtain ⟨i, y, hy⟩ := TopologicalSpace.exists_mem_open_of_closedPoint_cover
    (fun i => Set.range (f i)) hopen hclosed (x default)
  obtain ⟨l, hl, _⟩ := exists_fac_of_etale_of_isSepClosed (f i) x y hy
  exact ⟨i, l, hl⟩

/-- A property carried by actual etale charts at every closed point can be
retained on a chart above any specified separably closed geometric point. -/
theorem exists_pointed_etale_property_of_closedPoints
    {X : Scheme.{u}} [JacobsonSpace X] (P : X.Etale → Prop)
    (hclosed : ∀ x : X, IsClosed ({x} : Set X) →
      ∃ (U : X.Etale) (y : U.left), U.hom y = x ∧ P U)
    (Ω : Type u) [Field Ω] [IsSepClosed Ω] (x : Spec (.of Ω) ⟶ X) :
    ∃ (U : X.Etale) (y : Spec (.of Ω) ⟶ U.left), y ≫ U.hom = x ∧ P U := by
  let ι := { U : X.Etale // P U }
  have hcover (z : X) (hz : IsClosed ({z} : Set X)) :
      ∃ i : ι, z ∈ Set.range i.val.hom := by
    obtain ⟨U, y, hy, hP⟩ := hclosed z hz
    exact ⟨⟨U, hP⟩, y, hy⟩
  obtain ⟨i, y, hy⟩ := exists_geometricPoint_lift_of_closedPoint_etale_cover
    (fun i : ι => i.val.left) (fun i => i.val.hom) hcover Ω x
  exact ⟨i.val, y, hy, i.property⟩

end AlgebraicGeometry.Scheme
