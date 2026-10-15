/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Cohomology.Flasque.Basic

/-!
Source: `Quillen/AlgebraicGeometry/Scheme/Sheaf/FlasqueExtensions.lean` at LOCAL Quillen
`189a8e779f0c68b2dfc6f8195daebb3e684a5905`. Selection: whole_general;
source ranges [[1, 56]]. Actual objects, maps and hypotheses are preserved.
-/

/-!
# Extension closure of flasque module sheaves

The original restriction maps are surjective for an extension of two flasque
module sheaves. The proof uses the installed section-lifting theorem for the
flasque kernel and the actual left-exact sequence of additive sheaf sections.
-/
@[expose] public section

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite

open AlgebraicGeometry.Scheme.Modules

namespace AlgebraicGeometry.Scheme.Modules

/-- Extensions of flasque module sheaves are flasque on every scheme. -/
theorem flasque_of_shortExact_outer {X : Scheme.{u}} {S : ShortComplex X.Modules}
    (hS : S.ShortExact) [TopCat.Presheaf.IsFlasque S.X₁.presheaf]
    [TopCat.Presheaf.IsFlasque S.X₃.presheaf] :
    TopCat.Presheaf.IsFlasque S.X₂.presheaf where
  epi {U V} k := by
    apply (AddCommGrpCat.epi_iff_surjective _).mpr
    intro z
    obtain ⟨c, hc⟩ := (AddCommGrpCat.epi_iff_surjective (S.X₃.presheaf.map k)).mp
      (TopCat.Presheaf.IsFlasque.epi k) (S.g.app V.unop z)
    obtain ⟨b, hb⟩ := sections_surjective_of_flasque_kernel hS U.unop c
    have hn := ConcreteCategory.congr_hom (S.g.mapPresheaf.naturality k) b
    change S.g.app V.unop (S.X₂.presheaf.map k b) =
      S.X₃.presheaf.map k (S.g.app U.unop b) at hn
    have hz : S.g.app V.unop (z - S.X₂.presheaf.map k b) = 0 := by
      rw [map_sub, hn, hb, hc, sub_self]
    obtain ⟨a, ha⟩ := TopCat.Sheaf.sections_exact_of_left_exact
      (shortExact_toSheaf hS).exact (shortExact_toSheaf hS).mono_f
      (z - S.X₂.presheaf.map k b) hz
    change S.f.app V.unop a = z - S.X₂.presheaf.map k b at ha
    obtain ⟨d, hd⟩ := (AddCommGrpCat.epi_iff_surjective (S.X₁.presheaf.map k)).mp
      (TopCat.Presheaf.IsFlasque.epi k) a
    refine ⟨b + S.f.app U.unop d, ?_⟩
    have hf := ConcreteCategory.congr_hom (S.f.mapPresheaf.naturality k) d
    change S.f.app V.unop (S.X₁.presheaf.map k d) =
      S.X₂.presheaf.map k (S.f.app U.unop d) at hf
    rw [map_add, ← hf, hd, ha]
    abel

end AlgebraicGeometry.Scheme.Modules
