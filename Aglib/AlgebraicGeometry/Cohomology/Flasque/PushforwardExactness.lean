/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Cohomology.Flasque.Pushforward
public import Mathlib.Algebra.Homology.HomologicalComplexAbelian

/-!
Source: `Quillen/AlgebraicGeometry/Scheme/Sheaf/FlasquePushforwardExact.lean` at LOCAL Quillen
`189a8e779f0c68b2dfc6f8195daebb3e684a5905`. Selection: whole_general;
source ranges [[1, 61]]. Actual objects, maps and hypotheses are preserved.
-/

/-!
# Exact direct image of sequences with flasque kernel terms

The original sheaf direct image preserves the kernel and lifts every quotient
section using the original flasque-kernel theorem. The degreewise version
applies to the actual direct image of complexes without an upper bound.
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

open AlgebraicGeometry.Scheme.Modules

namespace AlgebraicGeometry.Scheme.Modules

/-- Actual direct image preserves a short exact sequence with flasque kernel. -/
theorem pushforward_shortExact_of_flasque_kernel {X Y : Scheme.{u}} (f : X ⟶ Y)
    {S : ShortComplex X.Modules} (hS : S.ShortExact)
    [TopCat.Presheaf.IsFlasque S.X₁.presheaf] :
    (S.map (Scheme.Modules.pushforward f)).ShortExact := by
  let F := Scheme.Modules.pushforward f
  have : Mono S.f := hS.mono_f
  have : Epi (F.map S.g) := by
    constructor
    intro N g h eq
    ext U m
    obtain ⟨x, hx⟩ := sections_surjective_of_flasque_kernel hS (f ⁻¹ᵁ U) m
    have hc := congrArg (fun q => q.app U x) eq
    change g.app U (S.g.app (f ⁻¹ᵁ U) x) = h.app U (S.g.app (f ⁻¹ᵁ U) x) at hc
    simpa only [hx] using hc
  exact {
    exact := hS.exact.map_of_mono_of_preservesKernel F inferInstance inferInstance
    mono_f := (inferInstance : Mono (F.map S.f))
    epi_g := (inferInstance : Epi (F.map S.g)) }

/-- The original degreewise direct image preserves every complex short exact
sequence whose first complex has flasque terms. No bound is required. -/
theorem pushforwardComplex_shortExact_of_flasque_kernel {X Y : Scheme.{u}} (f : X ⟶ Y)
    {S : ShortComplex (CochainComplex X.Modules ℤ)} (hS : S.ShortExact)
    (hK : ∀ n, TopCat.Presheaf.IsFlasque (S.X₁.X n).presheaf) :
    (S.map ((Scheme.Modules.pushforward f).mapHomologicalComplex (.up ℤ))).ShortExact := by
  apply HomologicalComplex.shortExact_of_degreewise_shortExact
  intro n
  have hs := (HomologicalComplex.shortExact_iff_degreewise_shortExact S).mp hS n
  let : TopCat.Presheaf.IsFlasque
    (S.map (HomologicalComplex.eval X.Modules (.up ℤ) n)).X₁.presheaf := hK n
  exact pushforward_shortExact_of_flasque_kernel f hs

end AlgebraicGeometry.Scheme.Modules
