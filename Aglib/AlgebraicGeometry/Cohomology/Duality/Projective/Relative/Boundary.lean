/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.Algebra.Homology.DerivedCategory.TStructure.HomToSingle

/-!
# Determining the trace component of a triangle

An epimorphism on top homology determines maps to a single in that degree.
Consequently, the third component supplied by TR3 is the prescribed trace
whenever the first two squares commute. Epimorphism cancellation takes place
in the coefficient category, with no epimorphism assertion in the derived
category. A shifted target triangle retains its native signs in both squares.
-/

@[expose] public section

noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated

universe u v w

namespace DerivedCategory

variable {C : Type u} [Category.{v} C] [Abelian C] [HasDerivedCategory.{w} C]

/-- Top-homology epimorphisms can be cancelled against maps to a top single. -/
theorem homToSingle_precomp_injective_of_epi_homology
    {K L : DerivedCategory C} (n : ℤ) [K.IsLE n] [L.IsLE n]
    (f : K ⟶ L) [Epi ((homologyFunctor C n).map f)] (V : C) :
    Function.Injective (fun g : L ⟶ (singleFunctor C n).obj V => f ≫ g) := by
  intro g h hgh
  apply (homToSingleAddEquiv L n V).injective
  apply (cancel_epi ((homologyFunctor C n).map f)).mp
  simpa only [homToSingleAddEquiv_naturality_left] using
    congrArg (homToSingleAddEquiv K n V) hgh

/-- TR3 has the prescribed third component if top homology determines it.
The target may be a shifted short-exact triangle, with its native signs. -/
theorem triangle_comm₃_of_epi_topHomology
    (T₁ T₂ : Triangle (DerivedCategory C))
    (hT₁ : T₁ ∈ distTriang (DerivedCategory C))
    (hT₂ : T₂ ∈ distTriang (DerivedCategory C))
    (n : ℤ) [T₁.obj₂.IsLE n] [T₁.obj₃.IsLE n]
    [Epi ((homologyFunctor C n).map T₁.mor₂)]
    (V : C) (e : T₂.obj₃ ≅ (singleFunctor C n).obj V)
    (a : T₁.obj₁ ⟶ T₂.obj₁) (b : T₁.obj₂ ⟶ T₂.obj₂)
    (c : T₁.obj₃ ⟶ T₂.obj₃)
    (h₁ : T₁.mor₁ ≫ b = a ≫ T₂.mor₁)
    (h₂ : T₁.mor₂ ≫ c = b ≫ T₂.mor₂) :
    T₁.mor₃ ≫ a⟦1⟧' = c ≫ T₂.mor₃ := by
  obtain ⟨c', hc₂, hc₃⟩ :=
    complete_distinguished_triangle_morphism T₁ T₂ hT₁ hT₂ a b h₁
  have hcc : c' ≫ e.hom = c ≫ e.hom := by
    apply homToSingle_precomp_injective_of_epi_homology n T₁.mor₂ V
    simp only [← Category.assoc, hc₂, h₂]
  have hc : c' = c := (cancel_mono e.hom).mp hcc
  simpa only [hc] using hc₃

end DerivedCategory
