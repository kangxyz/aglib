/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Approximation.FinitePresentationEnvelope.AffineGraph

/-!
# Simultaneous closed graphs for finitely many affine charts

A single original stage captures finite-type generators on every member of
a finite family of affine inverse-limit charts. Closedness is preserved on
passing to a later stage by cancellation against a separated morphism.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory Limits

universe u v

namespace AlgebraicGeometry.Scheme

/-- Finitely many affine-chart graphs are closed at one common original stage. -/
lemma exists_common_isClosedImmersion_graph_of_isLimit_of_isAffine
    {I : Type u} [Category.{u} I] [IsCofiltered I]
    {J : Type v} [Finite J]
    (D : J → I ⥤ Scheme.{u}) [∀ a i, IsAffine ((D a).obj i)]
    (c : ∀ a, Cone (D a)) (hc : ∀ a, IsLimit (c a))
    {S T : Scheme.{u}} [IsAffine S] [IsAffine T] (hT : IsTerminal T)
    (s : S ⟶ T) (t : ∀ a i, (D a).obj i ⟶ T)
    (f : ∀ a, (c a).pt ⟶ S) [∀ a, LocallyOfFiniteType (f a)] :
    ∃ i, ∀ a, IsClosedImmersion
      (pullback.lift (f := t a i) (g := s) ((c a).π.app i) (f a)
        (hT.hom_ext _ _)) := by
  classical
  let : Fintype J := Fintype.ofFinite J
  choose i hi using fun a => exists_isClosedImmersion_graph_of_isLimit_of_isAffine
    (D a) (c a) (hc a) s (t a) (f a) (fun _ => hT.hom_ext _ _)
  obtain ⟨k, hk⟩ := IsCofiltered.inf_objs_exists (Finset.univ.image i)
  let r (a : J) : k ⟶ i a := (hk (Finset.mem_image.mpr ⟨a, by simp, rfl⟩)).some
  refine ⟨k, fun a => ?_⟩
  let q := pullback.lift ((c a).π.app k) (f a)
    (hT.hom_ext (((c a).π.app k) ≫ t a k) (f a ≫ s))
  let q₀ := pullback.lift ((c a).π.app (i a)) (f a)
    (hT.hom_ext (((c a).π.app (i a)) ≫ t a (i a)) (f a ≫ s))
  let m := pullback.map (t a k) s (t a (i a)) s ((D a).map (r a))
    (𝟙 S) (𝟙 T) (hT.hom_ext _ _) (by simp)
  have he : q ≫ m = q₀ := by
    apply pullback.hom_ext <;> simp [q, q₀, m]
  have : IsClosedImmersion (q ≫ m) := by rw [he]; exact hi a
  exact IsClosedImmersion.of_comp q m

end AlgebraicGeometry.Scheme
