/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.CategoryTheory.Sites.Torsor.Basic
public import Mathlib.CategoryTheory.Sites.LocallyBijective

/-! # Maps of the selected actual sheaf torsors

An equivariant map for identical coefficients is locally bijective and hence
an isomorphism. The proof uses no set-sheafification or enough-points premise.
-/

@[expose] public section

noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory.Limits Opposite

namespace CategoryTheory.Sheaf

universe u v w e
variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
variable {L M : Sheaf J AddCommGrpCat.{w}}

/-- A torsor morphism relative to an actual coefficient sheaf morphism. -/
structure Torsor.Hom (q : L ⟶ M) (P : Torsor L) (Q : Torsor M) where
  /-- The morphism of carrier sheaves underlying the coefficient-relative torsor morphism. -/
  map : P.carrier ⟶ Q.carrier
  equivariant : ∀ U a t,
    map.hom.app U (P.action U a t) = Q.action U (q.hom.app U a) (map.hom.app U t)

variable {P Q : Torsor L}

/-- A same-coefficient equivariant torsor morphism is injective on every section set. -/
theorem Torsor.Hom.injective (r : Torsor.Hom (𝟙 L) P Q) (U : Cᵒᵖ) :
    Function.Injective (r.map.hom.app U) := by
  intro s t h
  obtain ⟨a, ha, _⟩ := P.unique_transport U s t
  have he : Q.action U a (r.map.hom.app U s) = r.map.hom.app U t := by
    exact (r.equivariant U a s).symm.trans (congrArg (r.map.hom.app U) ha)
  have hz : a = 0 := (Q.unique_transport U (r.map.hom.app U s)
    (r.map.hom.app U s)).unique (he.trans h.symm) (Q.zero_action U _)
  simpa only [hz, P.zero_action] using ha

/-- Local nonemptiness of the source proves local surjectivity. -/
instance Torsor.Hom.locallySurjective (r : Torsor.Hom (𝟙 L) P Q) :
    Sheaf.IsLocallySurjective r.map where
  imageSieve_mem {U} t := by
    refine J.superset_covering ?_ (P.locally_nonempty U)
    rintro V f ⟨p⟩
    obtain ⟨a, ha, _⟩ := Q.unique_transport (op V) (r.map.hom.app (op V) p)
      (Q.carrier.obj.map f.op t)
    refine ⟨P.action (op V) a p, ?_⟩
    exact (r.equivariant (op V) a p).trans ha

/-- The actual underlying sheaf map of a same-coefficient torsor map is invertible. -/
instance Torsor.Hom.map_isIso (r : Torsor.Hom (𝟙 L) P Q) : IsIso r.map := by
  let : Presheaf.IsLocallyInjective J r.map.hom :=
    Presheaf.isLocallyInjective_of_injective _ _ r.injective
  exact (Sheaf.isLocallyBijective_iff_isIso r.map).mp ⟨inferInstance, inferInstance⟩

/-- Genuine torsor maps are actual equivariant isomorphisms, without 03AJ. -/
noncomputable def Torsor.Hom.toIso (r : Torsor.Hom (𝟙 L) P Q) : Torsor.Iso P Q where
  carrierIso := asIso r.map
  equivariant := r.equivariant

end CategoryTheory.Sheaf
