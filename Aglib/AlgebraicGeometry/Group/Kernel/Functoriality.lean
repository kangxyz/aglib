/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Group.Kernel.Basic

/-! Commuting squares act on the same native group kernels over any base. -/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory MonObj
open scoped CategoryTheory.MonObj

universe u

namespace AlgebraicGeometry.Scheme.Group.Kernel

attribute [local instance] Over.cartesianMonoidalCategory

variable {S : Scheme.{u}} {G H G' H' G'' H'' : Grp (Over S)}

/-- The original kernel inclusion is killed by the original map. -/
theorem inclusion_comp_eq_one (p : G ⟶ H) :
    (inclusion p).hom.hom ≫ p.hom.hom = 1 := (square p).w

/-- Actual group maps preserve the original identity morphisms. -/
theorem identityHom_comp (b : H ⟶ H') :
    identityHom (E := H) ≫ b = identityHom (E := H') := by
  apply Grp.hom_ext
  exact IsMonHom.one_hom b.hom.hom

/-- A commuting square induces a map of the original native kernels. -/
@[no_expose]
def map (p : G ⟶ H) (q : G' ⟶ H') (a : G ⟶ G') (b : H ⟶ H')
    (w : a ≫ q = p ≫ b) : group p ⟶ group q :=
  pullback.lift (inclusion p ≫ a) (pullback.snd p (identityHom (E := H))) (by
    rw [Category.assoc, w, ← identityHom_comp b]
    have h := congrArg (fun c : group p ⟶ H => c ≫ b)
      (pullback.condition (f := p) (g := identityHom (E := H)))
    exact (Category.assoc (inclusion p) p b).symm.trans
      (h.trans (Category.assoc (pullback.snd p (identityHom (E := H)))
        (identityHom (E := H)) b)))

/-- The induced map retains the literal source map and original inclusions. -/
@[reassoc (attr := simp)]
theorem map_inclusion (p : G ⟶ H) (q : G' ⟶ H') (a : G ⟶ G') (b : H ⟶ H')
    (w : a ≫ q = p ≫ b) : map p q a b w ≫ inclusion q = inclusion p ≫ a :=
  pullback.lift_fst _ _ _

/-- Equality after the original inclusion determines a map into a kernel. -/
theorem hom_ext_of_inclusion (p : G ⟶ H) {T : Grp (Over S)} {a b : T ⟶ group p}
    (h : a ≫ inclusion p = b ≫ inclusion p) : a = b := by
  have : Mono (inclusion p).hom.hom := (square p).mono_fst_of_mono
  apply Grp.hom_ext
  apply (cancel_mono (inclusion p).hom.hom).mp
  exact congrArg (fun c : T ⟶ G => c.hom.hom) h

/-- The identity square acts as the identity on the same original kernel. -/
@[simp]
theorem map_id (p : G ⟶ H) : map p p (𝟙 G) (𝟙 H) (by simp) = 𝟙 (group p) := by
  apply hom_ext_of_inclusion p
  simp only [map_inclusion, Category.comp_id, Category.id_comp]

/-- Composition of actual squares gives composition of their native kernel maps. -/
theorem map_comp (p : G ⟶ H) (q : G' ⟶ H') (r : G'' ⟶ H'')
    (a : G ⟶ G') (b : H ⟶ H') (w : a ≫ q = p ≫ b)
    (a' : G' ⟶ G'') (b' : H' ⟶ H'') (w' : a' ≫ r = q ≫ b') :
    map p q a b w ≫ map q r a' b' w' =
      map p r (a ≫ a') (b ≫ b') (by rw [Category.assoc, w', ← Category.assoc, w,
        Category.assoc]) := by
  apply hom_ext_of_inclusion r
  simp only [Category.assoc, map_inclusion, map_inclusion_assoc]

/-- An isomorphism of the original squares gives the original kernel isomorphism. -/
def mapIso (p : G ⟶ H) (q : G' ⟶ H') (a : G ≅ G') (b : H ≅ H')
    (w : a.hom ≫ q = p ≫ b.hom) : group p ≅ group q where
  hom := map p q a.hom b.hom w
  inv := map q p a.inv b.inv (by
    apply (cancel_mono b.hom).mp
    simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
    rw [← w, Iso.inv_hom_id_assoc])
  hom_inv_id := by
    apply hom_ext_of_inclusion p
    simp only [Category.assoc, map_inclusion, map_inclusion_assoc,
      Iso.hom_inv_id, Category.comp_id, Category.id_comp]
  inv_hom_id := by
    apply hom_ext_of_inclusion q
    simp only [Category.assoc, map_inclusion, map_inclusion_assoc,
      Iso.inv_hom_id, Category.comp_id, Category.id_comp]

/-- The isomorphism's forward map is the same original kernel map. -/
theorem mapIso_hom (p : G ⟶ H) (q : G' ⟶ H') (a : G ≅ G') (b : H ≅ H')
    (w : a.hom ≫ q = p ≫ b.hom) :
    (mapIso p q a b w).hom = map p q a.hom b.hom w := rfl

end AlgebraicGeometry.Scheme.Group.Kernel
