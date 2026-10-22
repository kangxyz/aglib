/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Mathlib.Algebra.Category.Ring.FilteredColimits
public import Mathlib.CategoryTheory.Filtered.Final
public import Mathlib.RingTheory.FiniteType

/-!
# Eventual surjectivity in finite-type quotient systems

For a filtered diagram with surjective transition homomorphisms, a map from a
fixed ring which is surjective at the colimit is surjective at a finite stage,
provided one stage is of finite type. No finite-presentation or Noetherian
hypothesis is used. The finite-generator test is separated from the diagram
argument so that geometric inverse-limit arguments can use the actual maps.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace RingHom.FiniteType

universe u v w

/-- Finitely many algebra generators test surjectivity after any quotient. -/
theorem exists_finset_surjective_of_surjective
    {R : Type u} {A : Type v} [CommRing R] [CommRing A]
    (f : R →+* A) (hf : f.FiniteType) :
    ∃ s : Finset A, ∀ {B : Type w} [CommRing B] (q : A →+* B),
      Function.Surjective q →
      (∀ x ∈ s, q x ∈ Set.range (q.comp f)) → Function.Surjective (q.comp f) := by
  let : Algebra R A := f.toAlgebra
  obtain ⟨s, hs⟩ := hf.out
  refine ⟨s, fun {B} _ q hq hgen ↦ ?_⟩
  let : Algebra R B := (q.comp f).toAlgebra
  let q' : A →ₐ[R] B := { q with commutes' := fun _ ↦ rfl }
  have htop : (⊤ : Subalgebra R A) ≤ (⊥ : Subalgebra R B).comap q' := by
    rw [← hs]
    exact Algebra.adjoin_le fun x hx ↦ hgen x hx
  intro b
  obtain ⟨a, rfl⟩ := hq b
  exact Algebra.mem_bot.mp (htop (Algebra.mem_top : a ∈ (⊤ : Subalgebra R A)))

end RingHom.FiniteType

namespace CommRingCat

universe u

/-- A surjection from a fixed ring onto a filtered colimit of quotients is
already surjective at some stage after a specified finite-type stage. -/
theorem exists_surjective_of_isColimit
    {I : Type u} [Category.{u} I] [IsFiltered I]
    (D : I ⥤ CommRingCat.{u}) (c : Cocone D) (hc : IsColimit c)
    {R : CommRingCat.{u}} (t : (Functor.const I).obj R ⟶ D)
    (f : R ⟶ c.pt) (hfac : ∀ i, t.app i ≫ c.ι.app i = f)
    (htrans : ∀ {i j} (q : i ⟶ j), Function.Surjective (D.map q))
    (hf : Function.Surjective f) (i : I) (hi : (t.app i).hom.FiniteType) :
    ∃ j : Under i, Function.Surjective (t.app j.right) := by
  classical
  obtain ⟨s, hs⟩ := RingHom.FiniteType.exists_finset_surjective_of_surjective
    (t.app i).hom hi
  choose r hr using fun x : s ↦ hf ((c.ι.app i) x.1)
  have heq (x : s) :
      (c.ι.app i) x.1 = (c.ι.app i) ((t.app i) (r x)) := by
    rw [← ConcreteCategory.comp_apply, hfac]
    exact (hr x).symm
  choose j q hq using fun x : s ↦
    (Types.FilteredColimit.isColimit_eq_iff'
      (isColimitOfPreserves (forget CommRingCat) hc) x.1 ((t.app i) (r x))).mp (heq x)
  let e (x : s) : Under i := Under.mk (q x)
  obtain ⟨k, hk⟩ := IsFiltered.sup_objs_exists (Finset.univ.image e)
  let a (x : s) : e x ⟶ k := (hk (Finset.mem_image_of_mem e (Finset.mem_univ x))).some
  have hw (x : s) : q x ≫ (a x).right = k.hom := Under.w (a x)
  have htk : t.app i ≫ D.map k.hom = t.app k.right := by
    simpa using (t.naturality k.hom).symm
  refine ⟨k, ?_⟩
  have hsurj := hs (D.map k.hom).hom (htrans k.hom) (fun x hx ↦ ?_)
  · change Function.Surjective ((t.app i ≫ D.map k.hom).hom) at hsurj
    rwa [htk] at hsurj
  · refine ⟨r ⟨x, hx⟩, ?_⟩
    change (D.map k.hom) ((t.app i) (r ⟨x, hx⟩)) = (D.map k.hom) x
    rw [← hw ⟨x, hx⟩, D.map_comp]
    exact congrArg (D.map (a ⟨x, hx⟩).right) (hq ⟨x, hx⟩).symm

end CommRingCat
