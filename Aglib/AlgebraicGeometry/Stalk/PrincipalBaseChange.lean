/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Stalk.Scalar
public import Mathlib.AlgebraicGeometry.Stalk
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import Mathlib.AlgebraicGeometry.Limits
public import Mathlib.RingTheory.Ideal.Quotient.Operations
public import Mathlib.RingTheory.LocalRing.Quotient

/-!
# Principal kernels on actual base-change stalks

The actual quotient of the original local ring supplies a local test scheme.
The pullback universal property lifts it, and injectivity of the closed
projection identifies its closed point with the original given point.
The local-spectrum factorization then computes the original stalk-map kernel.
-/

@[expose] public noncomputable section

open CategoryTheory Limits AlgebraicGeometry TopologicalSpace
universe u
namespace AlgebraicGeometry.Scheme.Hom

private lemma fromSpecStalk_comp_structure
    {R : Type u} [CommRing R] {X : Scheme.{u}}
    (π : X ⟶ Spec (.of R)) (x : X) :
    X.fromSpecStalk x ≫ π = Spec.map (CommRingCat.ofHom (π.stalkScalar x)) := by
  rw [← Scheme.SpecMap_stalkMap_fromSpecStalk π, Spec.fromSpecStalk_eq,
    ← Spec.map_comp]
  congr 1
  apply CommRingCat.hom_ext
  exact (π.stalkScalar_eq_local x).symm

private lemma ker_stalkMap_le_ker_of_factor
    {Y X : Scheme.{u}} (b : Y ⟶ X) [IsClosedImmersion b] (y : Y)
    (D : CommRingCat.{u}) [IsLocalRing D]
    (φ : X.presheaf.stalk (b y) ⟶ D) [IsLocalHom φ.hom]
    (m : Spec D ⟶ Y)
    (hm : m ≫ b = Spec.map φ ≫ X.fromSpecStalk (b y)) :
    RingHom.ker (b.stalkMap y).hom ≤ RingHom.ker φ.hom := by
  have hmy : m (IsLocalRing.closedPoint D) = y := by
    apply b.isClosedEmbedding.injective
    have h := congrArg (fun f : Spec D ⟶ X => f (IsLocalRing.closedPoint D)) hm
    change b (m (IsLocalRing.closedPoint D)) =
      X.fromSpecStalk (b y) (Spec.map φ (IsLocalRing.closedPoint D)) at h
    rw [Spec_closedPoint, Scheme.fromSpecStalk_closedPoint] at h
    exact h
  subst y
  have heq : b.stalkMap (m (IsLocalRing.closedPoint D)) ≫
      Scheme.stalkClosedPointTo m = φ := by
    apply Spec.map_injective
    apply (cancel_mono (X.fromSpecStalk (b (m (IsLocalRing.closedPoint D))))).mp
    rw [Spec.map_comp, Category.assoc, Scheme.SpecMap_stalkMap_fromSpecStalk,
      ← Category.assoc, Scheme.Spec_stalkClosedPointTo_fromSpecStalk]
    exact hm
  intro r hr
  have h := congrArg
    (fun f : X.presheaf.stalk (b (m (IsLocalRing.closedPoint D))) ⟶ D => f r) heq
  change Scheme.stalkClosedPointTo m (b.stalkMap _ r) = φ r at h
  change b.stalkMap _ r = 0 at hr
  rw [hr, map_zero] at h
  exact h.symm

private lemma scalar_image_zero_of_base_kills
    {R S : Type u} [CommRing R] [CommRing S] (f : R →+* S)
    {X : Scheme.{u}} (π : X ⟶ Spec (.of R))
    (y : (pullback π (Spec.map (CommRingCat.ofHom f)) : Scheme.{u}))
    (a : R) (ha : f a = 0) :
    (pullback.fst π (Spec.map (CommRingCat.ofHom f))).stalkMap y
      (π.stalkScalar ((pullback.fst π (Spec.map (CommRingCat.ofHom f))) y) a) = 0 := by
  let b := pullback.fst π (Spec.map (CommRingCat.ofHom f))
  let t := pullback.snd π (Spec.map (CommRingCat.ofHom f))
  change b.stalkMap y ((X.presheaf.germ ⊤ (b y) trivial)
    (π.appTop ((Scheme.ΓSpecIso (.of R)).inv a))) = 0
  erw [Scheme.Hom.germ_stalkMap_apply]
  have h := congrArg
    (fun g : (pullback π (Spec.map (CommRingCat.ofHom f)) : Scheme.{u}) ⟶ Spec (.of R) =>
      g.appTop ((Scheme.ΓSpecIso (.of R)).inv a))
    (pullback.condition (f := π) (g := Spec.map (CommRingCat.ofHom f)))
  change b.appTop (π.appTop ((Scheme.ΓSpecIso (.of R)).inv a)) =
    t.appTop ((Spec.map (CommRingCat.ofHom f)).appTop
      ((Scheme.ΓSpecIso (.of R)).inv a)) at h
  have hs := congrArg
    (fun k : CommRingCat.of R ⟶ Γ(Spec (.of S), ⊤) => k a)
    (Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom f))
  change (Scheme.ΓSpecIso (.of S)).inv (f a) =
    (Spec.map (CommRingCat.ofHom f)).appTop ((Scheme.ΓSpecIso (.of R)).inv a) at hs
  rw [← hs, ha, map_zero, map_zero] at h
  erw [h, map_zero]

/-- A surjective base-ring map with principal kernel has that same principal
kernel on the actual stalks of its literal scheme pullback projection.
No flatness, domain or Noetherian condition is required. -/
theorem ker_stalkMap_pullback_fst_of_principal
    {R S : Type u} [CommRing R] [CommRing S] (f : R →+* S)
    (hf : Function.Surjective f) (a : R) (hker : RingHom.ker f = Ideal.span {a})
    {X : Scheme.{u}} (π : X ⟶ Spec (.of R))
    (y : (pullback π (Spec.map (CommRingCat.ofHom f)) : Scheme.{u})) :
    RingHom.ker ((pullback.fst π (Spec.map (CommRingCat.ofHom f))).stalkMap y).hom =
      Ideal.span {π.stalkScalar ((pullback.fst π (Spec.map (CommRingCat.ofHom f))) y) a} := by
  let b : (pullback π (Spec.map (CommRingCat.ofHom f)) : Scheme.{u}) ⟶ X :=
    pullback.fst π (Spec.map (CommRingCat.ofHom f))
  let : IsClosedImmersion (Spec.map (CommRingCat.ofHom f)) :=
    IsClosedImmersion.spec_of_surjective _ hf
  let A : CommRingCat.{u} := X.presheaf.stalk (b y)
  let I : Ideal A := Ideal.span {π.stalkScalar (b y) a}
  have ha : f a = 0 := by
    change a ∈ RingHom.ker f
    rw [hker]
    exact Ideal.subset_span (Set.mem_singleton a)
  have hle : I ≤ RingHom.ker (b.stalkMap y).hom := by
    apply (RingHom.ker (b.stalkMap y).hom).span_singleton_le_iff_mem.mpr
    exact scalar_image_zero_of_base_kills f π y a ha
  have hI : I ≠ ⊤ := ne_top_of_le_ne_top (RingHom.ker_ne_top _) hle
  let D := A ⧸ I
  let : Nontrivial D := Ideal.Quotient.nontrivial_iff.mpr hI
  let q : A →+* D := Ideal.Quotient.mk I
  let : IsLocalRing D := IsLocalRing.of_surjective' q Ideal.Quotient.mk_surjective
  let : IsLocalHom q := IsLocalHom.of_surjective q Ideal.Quotient.mk_surjective
  let φ : R →+* D := q.comp (π.stalkScalar (b y))
  have hφ : RingHom.ker f ≤ RingHom.ker φ := by
    rw [hker]
    apply (RingHom.ker φ).span_singleton_le_iff_mem.mpr
    change q (π.stalkScalar (b y) a) = 0
    exact Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.subset_span (Set.mem_singleton _))
  let e : S →+* D := f.liftOfSurjective hf ⟨φ, hφ⟩
  have he : e.comp f = φ := f.liftOfSurjective_comp hf ⟨φ, hφ⟩
  let lX : Spec (.of D) ⟶ X :=
    Spec.map (CommRingCat.ofHom q) ≫ X.fromSpecStalk (b y)
  let lS : Spec (.of D) ⟶ Spec (.of S) := Spec.map (CommRingCat.ofHom e)
  have hw : lX ≫ π = lS ≫ Spec.map (CommRingCat.ofHom f) := by
    dsimp only [lX, lS]
    rw [Category.assoc, fromSpecStalk_comp_structure, ← Spec.map_comp, ← Spec.map_comp]
    congr 1
    apply CommRingCat.hom_ext
    exact he.symm
  let m : Spec (.of D) ⟶ pullback π (Spec.map (CommRingCat.ofHom f)) :=
    pullback.lift lX lS hw
  have hrev := ker_stalkMap_le_ker_of_factor b y (.of D) (CommRingCat.ofHom q) m
    (pullback.lift_fst lX lS hw)
  change RingHom.ker (b.stalkMap y).hom ≤ RingHom.ker (Ideal.Quotient.mk I) at hrev
  rw [Ideal.mk_ker] at hrev
  exact le_antisymm hrev hle

end AlgebraicGeometry.Scheme.Hom
