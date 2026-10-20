/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Aglib.AlgebraicGeometry.Group.MultiplicativeBaseChange
public import Mathlib.AlgebraicGeometry.Morphisms.UnderlyingMap
public import Aglib.CategoryTheory.TorsorAction.Basic
public import Aglib.AlgebraicGeometry.Morphisms.FiniteEtale.Basic
/-!
# Actual finite étale positive-root covers and their marked torsor action

Mathematical source: `K2-018#lem:k2018-geometric-exact-order` and the positive
Kummer convention used by `K2-018#prop:k2018-arithmetic-characters`, at source
revision `e73d98b1b5c1e5abcdebf7d058e436d792b87982`.
Frozen package basis: `7f86e4a1763cc4ec35e9b0a8acd659750355a0de`.

For an actual global unit a and positive n, `scheme X n a` is the pullback
along `X.toSpecΓ` of `Spec (Γ(X,⊤)[T]/(T^n - a))`. On every scheme over X its
sections are identified naturally with units b satisfying b^n = a after
restriction. The canonical global root is the identity section in these
coordinates. Monicity proves finite freeness of the coordinate algebra and
finiteness of the scheme morphism. Its constants map is injective; integral
lying-over and scheme base change prove actual surjectivity.

If n is invertible in Γ(X,⊤), an explicit standard-étale pair proves
étaleness. The Bézout coefficients use the inverses of n and a. No local-root
surjectivity or finite-étale family is assumed. Stacks Project tag 03PL is
the source correspondence for this monic root-cover construction.

The actual μ_n action morphism has coordinate z*b. The transport morphism
from p to q has coordinate q/p. The action-pair map is an actual scheme
isomorphism, and `coverTorsorAction` supplies the existing
`MarkedCovers.TorsorAction` on the literal finite-étale cover object.
These positive signs match the field cocycle sigma(b)/b. No sheaf-torsor
classification or H¹ comparison is asserted by this pure scheme layer;
those consumers use the proved all-test section and action identities.
The level n=1 is included, and n=0 is excluded.

Read-only inputs when this construction began: `MultiplicativeGroup.lean`
SHA-256 `00d2f93b8d66e0059bf60def78b7ace6d0420906d1aa114a62daca46972179ea`;
`RootsFiniteEtale.lean` SHA-256
`2e7f1464a9906715d3bed4f4ff162c10268e9737d457960f1bb1ff2f3976821a`;
`MultiplicativeBaseChange.lean` SHA-256
`a221c36942dd338b8e39ef0044f3f4a5ca431c7a2bc89ba49c15cb94f56fe7ff`.
All three received separately disclosed comment-only provenance repairs
before this module's final build. No production proof body was changed.
-/

@[expose] public section

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite Polynomial
open MonoidalCategory CartesianMonoidalCategory MonObj
open scoped CategoryTheory.MonObj CategoryTheory.Obj
namespace AlgebraicGeometry.Scheme.Group.RootCover
universe u
variable (R : Type u) [CommRing R]
def rootPolynomial (n : ℕ) (a : Rˣ) : R[X] := X ^ n - C (a : R)
abbrev RootAlgebra (n : ℕ) (a : Rˣ) := AdjoinRoot (rootPolynomial R n a)

theorem rootPolynomial_monic (n : ℕ) (hn : 0 < n) (a : Rˣ) :
    (rootPolynomial R n a).Monic := monic_X_pow_sub_C (a : R) hn.ne'

instance rootAlgebra_finite (n : ℕ) [NeZero n] (a : Rˣ) : Module.Finite R (RootAlgebra R n a) :=
  (rootPolynomial_monic R n (Nat.pos_of_ne_zero (NeZero.ne n)) a).finite_adjoinRoot

instance rootAlgebra_free (n : ℕ) [NeZero n] (a : Rˣ) : Module.Free R (RootAlgebra R n a) :=
  (rootPolynomial_monic R n (Nat.pos_of_ne_zero (NeZero.ne n)) a).free_adjoinRoot

theorem root_pow (n : ℕ) (a : Rˣ) :
    (AdjoinRoot.root (rootPolynomial R n a)) ^ n = algebraMap R (RootAlgebra R n a) a := by
  have h := AdjoinRoot.eval₂_root (rootPolynomial R n a)
  simp only [rootPolynomial, eval₂_sub, eval₂_pow, eval₂_X, eval₂_C, sub_eq_zero] at h
  exact h

def rootUnit (n : ℕ) [NeZero n] (a : Rˣ) : (RootAlgebra R n a)ˣ :=
  ((isUnit_pow_iff (NeZero.ne n)).mp
    (show IsUnit ((AdjoinRoot.root (rootPolynomial R n a)) ^ n) from by
      rw [root_pow]
      exact a.isUnit.map (algebraMap R (RootAlgebra R n a)))).unit

@[simp] theorem rootUnit_val (n : ℕ) [NeZero n] (a : Rˣ) :
    (rootUnit R n a : RootAlgebra R n a) = AdjoinRoot.root (rootPolynomial R n a) :=
  IsUnit.unit_spec _

theorem rootUnit_pow (n : ℕ) [NeZero n] (a : Rˣ) :
    rootUnit R n a ^ n = Units.map (algebraMap R (RootAlgebra R n a)).toMonoidHom a := by
  apply Units.ext
  change (rootUnit R n a : RootAlgebra R n a) ^ n = algebraMap R (RootAlgebra R n a) a
  rw [rootUnit_val, root_pow]

def standardPair (n : ℕ) (hn : 0 < n) (hinv : IsUnit (n : R)) (a : Rˣ) :
    StandardEtalePair R where
  f := rootPolynomial R n a
  monic_f := rootPolynomial_monic R n hn a
  g := 1
  cond := by
    obtain ⟨b, hb⟩ := hinv
    refine ⟨C ((↑(b⁻¹) : R) * ↑(a⁻¹)) * X, -C (↑(a⁻¹) : R), 0, ?_⟩
    rcases n with _ | m
    · omega
    have hb' : (m + 1 : R) * ↑(b⁻¹) = 1 := by
      simpa only [hb, Nat.cast_add, Nat.cast_one] using b.mul_inv
    simp only [rootPolynomial, derivative_sub, derivative_X_pow_succ, derivative_C,
      sub_zero, pow_zero]
    calc
      C (m + 1 : R) * X ^ m * (C ((↑(b⁻¹) : R) * ↑(a⁻¹)) * X) +
          (X ^ (m + 1) - C (a : R)) * -C (↑(a⁻¹) : R) =
        C ((m + 1 : R) * ↑(b⁻¹)) * C (↑(a⁻¹) : R) * X ^ (m + 1) -
          (X ^ (m + 1) - C (a : R)) * C (↑(a⁻¹) : R) := by
        simp only [map_mul, pow_succ]
        ring
      _ = C ((a : R) * ↑(a⁻¹)) := by rw [hb', map_one, map_mul]; ring
      _ = 1 := by rw [a.mul_inv, map_one]

def standardPairEquiv (n : ℕ) (hn : 0 < n) (hinv : IsUnit (n : R)) (a : Rˣ) :
    (standardPair R n hn hinv a).Ring ≃ₐ[R] RootAlgebra R n a := by
  let P := standardPair R n hn hinv a
  change P.Ring ≃ₐ[R] AdjoinRoot P.f
  have hP : P.HasMap (AdjoinRoot.root P.f) :=
    ⟨AdjoinRoot.eval₂_root P.f, by simp [P, standardPair]⟩
  refine AlgEquiv.ofAlgHom
    (P.lift (AdjoinRoot.root P.f) hP)
    (AdjoinRoot.liftAlgHom P.f (Algebra.ofId R P.Ring) P.X P.hasMap_X.1) ?_ ?_
  · apply AdjoinRoot.algHom_ext
    change P.lift _ hP ((AdjoinRoot.liftAlgHom P.f (Algebra.ofId R P.Ring)
      P.X P.hasMap_X.1) (AdjoinRoot.root P.f)) = AdjoinRoot.root P.f
    rw [AdjoinRoot.liftAlgHom_root, P.lift_X]
  · apply P.hom_ext
    change (AdjoinRoot.liftAlgHom P.f (Algebra.ofId R P.Ring) P.X P.hasMap_X.1)
      (P.lift _ hP P.X) = P.X
    rw [P.lift_X, AdjoinRoot.liftAlgHom_root]

theorem rootAlgebra_etale (n : ℕ) (hn : 0 < n) (hinv : IsUnit (n : R)) (a : Rˣ) :
    Algebra.Etale R (RootAlgebra R n a) :=
  Algebra.Etale.of_equiv (standardPairEquiv R n hn hinv a)

theorem rootAlgebra_injective (n : ℕ) (hn : 0 < n) (a : Rˣ) :
    Function.Injective (algebraMap R (RootAlgebra R n a)) := by
  nontriviality R
  apply AdjoinRoot.of.injective_of_monic_of_degree_pos (rootPolynomial_monic R n hn a)
  rw [rootPolynomial, degree_X_pow_sub_C hn]
  exact_mod_cast hn

/-- The actual global-unit root cover is the polynomial spectrum after base change. -/
def scheme (X : Scheme.{u}) (n : ℕ) (a : Γ(X, ⊤)ˣ) : Over X :=
  Over.mk (pullback.fst X.toSpecΓ
    (Spec.map (CommRingCat.ofHom (algebraMap Γ(X, ⊤) (RootAlgebra Γ(X, ⊤) n a)))))

instance scheme_finite (X : Scheme.{u}) (n : ℕ) [NeZero n] (a : Γ(X, ⊤)ˣ) :
    IsFinite (scheme X n a).hom := by
  have : IsFinite (Spec.map (CommRingCat.ofHom
      (algebraMap Γ(X, ⊤) (RootAlgebra Γ(X, ⊤) n a)))) := by
    rw [IsFinite.SpecMap_iff]
    change (algebraMap Γ(X, ⊤) (RootAlgebra Γ(X, ⊤) n a)).Finite
    rw [RingHom.finite_algebraMap]
    infer_instance
  exact inferInstanceAs (IsFinite (pullback.fst _ _))

theorem scheme_etale (X : Scheme.{u}) (n : ℕ) (hn : 0 < n)
    (hinv : IsUnit (n : Γ(X, ⊤))) (a : Γ(X, ⊤)ˣ) : Etale (scheme X n a).hom := by
  have : Algebra.Etale Γ(X, ⊤) (RootAlgebra Γ(X, ⊤) n a) := rootAlgebra_etale _ n hn hinv a
  have : Etale (Spec.map (CommRingCat.ofHom
      (algebraMap Γ(X, ⊤) (RootAlgebra Γ(X, ⊤) n a)))) := by
    rw [HasRingHomProperty.Spec_iff (P := @Etale)]
    change (algebraMap Γ(X, ⊤) (RootAlgebra Γ(X, ⊤) n a)).Etale
    rw [RingHom.etale_algebraMap]
    infer_instance
  exact inferInstanceAs (Etale (pullback.fst _ _))

instance scheme_surjective (X : Scheme.{u}) (n : ℕ) [NeZero n] (a : Γ(X, ⊤)ˣ) :
    Surjective (scheme X n a).hom := by
  have hfin : (algebraMap Γ(X, ⊤) (RootAlgebra Γ(X, ⊤) n a)).Finite := by
    rw [RingHom.finite_algebraMap]
    infer_instance
  have : Surjective (Spec.map (CommRingCat.ofHom
      (algebraMap Γ(X, ⊤) (RootAlgebra Γ(X, ⊤) n a)))) :=
    ⟨hfin.to_isIntegral.comap_surjective (rootAlgebra_injective _ n (Nat.pos_of_ne_zero (NeZero.ne
      n)) a)⟩
  exact inferInstanceAs (Surjective (pullback.fst _ _))


variable {R} in
/-- Ring maps of the actual quotient, with constants fixed, are precisely unit roots. -/
def ringHomEquiv (S : Type u) [CommRing S] (i : R →+* S) (n : ℕ) [NeZero n] (a : Rˣ) :
    {h : RootAlgebra R n a →+* S // h.comp (algebraMap R _) = i} ≃
      {b : Sˣ // b ^ n = Units.map i.toMonoidHom a} where
  toFun h := ⟨Units.map h.val.toMonoidHom (rootUnit R n a), by
    apply Units.ext
    change (h.val (rootUnit R n a)) ^ n = i a
    rw [rootUnit_val, ← map_pow, root_pow]
    exact congrArg (fun k : R →+* S => k a) h.property⟩
  invFun b := ⟨AdjoinRoot.lift i (b.val : S) (by
    simp only [rootPolynomial, eval₂_sub, eval₂_pow, eval₂_X, eval₂_C, sub_eq_zero]
    exact congrArg Units.val b.property),
    AdjoinRoot.lift_comp_of _⟩
  left_inv h := by
    apply Subtype.ext
    apply AdjoinRoot.ringHom_ext
    · dsimp
      rw [AdjoinRoot.lift_comp_of]
      exact h.property.symm
    · simp
  right_inv b := by
    apply Subtype.ext
    apply Units.ext
    simp

variable {R}

def unitRestriction (X : Scheme.{u}) (a : Γ(X, ⊤)ˣ) (U : Over X) : Γ(U.left, ⊤)ˣ :=
  Units.map U.hom.appTop.hom.toMonoidHom a

/-- The literal positive-root solutions on any test scheme over X. -/
abbrev RootSections (X : Scheme.{u}) (n : ℕ) (a : Γ(X, ⊤)ˣ) (U : Over X) :=
  {b : Γ(U.left, ⊤)ˣ // b ^ n = unitRestriction X a U}

def homEquiv (X : Scheme.{u}) (n : ℕ) (a : Γ(X, ⊤)ˣ) (U : Over X) :
    (U ⟶ scheme X n a) ≃
      {g : U.left ⟶ Spec (.of (RootAlgebra Γ(X, ⊤) n a)) //
        g ≫ Spec.map (CommRingCat.ofHom (algebraMap Γ(X, ⊤) _)) = U.hom ≫ X.toSpecΓ} where
  toFun h := ⟨h.left ≫ pullback.snd _ _, by
    rw [Category.assoc, ← pullback.condition, ← Category.assoc]
    exact congrArg (fun k => k ≫ X.toSpecΓ) h.w⟩
  invFun g := Over.homMk (pullback.lift U.hom g.val g.property.symm) (by simp [scheme])
  left_inv h := by
    apply Over.OverMorphism.ext
    apply pullback.hom_ext
    · simpa [scheme] using h.w.symm
    · simp
  right_inv g := by apply Subtype.ext; simp

def homRingEquiv (X : Scheme.{u}) (n : ℕ) (a : Γ(X, ⊤)ˣ) (U : Over X) :
    (U ⟶ scheme X n a) ≃
      {h : RootAlgebra Γ(X, ⊤) n a →+* Γ(U.left, ⊤) //
        h.comp (algebraMap Γ(X, ⊤) _) = U.hom.appTop.hom} :=
  (homEquiv X n a U).trans
    ((RootsFiniteEtale.schemeHomRingEquiv U.left (RootAlgebra Γ(X, ⊤) n a)).subtypeEquiv (fun g =>
      by
      rw [← (RootsFiniteEtale.schemeHomRingEquiv U.left Γ(X, ⊤)).injective.eq_iff,
        RootsFiniteEtale.schemeHomRingEquiv_spec, RootsFiniteEtale.schemeHomRingEquiv_comp,
        RootsFiniteEtale.schemeHomRingEquiv_toSpecΓ, RingHom.comp_id]))

/-- All-test representation of the actual polynomial cover by positive unit roots. -/
def sectionsEquiv (X : Scheme.{u}) (n : ℕ) [NeZero n] (a : Γ(X, ⊤)ˣ) (U : Over X) :
    (U ⟶ scheme X n a) ≃ RootSections X n a U :=
  (homRingEquiv X n a U).trans (ringHomEquiv _ U.hom.appTop.hom n a)

theorem sectionsEquiv_val (X : Scheme.{u}) (n : ℕ) [NeZero n] (a : Γ(X, ⊤)ˣ) (U : Over X)
    (h : U ⟶ scheme X n a) :
    (sectionsEquiv X n a U h).val =
      Units.map (RootsFiniteEtale.schemeHomRingEquiv U.left (RootAlgebra Γ(X, ⊤) n a)
        (h.left ≫ pullback.snd _ _)).toMonoidHom (rootUnit Γ(X, ⊤) n a) := rfl

/-- Restriction is the literal pullback of invertible global functions. -/
theorem sectionsEquiv_naturality (X : Scheme.{u}) (n : ℕ) [NeZero n] (a : Γ(X, ⊤)ˣ)
    {U V : Over X} (h : U ⟶ V) (t : V ⟶ scheme X n a) :
    (sectionsEquiv X n a U (h ≫ t)).val =
      Units.map h.left.appTop.hom.toMonoidHom (sectionsEquiv X n a V t).val := by
  apply Units.ext
  simp only [sectionsEquiv_val, Units.coe_map, Over.comp_left, Category.assoc,
    RootsFiniteEtale.schemeHomRingEquiv_comp]
  rfl

/-- The cover has a canonical global root, obtained from its identity section. -/
def universalRoot (X : Scheme.{u}) (n : ℕ) [NeZero n] (a : Γ(X, ⊤)ˣ) :
    Γ((scheme X n a).left, ⊤)ˣ := (sectionsEquiv X n a _ (𝟙 _)).val

theorem universalRoot_pow (X : Scheme.{u}) (n : ℕ) [NeZero n] (a : Γ(X, ⊤)ˣ) :
    universalRoot X n a ^ n = Units.map (scheme X n a).hom.appTop.hom.toMonoidHom a :=
  (sectionsEquiv X n a _ (𝟙 _)).property


abbrev mu (X : Scheme.{u}) (n : ℕ) : Over X := (MultiplicativeGroup.rootsGroupScheme X n).X

theorem rootsVal_naturality (X : Scheme.{u}) (n : ℕ) {U V : Over X}
    (h : U ⟶ V) (z : V ⟶ mu X n) :
    (MultiplicativeGroup.rootsHomEquiv X n U (h ≫ z)).val =
      Units.map h.left.appTop.hom.toMonoidHom (MultiplicativeGroup.rootsHomEquiv X n V z).val :=
  congrArg Subtype.val ((MultiplicativeGroup.rootsRepresentable X n).homEquiv_comp h z)

theorem rootsVal_one (X : Scheme.{u}) (n : ℕ) (U : Over X) :
    (MultiplicativeGroup.rootsHomEquiv X n U (1 : U ⟶ mu X n)).val = 1 :=
  congrArg Subtype.val ((MultiplicativeBaseChange.rootsSectionsEquiv X n U).map_one)

theorem rootsVal_mul (X : Scheme.{u}) (n : ℕ) (U : Over X) (z w : U ⟶ mu X n) :
    (MultiplicativeGroup.rootsHomEquiv X n U (z * w)).val =
      (MultiplicativeGroup.rootsHomEquiv X n U z).val *
        (MultiplicativeGroup.rootsHomEquiv X n U w).val :=
  congrArg Subtype.val ((MultiplicativeBaseChange.rootsSectionsEquiv X n U).map_mul z w)

/-- The actual μ_n action morphism, with the positive-root multiplication convention. -/
def action (X : Scheme.{u}) (n : ℕ) [NeZero n] (a : Γ(X, ⊤)ˣ) :
    mu X n ⊗ scheme X n a ⟶ scheme X n a :=
  (sectionsEquiv X n a (mu X n ⊗ scheme X n a)).symm
    ⟨(MultiplicativeGroup.rootsHomEquiv X n (mu X n ⊗ scheme X n a) (fst (mu X n) (scheme X n
      a))).val *
      (sectionsEquiv X n a (mu X n ⊗ scheme X n a) (snd (mu X n) (scheme X n a))).val, by
      rw [mul_pow, (MultiplicativeGroup.rootsHomEquiv X n (mu X n ⊗ scheme X n a) (fst (mu X n)
        (scheme X n a))).property,
        (sectionsEquiv X n a (mu X n ⊗ scheme X n a) (snd (mu X n) (scheme X n a))).property,
          _root_.one_mul]⟩

theorem action_coordinate (X : Scheme.{u}) (n : ℕ) [NeZero n] (a : Γ(X, ⊤)ˣ) :
    (sectionsEquiv X n a (mu X n ⊗ scheme X n a) (action X n a)).val =
      (MultiplicativeGroup.rootsHomEquiv X n (mu X n ⊗ scheme X n a) (fst (mu X n) (scheme X n
        a))).val *
        (sectionsEquiv X n a (mu X n ⊗ scheme X n a) (snd (mu X n) (scheme X n a))).val :=
  congrArg Subtype.val ((sectionsEquiv X n a (mu X n ⊗ scheme X n a)).apply_symm_apply _)

theorem action_comp (X : Scheme.{u}) (n : ℕ) [NeZero n] (a : Γ(X, ⊤)ˣ)
    (U : Over X) (h : U ⟶ mu X n ⊗ scheme X n a) :
    (sectionsEquiv X n a U (h ≫ action X n a)).val =
      (MultiplicativeGroup.rootsHomEquiv X n U (h ≫ fst _ _)).val *
        (sectionsEquiv X n a U (h ≫ snd _ _)).val := by
  rw [sectionsEquiv_naturality, action_coordinate, map_mul,
    ← rootsVal_naturality, ← sectionsEquiv_naturality]

/-- On every test scheme the action is literal multiplication by the unit root of unity. -/
theorem action_sections (X : Scheme.{u}) (n : ℕ) [NeZero n] (a : Γ(X, ⊤)ˣ)
    (U : Over X) (z : U ⟶ mu X n) (p : U ⟶ scheme X n a) :
    (sectionsEquiv X n a U (lift z p ≫ action X n a)).val =
      (MultiplicativeGroup.rootsHomEquiv X n U z).val * (sectionsEquiv X n a U p).val := by
  have h := action_comp X n a U (lift z p)
  rw [lift_fst z p, lift_snd z p] at h
  exact h

theorem action_one (X : Scheme.{u}) (n : ℕ) [NeZero n] (a : Γ(X, ⊤)ˣ)
    (U : Over X) (p : U ⟶ scheme X n a) :
    lift (1 : U ⟶ mu X n) p ≫ action X n a = p := by
  apply (sectionsEquiv X n a U).injective
  apply Subtype.ext
  rw [action_sections, rootsVal_one, _root_.one_mul]

theorem action_mul (X : Scheme.{u}) (n : ℕ) [NeZero n] (a : Γ(X, ⊤)ˣ)
    (U : Over X) (z w : U ⟶ mu X n) (p : U ⟶ scheme X n a) :
    lift (z * w) p ≫ action X n a = lift z (lift w p ≫ action X n a) ≫ action X n a := by
  apply (sectionsEquiv X n a U).injective
  apply Subtype.ext
  rw [action_sections, action_sections, action_sections, rootsVal_mul, _root_.mul_assoc]

/-- The actual transport morphism from a root p to a root q has coordinate q/p. -/
def transport (X : Scheme.{u}) (n : ℕ) [NeZero n] (a : Γ(X, ⊤)ˣ) :
    scheme X n a ⊗ scheme X n a ⟶ mu X n :=
  (MultiplicativeGroup.rootsHomEquiv X n _).symm
    ⟨(sectionsEquiv X n a _ (snd _ _)).val / (sectionsEquiv X n a _ (fst _ _)).val, by
      change _ ^ n = 1
      rw [div_pow, (sectionsEquiv X n a _ (snd _ _)).property,
        (sectionsEquiv X n a _ (fst _ _)).property, div_self']⟩

theorem transport_coordinate (X : Scheme.{u}) (n : ℕ) [NeZero n] (a : Γ(X, ⊤)ˣ) :
    (MultiplicativeGroup.rootsHomEquiv X n _ (transport X n a)).val =
      (sectionsEquiv X n a _ (snd _ _)).val / (sectionsEquiv X n a _ (fst _ _)).val :=
  congrArg Subtype.val ((MultiplicativeGroup.rootsHomEquiv X n _).apply_symm_apply _)

/-- Positive transport agrees literally with q/p on every test scheme. -/
theorem transport_sections (X : Scheme.{u}) (n : ℕ) [NeZero n] (a : Γ(X, ⊤)ˣ)
    (U : Over X) (p q : U ⟶ scheme X n a) :
    (MultiplicativeGroup.rootsHomEquiv X n U (lift p q ≫ transport X n a)).val =
      (sectionsEquiv X n a U q).val / (sectionsEquiv X n a U p).val := by
  rw [rootsVal_naturality, transport_coordinate, _root_.map_div,
    ← sectionsEquiv_naturality, ← sectionsEquiv_naturality]
  simp

theorem action_transport (X : Scheme.{u}) (n : ℕ) [NeZero n] (a : Γ(X, ⊤)ˣ)
    (U : Over X) (p q : U ⟶ scheme X n a) :
    lift (lift p q ≫ transport X n a) p ≫ action X n a = q := by
  apply (sectionsEquiv X n a U).injective
  apply Subtype.ext
  rw [action_sections, transport_sections, div_mul_cancel]

theorem transport_action (X : Scheme.{u}) (n : ℕ) [NeZero n] (a : Γ(X, ⊤)ˣ)
    (U : Over X) (z : U ⟶ mu X n) (p : U ⟶ scheme X n a) :
    lift p (lift z p ≫ action X n a) ≫ transport X n a = z := by
  apply (MultiplicativeGroup.rootsHomEquiv X n U).injective
  apply Subtype.ext
  rw [transport_sections, action_sections, mul_div_cancel_right]

/-- The actual scheme map `(z,p) ↦ (p,z*p)` is an isomorphism, with inverse `(p,q) ↦ (q/p,p)`. -/
def actionPairIso (X : Scheme.{u}) (n : ℕ) [NeZero n] (a : Γ(X, ⊤)ˣ) :
    mu X n ⊗ scheme X n a ≅ scheme X n a ⊗ scheme X n a where
  hom := lift (snd _ _) (action X n a)
  inv := lift (transport X n a) (fst _ _)
  hom_inv_id := by
    apply CartesianMonoidalCategory.hom_ext
    · simp only [Category.assoc, lift_fst, Category.id_comp]
      have h := transport_action X n a _ (fst (mu X n) (scheme X n a)) (snd _ _)
      simpa using h
    · simp
  inv_hom_id := by
    apply CartesianMonoidalCategory.hom_ext
    · simp
    · simp only [Category.assoc, lift_snd, Category.id_comp]
      have h := action_transport X n a _ (fst (scheme X n a) (scheme X n a)) (snd _ _)
      simpa using h


/-- The actual finite étale root cover at positive invertible level. -/
def cover (X : Scheme.{u}) (n : ℕ) (hn : 0 < n)
    (hinv : IsUnit (n : Γ(X, ⊤))) (a : Γ(X, ⊤)ˣ) : _root_.AlgebraicGeometry.Scheme.FiniteEtale X :=
  let : NeZero n := ⟨hn.ne'⟩
  ⟨scheme X n a, ⟨inferInstance, scheme_etale X n hn hinv a⟩⟩

theorem cover_surjective (X : Scheme.{u}) (n : ℕ) (hn : 0 < n)
    (hinv : IsUnit (n : Γ(X, ⊤))) (a : Γ(X, ⊤)ˣ) :
    Surjective (cover X n hn hinv a).obj.hom := by
  let : NeZero n := ⟨hn.ne'⟩
  exact scheme_surjective X n a

/-- The natural, genuine μ_n torsor action on the constructed scheme. -/
def torsorAction (X : Scheme.{u}) (n : ℕ) [NeZero n] (a : Γ(X, ⊤)ˣ) :
    _root_.CategoryTheory.TorsorAction (MultiplicativeGroup.rootsGroupScheme X n) (toUnit (scheme X
      n a)) where
  act z p := lift z p ≫ action X n a
  naturality h z p := by simp [← Category.assoc]
  one_act p := action_one X n a _ p
  mul_act z w p := action_mul X n a _ z w p
  over z p := toUnit_unique _ _
  transport p q _ := by
    refine ⟨lift p q ≫ transport X n a, action_transport X n a _ p q, ?_⟩
    intro z hz
    have h := transport_action X n a _ z p
    rw [hz] at h
    exact h.symm

/-- This torsor record's represented action is the already constructed scheme action. -/
theorem torsorAction_actionMap (X : Scheme.{u}) (n : ℕ) [NeZero n] (a : Γ(X, ⊤)ˣ) :
    (torsorAction X n a).actionMap = action X n a := by
  change lift (fst _ _) (snd _ _) ≫ action X n a = _
  simp

/-- Literal positive action, suitable for comparing with the sheaf root torsor. -/
theorem torsorAction_sections (X : Scheme.{u}) (n : ℕ) [NeZero n] (a : Γ(X, ⊤)ˣ)
    (U : Over X) (z : U ⟶ mu X n) (p : U ⟶ scheme X n a) :
    (sectionsEquiv X n a U ((torsorAction X n a).act z p)).val =
      (MultiplicativeGroup.rootsHomEquiv X n U z).val * (sectionsEquiv X n a U p).val :=
  action_sections X n a U z p

/-- The torsor marking uses positive transport q/p. -/
theorem torsorAction_transport_ratio (X : Scheme.{u}) (n : ℕ) [NeZero n] (a : Γ(X, ⊤)ˣ)
    (U : Over X) (z : U ⟶ mu X n) (p q : U ⟶ scheme X n a)
    (hz : (torsorAction X n a).act z p = q) :
    (MultiplicativeGroup.rootsHomEquiv X n U z).val =
      (sectionsEquiv X n a U q).val / (sectionsEquiv X n a U p).val := by
  apply (eq_div_iff_mul_eq').mpr
  exact (torsorAction_sections X n a U z p).symm.trans
    (congrArg (fun t => (sectionsEquiv X n a U t).val) hz)

/-- The torsor marking on the exact finite-étale cover object consumed by A. -/
def coverTorsorAction (X : Scheme.{u}) (n : ℕ) (hn : 0 < n)
    (hinv : IsUnit (n : Γ(X, ⊤))) (a : Γ(X, ⊤)ˣ) :
    _root_.CategoryTheory.TorsorAction (MultiplicativeGroup.rootsGroupScheme X n)
      (toUnit (cover X n hn hinv a).obj) :=
  let : NeZero n := ⟨hn.ne'⟩
  torsorAction X n a

/-- A literal root exists on this actual surjective étale covering scheme. -/
theorem cover_hasRoot (X : Scheme.{u}) (n : ℕ) (hn : 0 < n)
    (hinv : IsUnit (n : Γ(X, ⊤))) (a : Γ(X, ⊤)ˣ) :
    ∃ b : Γ((cover X n hn hinv a).obj.left, ⊤)ˣ,
      b ^ n = Units.map (cover X n hn hinv a).obj.hom.appTop.hom.toMonoidHom a := by
  let : NeZero n := ⟨hn.ne'⟩
  exact ⟨universalRoot X n a, universalRoot_pow X n a⟩

end AlgebraicGeometry.Scheme.Group.RootCover
