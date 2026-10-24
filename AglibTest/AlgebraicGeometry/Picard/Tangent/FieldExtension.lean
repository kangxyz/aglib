/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Picard.Tangent.FieldExtension

/-! Focused consumer of the comparison between the test objects of `Picard/Tangent/Points` and
those of `Picard/Tangent/Comparison`, over `k` and over a field extension `K/k` viewed through
`Over.map (Spec K ⟶ Spec k)`; axiom guards. -/

@[expose] public section

noncomputable section

open CategoryTheory Opposite AlgebraicGeometry Scheme

universe w u

variable {k : Type u} [Field k] (F : (Over (Spec (.of k)))ᵒᵖ ⥤ AddCommGrpCat.{w})

/-- Over `k`, the tangent kernel of `Picard/Tangent/Points` is the kernel of
`F(closedPointOver k)`. -/
example : tangentKernel F k = (F.map (DualNumbers.closedPointOver k).op).hom.ker :=
  tangentKernel_eq_ker_closedPointOver F

/-- Over `k`, `µ_a` is `scaleOver k a`. -/
example (a : k) :
    specOverMap ((TrivSqZeroExt.map (a • LinearMap.id : k →ₗ[k] k)).restrictScalars k) =
      DualNumbers.scaleOver k a :=
  specOverMap_map_smul_id_eq_scaleOver a

/-- The comparison of the two `k`-scheme structures on `Spec k` has identity underlying morphism. -/
example : (specOverSelfIso k).hom.left = 𝟙 (Spec (.of k)) :=
  specOverSelfIso_hom_left

example : specOverMap (TrivSqZeroExt.fstHom k k k) =
    (specOverSelfIso k).hom ≫ DualNumbers.closedPointOver k :=
  specOverMap_fstHom_eq_specOverSelfIso_hom_comp_closedPointOver

variable {P : LocallyNoetherianOver (Spec (.of k))}
  (e : ((locallyNoetherianOverInclusion (Spec (.of k))).op ⋙ F ⋙
    CategoryTheory.forget AddCommGrpCat.{w}).RepresentableBy P)

/-- Over `k`, the scalar action of the tangent kernel on values is `F(scaleOver k a)`. -/
example (a : k) (t : tangentKernel F k) :
    letI := tangentKernelModule e k
    ((a • t : tangentKernel F k) : F.obj (op (specOver k (TrivSqZeroExt k k)))) =
      (F.map (DualNumbers.scaleOver k a).op).hom t :=
  coe_smul_tangentKernel_eq_map_scaleOver F e a t

/-- A map into `ker F(closedPointOver k)`, linear for `F(scaleOver k a)`, is a `k`-linear map
into the tangent kernel with the same values; it is injective if the map is. -/
example {V : Type*} [AddCommGroup V] [Module k V]
    (v : V →+ (F.map (DualNumbers.closedPointOver k).op).hom.ker)
    (hv : ∀ (a : k) (c : V), (v (a • c) : F.obj (op (Over.mk (DualNumbers.dualMap k)))) =
      (F.map (DualNumbers.scaleOver k a).op).hom (v c)) (c : V) :
    (linearMapToTangentKernel F e v hv c : F.obj (op (specOver k (TrivSqZeroExt k k)))) =
      (v c : F.obj (op (Over.mk (DualNumbers.dualMap k)))) :=
  coe_linearMapToTangentKernel_apply F e v hv c

example {V : Type*} [AddCommGroup V] [Module k V]
    (v : V →+ (F.map (DualNumbers.closedPointOver k).op).hom.ker)
    (hv : ∀ (a : k) (c : V), (v (a • c) : F.obj (op (Over.mk (DualNumbers.dualMap k)))) =
      (F.map (DualNumbers.scaleOver k a).op).hom (v c)) (hinj : Function.Injective v) :
    Function.Injective (linearMapToTangentKernel F e v hv) :=
  linearMapToTangentKernel_injective F e v hv hinj

variable (K : Type u) [Field K] [Algebra k K]

/-- Over a field extension `K/k`, the kernel for the `K`-schemes `Spec K[ε]` and `Spec K` viewed
over `Spec k` is the tangent kernel `ker(F(K[ε]) → F(K))` of `Picard/Tangent/Points`. -/
example : (F.map ((Over.map (Spec.map (CommRingCat.ofHom (algebraMap k K)))).map
      (DualNumbers.closedPointOver K)).op).hom.ker ≃+ tangentKernel F K :=
  kerClosedPointOverAddEquivTangentKernel F K

example (y : (F.map ((Over.map (Spec.map (CommRingCat.ofHom (algebraMap k K)))).map
      (DualNumbers.closedPointOver K)).op).hom.ker) :
    (kerClosedPointOverAddEquivTangentKernel F K y :
        F.obj (op (specOver k (TrivSqZeroExt K K)))) =
      (F.map (specOverDualNumberIso k K).hom.op).hom y :=
  coe_kerClosedPointOverAddEquivTangentKernel_apply F K y

/-- The scaling `scaleOver K a`, viewed over `Spec k`, goes to `F(µ_a)`. -/
example (a : K) (y : F.obj (op ((Over.map (Spec.map (CommRingCat.ofHom (algebraMap k K)))).obj
      (Over.mk (DualNumbers.dualMap K))))) :
    (F.map (specOverDualNumberIso k K).hom.op).hom
        ((F.map ((Over.map (Spec.map (CommRingCat.ofHom (algebraMap k K)))).map
          (DualNumbers.scaleOver K a)).op).hom y) =
      (F.map (specOverMap
          ((TrivSqZeroExt.map (a • LinearMap.id : K →ₗ[K] K)).restrictScalars k)).op).hom
        ((F.map (specOverDualNumberIso k K).hom.op).hom y) :=
  map_scaleOver_specOverDualNumberIso F a y

/-- Over a field extension: a map into the kernel of `G(closedPointOver K)`, followed by an
equivalence of kernels compatible with the scalings, is a `K`-linear map into the tangent kernel,
bijective if the map is. -/
example (G : (Over (Spec (.of K)))ᵒᵖ ⥤ AddCommGrpCat.{w})
    (E : (G.map (DualNumbers.closedPointOver K).op).hom.ker ≃+
      (F.map ((Over.map (Spec.map (CommRingCat.ofHom (algebraMap k K)))).map
        (DualNumbers.closedPointOver K)).op).hom.ker)
    (hE : ∀ (a : K) (y y' : (G.map (DualNumbers.closedPointOver K).op).hom.ker),
      (y' : G.obj (op (Over.mk (DualNumbers.dualMap K)))) =
          (G.map (DualNumbers.scaleOver K a).op).hom y →
        (E y' : F.obj (op ((Over.map (Spec.map (CommRingCat.ofHom (algebraMap k K)))).obj
            (Over.mk (DualNumbers.dualMap K))))) =
          (F.map ((Over.map (Spec.map (CommRingCat.ofHom (algebraMap k K)))).map
            (DualNumbers.scaleOver K a)).op).hom (E y))
    {V : Type*} [AddCommGroup V] [Module K V]
    (v : V →+ (G.map (DualNumbers.closedPointOver K).op).hom.ker)
    (hv : ∀ (a : K) (c : V), (v (a • c) : G.obj (op (Over.mk (DualNumbers.dualMap K)))) =
      (G.map (DualNumbers.scaleOver K a).op).hom (v c)) (hbij : Function.Bijective v) :
    Function.Bijective (linearMapToTangentKernelOfFieldExtension e G E hE v hv) :=
  linearMapToTangentKernelOfFieldExtension_bijective e G E hE v hv hbij

example (G : (Over (Spec (.of K)))ᵒᵖ ⥤ AddCommGrpCat.{w})
    (E : (G.map (DualNumbers.closedPointOver K).op).hom.ker ≃+
      (F.map ((Over.map (Spec.map (CommRingCat.ofHom (algebraMap k K)))).map
        (DualNumbers.closedPointOver K)).op).hom.ker)
    (hE : ∀ (a : K) (y y' : (G.map (DualNumbers.closedPointOver K).op).hom.ker),
      (y' : G.obj (op (Over.mk (DualNumbers.dualMap K)))) =
          (G.map (DualNumbers.scaleOver K a).op).hom y →
        (E y' : F.obj (op ((Over.map (Spec.map (CommRingCat.ofHom (algebraMap k K)))).obj
            (Over.mk (DualNumbers.dualMap K))))) =
          (F.map ((Over.map (Spec.map (CommRingCat.ofHom (algebraMap k K)))).map
            (DualNumbers.scaleOver K a)).op).hom (E y))
    {V : Type*} [AddCommGroup V] [Module K V]
    (v : V →+ (G.map (DualNumbers.closedPointOver K).op).hom.ker)
    (hv : ∀ (a : K) (c : V), (v (a • c) : G.obj (op (Over.mk (DualNumbers.dualMap K)))) =
      (G.map (DualNumbers.scaleOver K a).op).hom (v c)) (hbij : Function.Bijective v) :
    letI := tangentKernelModule e K
    tangentKernel F K ≃ₗ[K] V :=
  linearEquivTangentKernelOfFieldExtension e G E hE v hv hbij

/--
info: 'AlgebraicGeometry.Scheme.tangentKernel_eq_ker_closedPointOver' depends on axioms: [propext,
  Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms tangentKernel_eq_ker_closedPointOver

/--
info: 'AlgebraicGeometry.Scheme.specOverMap_map_smul_id_eq_scaleOver' depends on axioms: [propext,
  Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms specOverMap_map_smul_id_eq_scaleOver

/--
info: 'AlgebraicGeometry.Scheme.kerClosedPointOverAddEquivTangentKernel' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms kerClosedPointOverAddEquivTangentKernel

/--
info: 'AlgebraicGeometry.Scheme.map_scaleOver_specOverDualNumberIso' depends on axioms: [propext,
  Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms map_scaleOver_specOverDualNumberIso

/--
info: 'AlgebraicGeometry.Scheme.linearMapToTangentKernel' depends on axioms: [propext,
  Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms linearMapToTangentKernel

/--
info: 'AlgebraicGeometry.Scheme.linearMapToTangentKernelOfFieldExtension' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms linearMapToTangentKernelOfFieldExtension
