/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Cohomology.Godement.Stalk.TotalMatrix

/-!
Source: `Quillen/AlgebraicGeometry/Scheme/Sheaf/GodementStalkTotalHomotopy.lean` at LOCAL Quillen
`189a8e779f0c68b2dfc6f8195daebb3e684a5905`. Selection: whole_general;
source ranges [[1, 208]]. Actual objects, maps and hypotheses are preserved.
-/

/-! # The signed contraction of the actual original Godement total on each module stalk -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open AlgebraicGeometry.Scheme.Modules

namespace AlgebraicGeometry.Scheme.Modules.Godement

/-- The actual native vertical sign squares to one on every matrix entry. -/
theorem godementStalkTotal_sign_square (X : Scheme.{u}) (x : X) (p : ℤ)
    {A B : ModuleCat.{u} (X.presheaf.stalk x)} (f : A ⟶ B) :
    (ComplexShape.up ℤ).ε p • ((ComplexShape.up ℤ).ε p • f) = f := by
  rw [← mul_smul, Int.units_mul_self, one_smul]

/-- Adjacent horizontal columns give opposite native vertical-backstep signs. -/
theorem godementStalkTotal_sign_cancel (X : Scheme.{u}) (x : X) (p : ℤ)
    {A B : ModuleCat.{u} (X.presheaf.stalk x)} (f : A ⟶ B) :
    (ComplexShape.up ℤ).ε (p + 1) • f + (ComplexShape.up ℤ).ε p • f = 0 := by
  rw [ComplexShape.ε_succ (ComplexShape.up ℤ) (show (ComplexShape.up ℤ).Rel p (p + 1) from rfl)]
  change (-((ComplexShape.up ℤ).ε p : ℤ)) • f + ((ComplexShape.up ℤ).ε p : ℤ) • f = 0
  rw [neg_smul, neg_add_cancel]

/-- A backwards matrix entry with its intermediate degree explicit. -/
def godementStalkBackEntry (X : Scheme.{u}) (x : X) (K : CochainComplex.Plus X.Modules)
    (p q r n : ℤ) (hqr : r + 1 = q) (hpn : p + r = n) :
    (godementStalkIntTerm X x q).obj (K.obj.X p) ⟶ (godementTotalStalk X x K).X n :=
  (godementStalkIntBack X x q r hqr).app (K.obj.X p) ≫
    godementStalkTotalIn X x K p r n hpn

/-- Changing a proved intermediate degree preserves the original matrix entry. -/
theorem godementStalkBackEntry_congr (X : Scheme.{u}) (x : X)
    (K : CochainComplex.Plus X.Modules) (p q r r' n : ℤ) (hr : r = r')
    (hqr : r + 1 = q) (hpn : p + r = n) (hqr' : r' + 1 = q) (hpn' : p + r' = n) :
    godementStalkBackEntry X x K p q r n hqr hpn =
      godementStalkBackEntry X x K p q r' n hqr' hpn' := by
  subst r'
  rfl

/-- A backwards/vertical matrix entry with its terminal degree explicit. -/
def godementStalkBackDEntry (X : Scheme.{u}) (x : X) (K : CochainComplex.Plus X.Modules)
    (p q r s n : ℤ) (hqr : r + 1 = q) (hpn : p + s = n) :
    (godementStalkIntTerm X x q).obj (K.obj.X p) ⟶ (godementTotalStalk X x K).X n :=
  (godementStalkIntBack X x q r hqr).app (K.obj.X p) ≫
    (godementStalkIntD X x r s).app (K.obj.X p) ≫ godementStalkTotalIn X x K p s n hpn

/-- Changing a proved terminal column degree preserves this original composite entry. -/
theorem godementStalkBackDEntry_congr (X : Scheme.{u}) (x : X)
    (K : CochainComplex.Plus X.Modules) (p q r s s' n : ℤ) (hs : s = s')
    (hqr : r + 1 = q) (hpn : p + s = n) (hpn' : p + s' = n) :
    godementStalkBackDEntry X x K p q r s n hqr hpn =
      godementStalkBackDEntry X x K p q r s' n hqr hpn' := by
  subst s'
  rfl

/-- The vertical/backwards entry with its intermediate resolution degree explicit. -/
def godementStalkDBackEntry (X : Scheme.{u}) (x : X) (K : CochainComplex.Plus X.Modules)
    (p q s r n : ℤ) (hsr : r + 1 = s) (hpn : p + r = n) :
    (godementStalkIntTerm X x q).obj (K.obj.X p) ⟶ (godementTotalStalk X x K).X n :=
  (godementStalkIntD X x q s).app (K.obj.X p) ≫
    (godementStalkIntBack X x s r hsr).app (K.obj.X p) ≫ godementStalkTotalIn X x K p r n hpn

/-- Changing this proved intermediate degree preserves the original composite matrix entry. -/
theorem godementStalkDBackEntry_congr_middle (X : Scheme.{u}) (x : X)
    (K : CochainComplex.Plus X.Modules) (p q s s' r n : ℤ) (hs : s = s')
    (hsr : r + 1 = s) (hsr' : r + 1 = s') (hpn : p + r = n) :
    godementStalkDBackEntry X x K p q s r n hsr hpn =
      godementStalkDBackEntry X x K p q s' r n hsr' hpn := by
  subst s'
  rfl

/-- Changing the proved intermediate degree preserves the backwards/vertical composite. -/
theorem godementStalkBackDEntry_congr_middle (X : Scheme.{u}) (x : X)
    (K : CochainComplex.Plus X.Modules) (p q r r' s n : ℤ) (hr : r = r')
    (hqr : r + 1 = q) (hqr' : r' + 1 = q) (hpn : p + s = n) :
    godementStalkBackDEntry X x K p q r s n hqr hpn =
      godementStalkBackDEntry X x K p q r' s n hqr' hpn := by
  subst r'
  rfl

/-- The actual signed backstep contracts the total, leaving exactly its original
zero-row projection. -/
theorem godementStalkTotal_contraction (X : Scheme.{u}) (x : X)
    (K : CochainComplex.Plus X.Modules) (n : ℤ) :
    (godementTotalStalk X x K).d n (n + 1) ≫ godementStalkTotalBack X x K (n + 1) n rfl +
      godementStalkTotalBack X x K n (n - 1) (by omega) ≫
        (godementTotalStalk X x K).d (n - 1) n +
      godementStalkTotalProjection X x K n ≫ (godementStalkTotalUnit X x K).f n = 𝟙 _ := by
  apply godementStalkTotal_hom_ext
  intro p q hpq
  by_cases hneg : q < 0
  · exact (godementStalkIntTerm_isZero_negative X x (K.obj.X p) q hneg).eq_of_src _ _
  rw [Preadditive.comp_add, Preadditive.comp_add]
  simp only [← Category.assoc, godementStalkTotalIn_d, godementStalkTotalIn_back,
    Preadditive.add_comp, Linear.units_smul_comp]
  simp only [Category.assoc]
  rw [godementStalkTotalIn_d_to _ _ _ p (q - 1) (n - 1) n
    (by omega) (by omega)]
  simp only [godementStalkTotalIn_back, Linear.comp_units_smul]
  simp only [Preadditive.comp_add, smul_add, Linear.comp_units_smul,
    godementStalkTotal_sign_square, Category.comp_id]
  rw [godementStalkHorizontal_back_assoc]
  have he₁ := godementStalkBackEntry_congr X x K p (q + 1) (q + 1 - 1) q n
    (by omega) (by omega) (by omega) rfl hpq
  have he₂ := godementStalkBackDEntry_congr X x K p q (q - 1) (q - 1 + 1) q n
    (by omega) (by omega) (by omega) hpq
  change ((ComplexShape.up ℤ).ε (p + 1) •
        ((godementStalkIntBack X x q (q - 1) (by omega)).app (K.obj.X p) ≫
          godementStalkHorizontal X x K p (q - 1) ≫
            godementStalkTotalIn X x K (p + 1) (q - 1) n (by omega)) +
      (godementStalkIntD X x q (q + 1)).app (K.obj.X p) ≫
        godementStalkBackEntry X x K p (q + 1) (q + 1 - 1) n (by omega) (by omega)) +
    ((ComplexShape.up ℤ).ε p •
        ((godementStalkIntBack X x q (q - 1) (by omega)).app (K.obj.X p) ≫
          godementStalkHorizontal X x K p (q - 1) ≫
            godementStalkTotalIn X x K (p + 1) (q - 1) n (by omega)) +
      godementStalkBackDEntry X x K p q (q - 1) (q - 1 + 1) n (by omega) (by omega)) +
    (godementStalkTotalIn X x K p q n hpq ≫ godementStalkTotalProjection X x K n) ≫
      (godementStalkTotalUnit X x K).f n = godementStalkTotalIn X x K p q n hpq
  rw [he₁, he₂]
  let z := (godementStalkIntBack X x q (q - 1) (by omega)).app (K.obj.X p) ≫
    godementStalkHorizontal X x K p (q - 1) ≫
      godementStalkTotalIn X x K (p + 1) (q - 1) n (by omega)
  have hz := godementStalkTotal_sign_cancel X x p z
  have hr : ((ComplexShape.up ℤ).ε (p + 1) • z +
      (godementStalkIntD X x q (q + 1)).app (K.obj.X p) ≫
        godementStalkBackEntry X x K p (q + 1) q n rfl hpq) +
    ((ComplexShape.up ℤ).ε p • z +
      godementStalkBackDEntry X x K p q (q - 1) q n (by omega) hpq) =
    ((ComplexShape.up ℤ).ε (p + 1) • z + (ComplexShape.up ℤ).ε p • z) +
      ((godementStalkIntD X x q (q + 1)).app (K.obj.X p) ≫
        godementStalkBackEntry X x K p (q + 1) q n rfl hpq +
          godementStalkBackDEntry X x K p q (q - 1) q n (by omega) hpq) := by abel
  rw [hr, hz, zero_add]
  dsimp only [godementStalkBackEntry, godementStalkBackDEntry]
  by_cases hq : q = 0
  · subst hq
    have hp : p = n := by omega
    subst p
    rw [godementStalkIntBack_negative X x 0 (0 - 1) (by omega) (by norm_num)]
    simp only [NatTrans.app_zero, zero_comp, add_zero]
    rw [godementStalkTotalIn_projection_zero, godementStalkTotalUnit_f]
    have hc := godementStalkIntContraction_zero X x (K.obj.X n)
    change godementStalkDBackEntry X x K n 0 (0 + 1) 0 n (by omega) hpq +
      (godementStalkIntRetraction X x).app (K.obj.X n) ≫
        (godementStalkIntGerm X x).app (K.obj.X n) ≫ godementStalkTotalIn X x K n 0 n hpq =
          godementStalkTotalIn X x K n 0 n hpq
    rw [godementStalkDBackEntry_congr_middle X x K n 0 (0 + 1) 1 0 n
      (by norm_num) (by omega) (by omega) hpq]
    simpa only [Preadditive.add_comp, Category.id_comp, Category.assoc,
      godementStalkDBackEntry] using
      congrArg (fun f => f ≫ godementStalkTotalIn X x K n 0 n hpq) hc
  · have hpos : 0 < q := by omega
    obtain ⟨k, hk⟩ : ∃ k : ℕ, (k : ℤ) + 1 = q := ⟨(q - 1).toNat, by omega⟩
    subst q
    rw [godementStalkTotalIn_projection_ne X x K p (k + 1) n hpq (by omega), zero_comp]
    rw [add_zero]
    have he := godementStalkBackDEntry_congr_middle X x K p (k + 1)
      (k + 1 - 1) k (k + 1) n (by omega) (by omega) (by omega) hpq
    change (godementStalkIntD X x (k + 1) (k + 1 + 1)).app (K.obj.X p) ≫
        (godementStalkIntBack X x (k + 1 + 1) (k + 1) (by omega)).app (K.obj.X p) ≫
          godementStalkTotalIn X x K p (k + 1) n hpq +
      godementStalkBackDEntry X x K p (k + 1) (k + 1 - 1) (k + 1) n (by omega) hpq = _
    rw [he]
    have hc := godementStalkIntContraction_succ X x (K.obj.X p) k
    have hc' := (add_comm _ _).trans hc
    simpa only [Preadditive.add_comp, Category.id_comp, Category.assoc,
      godementStalkBackDEntry] using
      congrArg (fun f => f ≫ godementStalkTotalIn X x K p (k + 1) n hpq) hc'


/-- The checked actual matrix identity is a homotopy of the original total chain maps. -/
def godementStalkTotalHomotopy (X : Scheme.{u}) (x : X) (K : CochainComplex.Plus X.Modules) :
    Homotopy (𝟙 (godementTotalStalk X x K))
      (godementStalkTotalRetraction X x K ≫ godementStalkTotalUnit X x K) where
  hom i j := if h : j + 1 = i then godementStalkTotalBack X x K i j h else 0
  zero i j h := dite_eq_right h
  comm n := by
    rw [dNext_eq _ (show (ComplexShape.up ℤ).Rel n (n + 1) from rfl),
      prevD_eq _ (show (ComplexShape.up ℤ).Rel (n - 1) n from by change n - 1 + 1 = n; omega)]
    simp only [HomologicalComplex.id_f, HomologicalComplex.comp_f,
      dite_eq_left (show n - 1 + 1 = n by omega)]
    exact (godementStalkTotal_contraction X x K n).symm

/-- The original total augmentation is an actual homotopy equivalence on every module stalk. -/
def godementStalkTotalHomotopyEquiv (X : Scheme.{u}) (x : X)
    (K : CochainComplex.Plus X.Modules) :
    HomotopyEquiv (godementSourceStalk X x K) (godementTotalStalk X x K) where
  hom := godementStalkTotalUnit X x K
  inv := godementStalkTotalRetraction X x K
  homotopyHomInvId := Homotopy.ofEq (godementStalkTotalUnit_retraction X x K)
  homotopyInvHomId := (godementStalkTotalHomotopy X x K).symm

/-- The actual original total augmentation is a quasi-isomorphism on every module stalk. -/
instance godementStalkTotalUnit_quasiIso (X : Scheme.{u}) (x : X)
    (K : CochainComplex.Plus X.Modules) : QuasiIso (godementStalkTotalUnit X x K) :=
  inferInstanceAs (QuasiIso (godementStalkTotalHomotopyEquiv X x K).hom)

end AlgebraicGeometry.Scheme.Modules.Godement
