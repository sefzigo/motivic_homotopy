import Mathlib.Analysis.RCLike.Basic
import Mathlib.Order.CompletePartialOrder
import Mathlib.Data.Quot
import Mathlib.Logic.Function.Basic
import Mathlib.Data.Set.Countable
import Batteries.Data.Rat.Basic
import Mathlib.Data.Rat.Cast.Order
import Mathlib.Order.Basic
import Mathlib.Topology.Algebra.InfiniteSum.ENNReal
import Mathlib.Data.Finite.Defs
import Mathlib.Algebra.Order.Group.OrderIso

--import Mathlib.Topology.Instances.ENNReal.Lemmas

open Set Filter Real Function Rat Classical ENNReal Group
noncomputable section

structure naiveMeasure where
  μ : Set ℝ → ENNReal
  monotone {A B : Set ℝ} (h : A ⊆ B) : μ A ≤ μ B
  translation_invariance {A : Set ℝ} {x : ℝ} : μ ((fun a ↦ a + x)''A) = μ A
  normalised {l : ℝ} : μ (Icc 0 l) = ENNReal.ofReal l
  sigma_additivity (α : Type)[Countable α] {A : α → Set ℝ} (h : Pairwise (Disjoint on A)):
   μ (⋃ n : α , A n) = ∑' n : α , μ (A n)

instance : CoeFun naiveMeasure (λ _ => Set ℝ → ENNReal) where
  coe := naiveMeasure.μ

def I : Set ℝ := Icc 0 1
def S : Set ℝ := Icc (-1) 1
def J : Set ℝ := Icc (-1) 2
def K : Set ℝ := Icc 0 3
def shiftRange := { x : ℚ | x ∈ Icc (-1) 1}



instance : Countable shiftRange := by
  have h : (shiftRange ⊆ univ) := by exact fun ⦃a⦄ a ↦ trivial
  let f : ℤ × ℤ  → ℚ := fun (n,m) => n/m
  refine Set.Countable.mono h ?_
  have : range f = univ := by
    ext x; simp
    use x.num, x.den
    unfold f; simp
    exact num_div_den x
  rw[← this]
  refine Set.countable_range f

instance : Infinite shiftRange := by
let f : ℕ → shiftRange := fun n =>  ⟨ 1/(n+1) , ?_⟩
· refine Infinite.of_injective f ?_
  intro x y
  simp [f]
simp_all [shiftRange]
norm_cast
have : (0 : ℚ) < ((n + 1):ℚ)⁻¹ := by
  apply inv_pos.mpr
  exact Nat.cast_add_one_pos n
have : (-1 : ℚ) ≤ ((n + 1): ℚ)⁻¹ := by
  linarith
constructor
· norm_cast at this;
exact Nat.cast_inv_le_one (n+1)


instance equiv : Setoid ℝ  where
  r := fun x y ↦ (x - y) ∈ range (Rat.cast)
  iseqv := {
    refl := by
      intro x
      use 0
      simp

    symm := by
      rintro x y ⟨q, hxy⟩
      use (-q)
      have h₁ : y - x = -(x- y) := by ring
      rw [h₁, ← hxy]
      norm_cast

    trans := by
      rintro x y z ⟨q₁, hxy⟩ ⟨q₂, hyz⟩
      use q₁ + q₂
      simp at hxy hyz ⊢
      rw [hxy, hyz]
      simp
  }


instance equiv' : Setoid I := inferInstance

def vitaliSet : Set ℝ  := {x : ℝ | ∃y : Quotient equiv', x = Quotient.out y}

def vitaliSet' (j : ℝ) : Set ℝ := (fun x ↦ x + j)'' vitaliSet

def trans_vitaliSet (j : shiftRange) : Set ℝ := (fun x ↦ x + j)'' vitaliSet

def vitaliUnion : Set ℝ := ⋃ i : shiftRange , trans_vitaliSet i


lemma vitali_mem_eq_off_rat_diff {x y : ℝ} (hx : x ∈ vitaliSet) (hy : y ∈ vitaliSet)(h : x - y ∈ range ((↑) : ℚ → ℝ)) : x = y := by
  have heq : x ≈ y := h
  obtain ⟨x', hx'⟩ := hx; obtain ⟨y', hy'⟩ := hy
  rw[hx',hy']
  rw[hx', hy'] at heq
  refine Subtype.eq_iff.mp ?_
  simp [Quotient.out_eq,← Quotient.out_equiv_out]
  exact heq

lemma translates_disjoint : Pairwise (Disjoint on trans_vitaliSet) := by
  intro i j h U hUi hUj x hUx
  simp_all only [le_eq_subset, bot_eq_empty, mem_empty_iff_false]
  have hxi : x ∈ trans_vitaliSet i:= hUi  hUx
  have hxj : x ∈ trans_vitaliSet j:= hUj  hUx
  simp [trans_vitaliSet] at hxi hxj
  have : x + -↑i = x + -↑j := by
    refine vitali_mem_eq_off_rat_diff hxi hxj ?_
    use (-i + j); simp
  simp_all [ne_eq, _root_.add_right_inj, neg_inj, Rat.cast_inj] ;aesop

lemma vit_sub_I : vitaliSet ⊆ I := by
  rintro x ⟨t, ht⟩
  simp_all only [Subtype.coe_prop]

lemma vit_trans_measure {μ : naiveMeasure} {r : shiftRange} :  μ vitaliSet = μ (trans_vitaliSet r) := by
  unfold trans_vitaliSet
  symm
  apply μ.translation_invariance

lemma I_sub_vitUn : I ⊆ vitaliUnion := by
  intro x  hx
  --define delta and show that it is in shiftRange
  let δ := x - Quotient.out (Quotient.mk equiv' ⟨ x, hx⟩)
  have : equiv'  (Quotient.out (Quotient.mk equiv' ⟨ x, hx⟩)) ⟨ x, hx⟩ := by exact Quotient.eq_mk_iff_out.mp rfl
  set y  :=  Quotient.out (Quotient.mk equiv' ⟨ x, hx⟩ ) with y_def
  have ⟨d, d2⟩ : δ ∈ range Rat.cast := equiv'.symm this
  have dI : d ∈ shiftRange := by
    unfold I at *;simp_all [shiftRange]
    rw[← y_def] at d2
    obtain ⟨y, hy⟩ := y
    simp [mem_Icc] at hx hy
    constructor
    · have : (d: ℝ) ≥ -1 := by linarith
      apply ge_iff_le.1 at this
      norm_cast at this
    have : (d: ℝ) ≤ 1 := by linarith
    norm_cast at this
  --actual proof
  simp_all [vitaliUnion]
  use d
  simp[trans_vitaliSet]
  constructor
  · exact dI
  simp[d2, vitaliSet]
  exact Exists.intro ⟦⟨x, hx⟩⟧ rfl

lemma vitUn_sub_J : vitaliUnion ⊆ J := by
  let I_i (i : shiftRange) : Set ℝ := (fun x ↦ x + i)'' I
  let V :=  ⋃ i : shiftRange, I_i i
  have h0: Rat.cast '' shiftRange ⊆ S := by
    intro x
    simp[J, shiftRange]
    intro _ _ _ h
    rw[← h]
    constructor <;> norm_cast
  have h : vitaliUnion ⊆ V := by
    rintro x ⟨ i0, ⟨ ⟨ ⟨a,b⟩, hval ⟩, hxi0⟩ ⟩
    have : i0 ⊆ I_i ⟨ a,b⟩ := by
      simp [← hval, trans_vitaliSet, I_i]
      intro x hx
      exact vit_sub_I hx
    have ha : I_i ⟨ a,b⟩ ⊆ V := by
      intro x
      simp [I_i, V]; intro h
      use a
    exact ha (this hxi0)
  have h2 : V ⊆ J := by
    rintro x ⟨i0 , ⟨ ⟨a, ha⟩, hxi0⟩⟩
    --obtain ⟨a, ha⟩ := hxi.1
    have : i0 ⊆ J := by
      rw[← ha]
      intro y ⟨z, hz⟩
      unfold J; unfold I at hz
      simp_all only [image_subset_iff, mem_range, Subtype.exists, mem_Icc]
      repeat rw[← hz.2]
      have : ↑ a ∈ S := mem_preimage.mp (h0 (Subtype.coe_prop a))
      unfold S at this
      simp [mem_Icc] at this
      constructor <;> linarith
    exact this hxi0
  intro x hx
  exact h2 (h hx)

lemma J_measure (μ : naiveMeasure) : μ J = ENNReal.ofReal 3 := by
  have eqJ (μ : naiveMeasure) : μ J = μ K := by
    have h_translate : K = (fun a ↦ a + 1)''J := by
      ext x
      simp [J, K]
      intro h
      constructor
      · intro h'; linarith
      intro h'';linarith
    rw [h_translate]
    exact Eq.symm μ.translation_invariance
  rw[eqJ]
  exact μ.normalised

theorem vitali (μ : naiveMeasure) (t : ENNReal): μ vitaliSet = t → False := by
  by_contra h
  by_cases h0 : t = 0
  · have : ENNReal.ofReal 1 ≤  0 :=
    calc
        ENNReal.ofReal 1 = μ I := by symm; apply μ.normalised
        _ ≤ μ vitaliUnion := by apply μ.monotone (I_sub_vitUn)
        _ = ∑' i : shiftRange , μ ( trans_vitaliSet i ):= by
            unfold vitaliUnion; exact μ.sigma_additivity shiftRange translates_disjoint
        _ = ∑' i : shiftRange , 0 := by
            refine tsum_congr ?_
            intro b
            rw [← vit_trans_measure, h, h0]
        _ = 0 := by simp
    aesop

  have : μ (vitaliUnion) ≤ ENNReal.ofReal 3 := by
    rw[← J_measure μ ]; exact μ.monotone vitUn_sub_J

  have : μ (vitaliUnion) = ∞ :=
  calc
         μ (vitaliUnion) = ∑' i : shiftRange , μ ( trans_vitaliSet i ) := by
            unfold vitaliUnion; exact μ.sigma_additivity shiftRange translates_disjoint
        _ = ∑' i : shiftRange , t := by
            refine tsum_congr ?_
            intro b
            rw [← vit_trans_measure, h]
        _ = ∞ := by
            exact ENNReal.tsum_const_eq_top_of_ne_zero h0

  aesop

end
