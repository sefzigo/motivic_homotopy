import Mathlib.Analysis.RCLike.Basic
import Mathlib.Order.CompletePartialOrder
import Mathlib.Data.Quot
import Mathlib.Logic.Function.Basic
import Mathlib.Data.Set.Countable
import Batteries.Data.Rat.Basic
--set_option warningAsError false

open Set Filter Real Function Rat Classical ENNReal
noncomputable section

structure naiveMeasure where
  μ : Set ℝ → ENNReal
  monotony {A B : Set ℝ} (h : A ⊆ B) : μ A ≤ μ B
  translation_invariance {A : Set ℝ} {x : ℝ} : μ ((fun a ↦ a + x)''A) = μ A
  normalised {l : ℝ} : μ (Icc 0 l) = ENNReal.ofReal l
  sigma_additivity (α : Type)[Countable α] {A : α → Set ℝ} (h : Pairwise (Disjoint on A)): μ (⋃ n : α , A n) = ∑' n : α , μ (A n)

instance : CoeFun naiveMeasure (λ _ => Set ℝ → ENNReal) where
  coe := naiveMeasure.μ

def I : Set ℝ := Icc 0 1
def J : Set ℝ := Icc (-1) 2
def J' : Set ℝ := Icc 0 3
def shiftRange := { x : ℚ | x ∈ Icc (-1) 1}


instance : Countable shiftRange := by
have h : (shiftRange ⊆ univ) := by exact fun ⦃a⦄ a ↦ trivial
refine Set.Countable.mono h ?_

let f : ℤ × ℤ  → ℚ := fun (n,m) => n/m

have : range f = univ := by
  ext x
  simp
  use x.num, x.den
  unfold f
  simp
  exact num_div_den x

rw[← this]
refine Set.countable_range f



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
      rw [h₁]
      rw [← hxy]
      norm_cast

    trans := by
      rintro x y z ⟨q₁, hxy⟩ ⟨q₂, hyz⟩
      use q₁ + q₂
      simp at hxy hyz ⊢
      rw [hxy]
      rw [hyz]
      simp
  }


instance equiv' : Setoid I := inferInstance

def vitaliSet : Set ℝ  := {x : ℝ | ∃y : Quotient equiv', x = Quotient.out y}

def vitaliSet' (j : ℝ) : Set ℝ := (fun x ↦ x + j)'' vitaliSet

def trans_vitaliSet (j : shiftRange) : Set ℝ := (fun x ↦ x + j)'' vitaliSet

def vitaliUnion : Set ℝ := ⋃ i : shiftRange , trans_vitaliSet i


lemma vitali_sub_I : vitaliSet ⊆ I := by
  intro x hv
  obtain ⟨y, h1,h2⟩ := hv
  simp_all only [Subtype.coe_prop]


lemma vitali_mem_eq_off_rat_diff {x y : ℝ} (hx : x ∈ vitaliSet) (hy : y ∈ vitaliSet)(h : x - y ∈ range ((↑) : ℚ → ℝ)) : x = y := by

have heq : x ≈ y := h

obtain ⟨x', hx'⟩ := hx
obtain ⟨y', hy'⟩ := hy

rw[hx',hy']

rw[hx', hy'] at heq

refine Subtype.eq_iff.mp ?_
simp [Quotient.out_eq]
simp [← Quotient.out_equiv_out]
exact heq

-- {j k : ℕ} (h : j≠k) : vitaliSet' j ∩ vitaliSet' k = ∅
lemma translates_disjoint : Pairwise (Disjoint on trans_vitaliSet) := by
  intro i j h
  intro U hUi hUj
  intro x hUx
  simp_all only [le_eq_subset, bot_eq_empty, mem_empty_iff_false]
  have hxi : x ∈ trans_vitaliSet i:= hUi  hUx
  have hxj : x ∈ trans_vitaliSet j:= hUj  hUx
  simp [trans_vitaliSet] at hxi hxj

  have : x + -↑i = x + -↑j := by
    refine vitali_mem_eq_off_rat_diff hxi hxj ?_
    simp
    use (-i + j)
    simp

  simp_all only [ne_eq, _root_.add_right_inj, neg_inj, Rat.cast_inj]
  aesop

lemma vitali_super : vitaliSet ⊆ I := by
  rintro x ⟨t, ht⟩
  simp_all only [Subtype.coe_prop]


lemma bound (μ : naiveMeasure): μ vitaliSet ≤ ENNReal.ofReal 1 := by
  have h' : μ I = ENNReal.ofReal 1 := by
    exact μ.normalised
  rw[← h']
  apply μ.monotony (vitali_super)

lemma vitaliTranslations (μ : naiveMeasure) {r : ℝ} : μ vitaliSet = μ (vitaliSet' r) := by
  unfold vitaliSet'
  symm
  apply μ.translation_invariance



lemma vitUn_measure (μ : naiveMeasure): μ vitaliUnion = ∑' r , μ (trans_vitaliSet r) := μ.sigma_additivity shiftRange translates_disjoint


lemma superset (μ : naiveMeasure) : I ⊆ vitaliUnion := by
  -- surely the smallest/biggest element of vitaliUnion is smaller/bigger (or equal to) than 0/1.
  -- the hard part is to show that for any element in I, there is an element in vitaliUnion
  sorry

lemma subset (μ : naiveMeasure) : vitaliUnion ⊆ J := by

  have : Rat.cast '' shiftRange ⊆ I := by sorry

  unfold vitaliUnion
  intro x
  simp
  intro r hr hx
  simp_all [trans_vitaliSet, J]
  have hr_le : r ≤ 1 := by sorry
  have hr_ge : -1 ≤ r := by sorry
  have hx_ge : 0 ≤ x := by sorry
  have hx_ge : x ≤ 1 := by sorry
  constructor
  · apply?



    sorry
  sorry
lemma threeJ (μ : naiveMeasure) : μ J = ENNReal.ofReal 3 := by
  have eqJ (μ : naiveMeasure) : μ J = μ J' := by
    have h_translate : J' = (fun a ↦ a + 1)''J := by
      ext x
      simp [J, J']
      intro h
      constructor
      · intro h'
        linarith
      intro h''
      linarith
    rw [h_translate]
    exact Eq.symm μ.translation_invariance
  rw[eqJ]
  exact μ.normalised


theorem vitali (μ : naiveMeasure) (t : ENNReal): μ vitaliSet = t → False := by
  by_contra h
  by_cases h₀ : t = 0

  · have contra : ENNReal.ofReal 1 ≤ 0 := by
      calc
        ENNReal.ofReal 1 = μ I := by symm; apply μ.normalised
        _ ≤ μ vitaliUnion := by apply μ.monotony (superset μ)
        _ = tsum (fun r => if r ∈ shiftRange then μ (vitaliSet' r) else 0) := by exact sigma μ
        _ = tsum (fun r => if r ∈ shiftRange then μ vitaliSet else 0) := by sorry -- vitaliTranslations
        _ = tsum (fun r => if r ∈ shiftRange then 0 else 0) := by rw [h, h₀]
        _ = 0 := by simp
    have one_pos : ENNReal.ofReal 1 > 0 := by simp
    exact absurd contra (not_le_of_gt one_pos)

  have contra' : ENNReal.ofReal 3 ≥ ⊤ := by
      calc
        ENNReal.ofReal 3 = μ J := by symm; apply threeJ
        _ ≥ μ vitaliUnion := by apply μ.monotony (subset μ)
        _ = tsum (fun r => if r ∈ shiftRange then μ (vitaliSet' r) else 0) := by exact sigma μ
        _ = tsum (fun r => if r ∈ shiftRange then μ vitaliSet else 0) := by sorry -- vitaliTranslations
        _ = tsum (fun r => if r ∈ shiftRange then t else 0) := by exact tsum_congr fun b => congrFun (congrArg (ite (b ∈ shiftRange)) h) 0
        _ = t * tsum (fun r => if r ∈ shiftRange then 1 else 0) := by hint
        _ = t * ⊤ := by apply sorry -- an infinite sum of ones is infinite
        _ = ⊤ := by exact ENNReal.mul_top h₀
  have three_finite : ENNReal.ofReal 3 < ⊤ := by simp
  exact absurd contra' (not_le_of_gt three_finite)

end

#min_imports
