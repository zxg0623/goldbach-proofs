import Conjectures.Goldbach.B13BilateralVaughanReduction
import Mathlib
import PEqualNP.Outside.L_goldbach_discrete_parseval
import PEqualNP.Outside.L_goldbach_finite_fixed_chi_constant_mode
import PEqualNP.Outside.L_goldbach_finite_fixed_nonunit_mangoldt
import PEqualNP.Outside.L_goldbach_finite_phase_abel_two_ranges

section

/-!
This extends the Goldbach catalogue proof FiniteMajorBmorConditionalEnergy
(upstream Git blob 93f64a6df5db6b40d334413c6cba44b8e417216e). Its reduced
Parseval and modulus-four arguments are reused. Here the width is 140/(q n).
The early and middle prefixes cost at most 2 n/10^9 together. The extra
2 n/10^8 in the final affine envelope includes the non-unit contribution.
-/
open Finset
open scoped BigOperators Interval
open ArithmeticFunction MeasureTheory

namespace GoldbachCollarBmor

private abbrev abelTwo := PEqualNP.Outside.L_goldbach_finite_phase_abel_two_ranges
private abbrev constantMode := PEqualNP.Outside.L_goldbach_finite_fixed_chi_constant_mode
private abbrev nonunitMass := PEqualNP.Outside.L_goldbach_finite_fixed_nonunit_mangoldt

private theorem earlyCost :
    let D := fun (q a n : ℕ) => (∑ k ∈ (Finset.range (n+1)).filter (fun k => k % q=a % q), ArithmeticFunction.vonMangoldt k) - (n:ℝ)/(Nat.totient q:ℝ); let J := fun (q a l u : ℕ) (β : ℝ) => 2 * Real.pi * |β| * (∑ m ∈ Finset.Ico l u, |D q a m|); let T : ℕ := 8000000000; ∀ (q a n : ℕ) (β : ℝ), 3 ≤ q → q ≤ 105 → a < q → Nat.Coprime a q → 4000000000000000000 ≤ n → |β| ≤ 140/(n:ℝ) → J q a 0 T β ≤ (n:ℝ)/10^12 := by

  dsimp only
  intro q a n β hq hqmax ha hcop hn hβ
  let T : ℕ := 8000000000
  let D : ℕ → ℝ := fun m => (∑ k ∈ (Finset.range (m+1)).filter (fun k => k % q=a % q), ArithmeticFunction.vonMangoldt k) - (m:ℝ)/Nat.totient q
  change 2 * Real.pi * |β| * (∑ m ∈ Finset.Ico 0 T, |D m|) ≤ (n:ℝ)/10^12
  have hT : (T:ℝ) ≤ (2:ℝ)^34 := by norm_num [T]
  have hlog2 : Real.log 2 ≤ 1 := by
    have h := Real.log_le_sub_one_of_pos (by norm_num : 0 < (2:ℝ))
    linarith
  have hlog : Real.log (T:ℝ) ≤ 50 := by
    calc
      _ ≤ Real.log ((2:ℝ)^34) := Real.log_le_log (by norm_num [T]) hT
      _ = (34:ℝ)*Real.log 2 := by rw [Real.log_pow]; norm_num
      _ ≤ 50 := by linarith
  have hΛ (k : ℕ) (hk : k ≤ T) : ArithmeticFunction.vonMangoldt k ≤ 50 := by
    by_cases hk0 : k = 0
    · subst k
      simp
    · exact ArithmeticFunction.vonMangoldt_le_log.trans ((Real.log_le_log (by exact_mod_cast Nat.pos_of_ne_zero hk0) (by exact_mod_cast hk)).trans hlog)
  have htot : (1:ℝ) ≤ Nat.totient q := by
    exact_mod_cast (show 1 ≤ Nat.totient q from Nat.totient_pos.mpr (by omega))
  have hD (m : ℕ) (hm : m ∈ Finset.Ico 0 T) : |D m| ≤ 51*(T:ℝ) := by
    have hmt : m < T := (Finset.mem_Ico.mp hm).2
    let s := (Finset.range (m+1)).filter (fun k => k % q=a % q)
    have hs : s.card ≤ T := (Finset.card_le_card (Finset.filter_subset _ _)).trans (by simpa using (show m+1 ≤ T by omega))
    have hsum0 : 0 ≤ ∑ k ∈ s, ArithmeticFunction.vonMangoldt k :=
      Finset.sum_nonneg (fun _ _ => ArithmeticFunction.vonMangoldt_nonneg)
    have hsum : (∑ k ∈ s, ArithmeticFunction.vonMangoldt k) ≤ 50*(T:ℝ) := by
      calc
        _ ≤ ∑ k ∈ s, (50:ℝ) := by
          apply Finset.sum_le_sum
          intro k hk
          have hkm := Finset.mem_range.mp (Finset.mem_filter.mp hk).1
          exact hΛ k (by omega)
        _ = (s.card:ℝ)*50 := by simp
        _ ≤ _ := by
          have hh : (s.card:ℝ) ≤ T := by exact_mod_cast hs
          linarith
    have hmR : (m:ℝ) ≤ T := by exact_mod_cast hmt.le
    have hdiv0 : 0 ≤ (m:ℝ)/Nat.totient q := by positivity
    have hdiv : (m:ℝ)/Nat.totient q ≤ (T:ℝ) := by
      apply (div_le_iff₀ (by linarith : (0:ℝ)<Nat.totient q)).mpr
      calc
        _ ≤ (T:ℝ) := hmR
        _ = (T:ℝ)*1 := by ring
        _ ≤ _ := mul_le_mul_of_nonneg_left htot (by positivity)
    change |(∑ k ∈ s, ArithmeticFunction.vonMangoldt k)-(m:ℝ)/Nat.totient q| ≤ _
    rw [abs_le]
    have hT0 : (0:ℝ) ≤ (T:ℝ) := by positivity
    constructor
    · linarith only [hsum0, hdiv, hT0]
    · calc
        _ ≤ ∑ k ∈ s, ArithmeticFunction.vonMangoldt k := sub_le_self _ hdiv0
        _ ≤ 50*(T:ℝ) := hsum
        _ ≤ 51*(T:ℝ) := mul_le_mul_of_nonneg_right (by norm_num) hT0
  have hS : (∑ m ∈ Finset.Ico 0 T, |D m|) ≤ 51*(T:ℝ)^2 := by
    calc
      _ ≤ ∑ m ∈ Finset.Ico 0 T, 51*(T:ℝ) := Finset.sum_le_sum hD
      _ = _ := by simp [Nat.card_Ico]; ring
  have hnR : (4000000000000000000:ℝ) ≤ n := by exact_mod_cast hn
  have hqR : (1:ℝ) ≤ q := by exact_mod_cast (show 1≤q by omega)
  have hden : (4000000000000000000:ℝ) ≤ (q:ℝ)*n := by
    calc
      _ ≤ (n:ℝ) := hnR
      _ = 1*(n:ℝ) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_right hqR (by positivity)
  have hβ' : |β| ≤ (140:ℝ)/4000000000000000000 :=
    hβ.trans (div_le_div_of_nonneg_left (by norm_num) (by norm_num) hnR)
  have hpi : 2*Real.pi ≤ 8 := by linarith [Real.pi_lt_four]
  calc
    _ ≤ 8*((140:ℝ)/4000000000000000000)*(51*(T:ℝ)^2) := by
      exact mul_le_mul (mul_le_mul hpi hβ' (abs_nonneg _) (by norm_num))
        hS (Finset.sum_nonneg (fun _ _ => abs_nonneg _)) (by positivity)
    _ ≤ (4000000000000000000:ℝ)/10^12 := by norm_num [T]
    _ ≤ _ := div_le_div_of_nonneg_right hnR (by norm_num)



private noncomputable def ph (M j k : ℕ) : ℂ :=
  Complex.exp (((2 * Real.pi * ((j : ℝ) * (k : ℝ) / M) : ℝ) : ℂ) * Complex.I)


private theorem parseval_range (M : ℕ) (f : ℕ → ℂ) :
    (∑ j ∈ range M, ‖∑ k ∈ range M, f k * ph M j k‖^2)
      = (M:ℝ)*∑ k ∈ range M, ‖f k‖^2 := PEqualNP.Outside.L_goldbach_discrete_parseval M f

noncomputable def E (x : ℝ) : ℂ :=
  Complex.exp (((2*Real.pi*x:ℝ):ℂ)*Complex.I)

private noncomputable def P (q a m : ℕ) : ℝ :=
  (∑ k ∈ (range (m+1)).filter (fun k => k % q = a % q), vonMangoldt k) -
    (m:ℝ)/Nat.totient q

def BMOR : Prop := ∀ (q a m : ℕ), 3 ≤ q → q ≤ 105 → a < q →
  Nat.Coprime a q → 8000000000 ≤ m →
    |(∑ k ∈ (range (m+1)).filter (fun k => k % q = a % q), vonMangoldt k) -
      (m:ℝ)/Nat.totient q| ≤ (m:ℝ)/(840*Real.log (m:ℝ))

private theorem logT : 22 ≤ Real.log (8000000000:ℝ) := by
  rw [show (8000000000:ℝ) = 2^12*5^9 by norm_num,
    Real.log_mul (by norm_num) (by norm_num), Real.log_pow, Real.log_pow]
  norm_num
  linarith [Real.log_two_gt_d9,Real.log_five_gt_d9]

private theorem logL : 34 ≤ Real.log (600000000000000:ℝ) := by
  rw [show (600000000000000:ℝ) = 2^15*3*5^14 by norm_num,
    Real.log_mul (by norm_num) (by norm_num),Real.log_mul (by norm_num) (by norm_num),
    Real.log_pow,Real.log_pow]
  norm_num
  linarith [Real.log_two_gt_d9,Real.log_three_gt_d9,Real.log_five_gt_d9]

private theorem logN (n : ℕ) (hn : 4000000000000000000 ≤ n) :
    42 ≤ Real.log (n:ℝ) := by
  have h : Real.log (4000000000000000000:ℝ) ≤ Real.log (n:ℝ) :=
    Real.log_le_log (by norm_num) (by exact_mod_cast hn)
  rw [show (4000000000000000000:ℝ) = 2^20*5^18 by norm_num,
    Real.log_mul (by norm_num) (by norm_num),Real.log_pow,Real.log_pow] at h
  norm_num at h
  linarith [Real.log_two_gt_d9,Real.log_five_gt_d9]

private theorem prefixSum (n : ℕ) : (∑ m ∈ range n, (m:ℝ)) ≤ (n:ℝ)^2/2 := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [sum_range_succ,Nat.cast_succ]
    nlinarith only [ih]

private theorem prefixBound (h : BMOR) (q a m : ℕ) (hq : 3 ≤ q) (hq' : q ≤ 105)
    (ha : a < q) (hc : Nat.Coprime a q) (hm : 8000000000 ≤ m)
    (t : ℝ) (ht : 0 < t) (htm : t ≤ Real.log (m:ℝ)) :
    |P q a m| ≤ (m:ℝ)/(840*t) := by
  apply (h q a m hq hq' ha hc hm).trans
  exact div_le_div_of_nonneg_left (by positivity) (by positivity)
    (mul_le_mul_of_nonneg_left htm (by norm_num))

private theorem piBound : Real.pi ≤ 22/7 := by
  linarith [Real.pi_lt_d4]

private theorem threeRanges (h : BMOR) (q a n : ℕ) (β : ℝ)
    (hq : 3 ≤ q) (hq' : q ≤ 105) (ha : a < q) (hc : Nat.Coprime a q)
    (hn : 4000000000000000000 ≤ n) (hβ : |β| ≤ 140/(n:ℝ)) :
    ‖∑ k ∈ Icc 1 n, (((if k % q=a then vonMangoldt k else 0) -
      1/(Nat.totient q:ℝ):ℝ):ℂ)*E ((k:ℝ)*β)‖ ≤
      (n:ℝ)*(2/(10^9:ℝ)+1/(840*42)) +
        Real.pi* |β| *(n:ℝ)^2/(840*34) := by
  let T : ℕ := 8000000000
  let L : ℕ := 600000000000000
  let B := 2*Real.pi* |β|
  have hB : 0 ≤ B := by positivity
  have hnR : (4000000000000000000:ℝ) ≤ n := by exact_mod_cast hn
  have hβ' : |β| ≤ (140:ℝ)/4000000000000000000 :=
    hβ.trans (div_le_div_of_nonneg_left (by norm_num) (by norm_num) hnR)
  have hA := abelTwo q a n T β (by omega) (by dsimp [T]; omega)
  dsimp only at hA
  change ‖∑ k ∈ Icc 1 n, (((if k % q=a % q then vonMangoldt k else 0) -
      1/(Nat.totient q:ℝ):ℝ):ℂ)*E ((k:ℝ)*β)‖ ≤
      |P q a n| + B*(∑ m ∈ Ico 0 T, |P q a m|) +
        B*(∑ m ∈ Ico T n, |P q a m|) at hA
  have hmod : a % q = a := Nat.mod_eq_of_lt ha
  simp only [hmod] at hA
  have hEarly := earlyCost q a n β hq hq' ha hc hn hβ
  change B*(∑ m ∈ Ico 0 T, |P q a m|) ≤ (n:ℝ)/10^12 at hEarly
  have hEnd : |P q a n| ≤ (n:ℝ)/(840*42) :=
    prefixBound h q a n hq hq' ha hc (by omega) 42 (by norm_num) (logN n hn)
  have hmid : (∑ m ∈ Ico T L, |P q a m|) ≤ (L:ℝ)^2/(840*22) := by
    calc
      _ ≤ ∑ m ∈ Ico T L, (L:ℝ)/(840*22) := by
        apply sum_le_sum
        intro m hm
        have hmt := (mem_Ico.mp hm).1
        have hml := (mem_Ico.mp hm).2
        have hlog : 22 ≤ Real.log (m:ℝ) := logT.trans
          (Real.log_le_log (by norm_num) (by exact_mod_cast hmt))
        exact (prefixBound h q a m hq hq' ha hc hmt 22 (by norm_num) hlog).trans
          (div_le_div_of_nonneg_right (by exact_mod_cast hml.le) (by norm_num))
      _ = ((L-T:ℕ):ℝ)*((L:ℝ)/(840*22)) := by
        simp only [sum_const, Nat.card_Ico, nsmul_eq_mul]
      _ ≤ _ := by
        have hlt : ((L-T:ℕ):ℝ) ≤ L := by exact_mod_cast Nat.sub_le L T
        calc
          _ ≤ (L:ℝ)*((L:ℝ)/(840*22)) := mul_le_mul_of_nonneg_right hlt (by positivity)
          _ = _ := by ring
  have hMidCost : B*(∑ m ∈ Ico T L, |P q a m|) ≤
      (n:ℝ)*(2/10^9-1/10^12) := by
    have hb : B ≤ 7*((140:ℝ)/4000000000000000000) := by
      dsimp only [B]
      exact mul_le_mul (by linarith [piBound] : 2*Real.pi ≤ 7) hβ'
        (abs_nonneg _) (by norm_num)
    calc
      _ ≤ 7*((140:ℝ)/4000000000000000000)*((L:ℝ)^2/(840*22)) :=
        mul_le_mul hb hmid (sum_nonneg fun _ _ => abs_nonneg _) (by positivity)
      _ ≤ (4000000000000000000:ℝ)*(2/10^9-1/10^12) := by norm_num [L]
      _ ≤ _ := mul_le_mul_of_nonneg_right hnR (by norm_num)
  have htail : (∑ m ∈ Ico L n, |P q a m|) ≤ (n:ℝ)^2/(2*(840*34)) := by
    calc
      _ ≤ ∑ m ∈ Ico L n, (m:ℝ)/(840*34) := by
        apply sum_le_sum
        intro m hm
        have hmL := (mem_Ico.mp hm).1
        have hlog : 34 ≤ Real.log (m:ℝ) := logL.trans
          (Real.log_le_log (by norm_num) (by exact_mod_cast hmL))
        exact prefixBound h q a m hq hq' ha hc (by dsimp [L] at hmL; omega) 34 (by norm_num) hlog
      _ = (∑ m ∈ Ico L n, (m:ℝ))/(840*34) := by rw [sum_div]
      _ ≤ _ := by
        have hs : (∑ m ∈ Ico L n, (m:ℝ)) ≤ (n:ℝ)^2/2 :=
          (sum_le_sum_of_subset_of_nonneg (t := range n)
            (fun m hm => mem_range.mpr (mem_Ico.mp hm).2) (by intros; positivity)).trans (prefixSum n)
        calc
          _ ≤ ((n:ℝ)^2/2)/(840*34) := div_le_div_of_nonneg_right hs (by norm_num)
          _ = _ := by ring
  have hTailCost : B*(∑ m ∈ Ico L n, |P q a m|) ≤
      Real.pi* |β| *(n:ℝ)^2/(840*34) := by
    calc
      _ ≤ B*((n:ℝ)^2/(2*(840*34))) := mul_le_mul_of_nonneg_left htail hB
      _ = _ := by dsimp [B]; ring
  have hs : (∑ m ∈ Ico T L, |P q a m|) + (∑ m ∈ Ico L n, |P q a m|) =
      ∑ m ∈ Ico T n, |P q a m| :=
    sum_Ico_consecutive _ (by norm_num [T,L]) (by dsimp [L]; omega)
  rw [← hs, mul_add] at hA
  linarith only [hA,hEarly,hEnd,hMidCost,hTailCost]


noncomputable def V (n : ℕ) (β : ℝ) : ℂ :=
  ∑ k ∈ Icc 1 n, E ((k:ℝ)*β)

noncomputable def S (n : ℕ) (α : ℝ) : ℂ :=
  ∑ k ∈ Icc 1 n, (vonMangoldt k:ℂ)*E ((k:ℝ)*α)

noncomputable def M (n q : ℕ) (β : ℝ) : ℂ :=
  ((moebius q:ℤ):ℂ)/(Nat.totient q:ℂ)*V n β

def A (q : ℕ) : Finset ℕ := (range q).filter (fun a => Nat.Coprime a q)

private noncomputable def G (n p r : ℕ) (β : ℝ) : ℂ :=
  ∑ k ∈ (Icc 1 n).filter (fun k => k % p = r), (vonMangoldt k:ℂ)*E ((k:ℝ)*β)

private noncomputable def F (n p r : ℕ) (β : ℝ) : ℂ :=
  G n p r β - (if Nat.Coprime r p then V n β/(Nat.totient p:ℂ) else 0)

private noncomputable def B (n : ℕ) (β : ℝ) : ℝ :=
  (n:ℝ)*(2/(10^9:ℝ)+1/(840*42)) + Real.pi* |β| *(n:ℝ)^2/(840*34)

private noncomputable def δ (n : ℕ) : ℝ := (n:ℝ)/10^9

noncomputable def c (q : ℕ) : ℝ := if q ≤ 2 then 2 else 1

noncomputable def a (q : ℕ) : ℝ := c q/(840*42)+2/10^8

noncomputable def H (n q : ℕ) : ℝ := 140/((q:ℝ)*(n:ℝ))

private theorem cardA (q : ℕ) : (A q).card = q.totient := by
  rw [Nat.totient_eq_card_coprime]
  congr 1
  ext x
  simp only [A,mem_filter,Nat.coprime_comm]

private theorem normE (t : ℝ) : ‖E t‖ = 1 := Complex.norm_exp_ofReal_mul_I _

private theorem Eadd (x y : ℝ) : E (x+y) = E x * E y := by
  unfold E
  rw [← Complex.exp_add]
  congr 1
  push_cast
  ring

private theorem Enat (n : ℕ) : E (n:ℝ) = 1 := by
  unfold E
  have he : (((2*Real.pi*(n:ℝ):ℝ):ℂ)*Complex.I) = (n:ℕ)*(2*Real.pi*Complex.I) := by
    push_cast
    ring
  rw [he,Complex.exp_nat_mul,Complex.exp_two_pi_mul_I,one_pow]

private theorem phaseMod (p q a k : ℕ) (hp : 0 < p) (hq : 0 < q) (hd : q ∣ p) (β : ℝ) :
    E ((k:ℝ)*((a:ℝ)/q+β)) =
      E ((k:ℝ)*β)*E ((a:ℝ)*((k % p:ℕ):ℝ)/q) := by
  obtain ⟨j,hj⟩ := hd
  have hk : (k:ℝ) = (p:ℝ)*(k/p:ℕ)+(k % p:ℕ) := by
    exact_mod_cast (Nat.div_add_mod k p).symm
  have hq0 : (q:ℝ) ≠ 0 := by positivity
  have he : (k:ℝ)*((a:ℝ)/q+β) = (k:ℝ)*β+(a:ℝ)*((k % p:ℕ):ℝ)/q+
      ((a*j*(k/p):ℕ):ℝ) := by
    have hpc : (p:ℝ)=(q:ℝ)*j := by exact_mod_cast hj
    have hk' : (k:ℝ) = (q:ℝ)*j*(k/p:ℕ)+(k % p:ℕ) := by rw [hk,hpc]
    push_cast
    field_simp
    linear_combination (a:ℝ)*hk'
  rw [he,Eadd,Eadd,Enat,mul_one]

private theorem phaseGroup (n p q a : ℕ) (hp : 0 < p) (hq : 0 < q) (hd : q ∣ p) (β : ℝ) :
    S n ((a:ℝ)/q+β) = ∑ r ∈ range p, G n p r β * E ((a:ℝ)*(r:ℝ)/q) := by
  unfold S
  calc
    _ = ∑ k ∈ Icc 1 n, (vonMangoldt k:ℂ)*E ((k:ℝ)*β)*
        E ((a:ℝ)*((k % p:ℕ):ℝ)/q) := by
      apply sum_congr rfl
      intro k hk
      rw [phaseMod p q a k hp hq hd β]
      ring
    _ = ∑ r ∈ range p, ∑ k ∈ (Icc 1 n).filter (fun k => k % p=r),
        (vonMangoldt k:ℂ)*E ((k:ℝ)*β)*E ((a:ℝ)*((k % p:ℕ):ℝ)/q) :=
      (sum_fiberwise_of_maps_to (fun k _ => mem_range.mpr (Nat.mod_lt k hp)) _).symm
    _ = _ := by
      apply sum_congr rfl
      intro r hr
      rw [G,sum_mul]
      apply sum_congr rfl
      intro k hk
      rw [(mem_filter.mp hk).2]

private theorem unitError (h : BMOR) (n p r : ℕ) (β : ℝ)
    (hp : 3 ≤ p) (hp' : p ≤ 105) (hr : r < p) (hc : Nat.Coprime r p)
    (hn : 4000000000000000000 ≤ n) (hb : |β| ≤ 140/(n:ℝ)) :
    ‖F n p r β‖ ≤ B n β := by
  have h3 := threeRanges h p r n β hp hp' hr hc hn hb
  have he : F n p r β =
      ∑ k ∈ Icc 1 n, (((if k % p=r then vonMangoldt k else 0) -
        1/(Nat.totient p:ℝ):ℝ):ℂ)*E ((k:ℝ)*β) := by
    unfold F G V
    rw [if_pos hc,Finset.sum_filter,Finset.sum_div,← Finset.sum_sub_distrib]
    apply sum_congr rfl
    intro k hk
    have hp0 : (p.totient:ℝ) ≠ 0 := by exact_mod_cast (Nat.totient_pos.mpr (by omega : 0 < p)).ne'
    by_cases hm : k % p=r
    · simp only [if_pos hm,Complex.ofReal_sub,Complex.ofReal_div,Complex.ofReal_one,Complex.ofReal_natCast]
      ring
    · simp only [if_neg hm,Complex.ofReal_sub,Complex.ofReal_div,Complex.ofReal_one,
        Complex.ofReal_natCast,Complex.ofReal_zero]
      ring
  rw [he]
  exact h3

private theorem logSmall (n : ℕ) (hn : 4000000000000000000 ≤ n) :
    106*Real.log (n:ℝ) ≤ δ n := by
  have hnR : (4000000000000000000:ℝ) ≤ n := by exact_mod_cast hn
  have hnp : (0:ℝ) < n := by linarith
  have hlog : Real.log (10^12:ℝ) ≤ 36 := by
    rw [Real.log_pow,Real.log_ten_eq]
    norm_num
    linarith [Real.log_two_lt_d9,Real.log_five_lt_d9]
  have hs : Real.log ((n:ℝ)/10^12) ≤ (n:ℝ)/10^12-1 :=
    Real.log_le_sub_one_of_pos (by positivity)
  rw [Real.log_div (by positivity) (by positivity)] at hs
  unfold δ
  norm_num at hs hlog ⊢
  linarith only [hnR,hs,hlog]

private theorem nonunitError (n p r : ℕ) (β : ℝ)
    (hp : 1 ≤ p) (hp' : p ≤ 105) (hr : r < p) (hc : ¬Nat.Coprime r p)
    (hn : 4000000000000000000 ≤ n) :
    ‖F n p r β‖ ≤ δ n := by
  rw [F,if_neg hc,sub_zero]
  unfold G
  have hcard : p.primeFactors.card ≤ 106 := by
    have hs : p.primeFactors ⊆ range 106 := by
      intro z hz
      exact mem_range.mpr (by
        have hh := Nat.le_of_dvd (by omega : 0 < p) (Nat.dvd_of_mem_primeFactors hz)
        omega)
    simpa using card_le_card hs
  have hsub : (Icc 1 n).filter (fun k => k % p=r) ⊆
      (range (n+1)).filter (fun k => ¬Nat.Coprime k p) := by
    intro k hk
    obtain ⟨hkn,hkr⟩ := mem_filter.mp hk
    refine mem_filter.mpr ⟨mem_range.mpr (by have := (mem_Icc.mp hkn).2; omega),?_⟩
    intro hcop
    apply hc
    rw [← hkr]
    change Nat.gcd (k % p) p = 1
    rw [← Nat.gcd_rec p k, Nat.gcd_comm]
    exact hcop.gcd_eq_one
  calc
    _ ≤ ∑ k ∈ (Icc 1 n).filter (fun k => k % p=r), ‖(vonMangoldt k:ℂ)*E ((k:ℝ)*β)‖ :=
      norm_sum_le _ _
    _ = ∑ k ∈ (Icc 1 n).filter (fun k => k % p=r), vonMangoldt k := by
      apply sum_congr rfl
      intro k hk
      rw [norm_mul,normE,mul_one,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg vonMangoldt_nonneg]
    _ ≤ ∑ k ∈ (range (n+1)).filter (fun k => ¬Nat.Coprime k p), vonMangoldt k :=
      sum_le_sum_of_subset_of_nonneg hsub (fun _ _ _ => vonMangoldt_nonneg)
    _ ≤ (p.primeFactors.card:ℝ)*Real.log (n:ℝ) := nonunitMass p n hp (by omega)
    _ ≤ 106*Real.log (n:ℝ) :=
      mul_le_mul_of_nonneg_right (by exact_mod_cast hcard) (by linarith [logN n hn])
    _ ≤ _ := logSmall n hn

private theorem mode (p q a : ℕ) (hp : 0 < p) (hq : 0 < q) (ha : a < q)
    (hc : Nat.Coprime a q) (h : p=q ∨ (p=4 ∧ q ≤ 2)) :
    (∑ r ∈ A p, E ((a:ℝ)*(r:ℝ)/q)) = ((moebius q:ℤ):ℂ)*(p.totient:ℂ)/(q.totient:ℂ) := by
  rcases h with hpq | ⟨rfl,hsmall⟩
  · subst p
    have he : ∀ r : ℕ, E ((a:ℝ)*(r:ℝ)/q) =
        Complex.exp (Complex.I*((2*Real.pi*(a:ℝ)*(r:ℝ)/(q:ℝ):ℝ):ℂ)) := by
      intro r
      unfold E
      congr 1
      push_cast
      ring
    simp_rw [he]
    change (∑ r ∈ (range q).filter (fun r => Nat.Coprime r q), _) = _
    rw [constantMode a q hq hc]
    have ht : (q.totient:ℂ) ≠ 0 := by exact_mod_cast (Nat.totient_pos.mpr hq).ne'
    field_simp
  · have hA4 : A 4 = ({1,3}:Finset ℕ) := by decide
    have hφ4 : Nat.totient 4=2 := by decide
    rw [hA4,hφ4,sum_pair (by decide : (1:ℕ)≠3)]
    have hEhalf : E (1/2) = -1 := by
      unfold E
      have he : (((2*Real.pi*(1/2):ℝ):ℂ)*Complex.I) = Real.pi*Complex.I := by push_cast; ring
      rw [he,Complex.exp_pi_mul_I]
    have hEthree : E (3/2) = -1 := by
      rw [show (3/2:ℝ)=1/2+1 by norm_num,Eadd,hEhalf,show E (1:ℝ)=1 from Enat 1,mul_one]
    interval_cases q
    · have ha0 : a=0 := by omega
      subst a
      have hμ : moebius 1 = 1 := by simp
      have hφ : Nat.totient 1 = 1 := by decide
      norm_num [E,hμ,hφ]
    · have ha1 : a=1 := by
        interval_cases a
        · norm_num at hc
        · rfl
      subst a
      have hμ : moebius 2 = -1 := ArithmeticFunction.moebius_apply_prime Nat.prime_two
      have hφ : Nat.totient 2 = 1 := by decide
      norm_num [hμ,hφ,hEhalf,hEthree]

private theorem errorGroup (n p q a : ℕ) (β : ℝ)
    (hp : 0 < p) (hq : 0 < q) (hd : q ∣ p) (ha : a < q) (hc : Nat.Coprime a q)
    (h : p=q ∨ (p=4 ∧ q ≤ 2)) :
    S n ((a:ℝ)/q+β)-M n q β = ∑ r ∈ range p, F n p r β*E ((a:ℝ)*(r:ℝ)/q) := by
  rw [phaseGroup n p q a hp hq hd β]
  have ht : (p.totient:ℂ) ≠ 0 := by exact_mod_cast (Nat.totient_pos.mpr hp).ne'
  have hu : (q.totient:ℂ) ≠ 0 := by exact_mod_cast (Nat.totient_pos.mpr hq).ne'
  have he : (∑ r ∈ range p, (if Nat.Coprime r p then V n β/(p.totient:ℂ) else 0) *
      E ((a:ℝ)*(r:ℝ)/q)) = M n q β := by
    calc
      _ = ∑ r ∈ A p, (V n β/(p.totient:ℂ))*E ((a:ℝ)*(r:ℝ)/q) := by
        rw [A,sum_filter]
        apply sum_congr rfl
        intro r hr
        split_ifs <;> simp
      _ = (V n β/(p.totient:ℂ))*(∑ r ∈ A p, E ((a:ℝ)*(r:ℝ)/q)) := by rw [mul_sum]
      _ = _ := by rw [mode p q a hp hq ha hc h]; unfold M; field_simp <;> ring
  unfold F
  simp_rw [sub_mul]
  rw [sum_sub_distrib,he]

private theorem Blarge (n : ℕ) (β : ℝ) :
    100*δ n ≤ B n β := by
  unfold B δ
  have hn : (0:ℝ) ≤ n := by positivity
  have hp : 0 ≤ Real.pi* |β| *(n:ℝ)^2/(840*34) := by positivity
  linarith

private theorem affineCompare (n q : ℕ) (β : ℝ) (hn : 0 < n) (hq : 0 < q) :
    c q*B n β + (10-c q)*δ n ≤ (n:ℝ)*a q + c q*(22/7)* |β| *(n:ℝ)^2/(840*34) := by
  have hc : 0 ≤ c q := by unfold c; split_ifs <;> norm_num
  have h := mul_le_mul_of_nonneg_right piBound
      (show 0 ≤ c q* |β| *(n:ℝ)^2/(840*34) by positivity)
  unfold B δ a
  unfold c at *
  split_ifs at * <;> nlinarith only [h,Nat.cast_nonneg (α:=ℝ) n]

theorem energyPoint (h : BMOR) (n q : ℕ) (β : ℝ)
    (hn : 4000000000000000000 ≤ n) (hq : 1 ≤ q) (hq' : q ≤ 105) (hb : |β| ≤ H n q) :
    (∑ i ∈ A q, ‖S n ((i:ℝ)/q+β)-M n q β‖^2) ≤
      (q:ℝ)*(q.totient:ℝ)*((n:ℝ)*a q + c q*(22/7)* |β| *(n:ℝ)^2/(840*34))^2 := by
  have hnp : 0 < n := by omega
  have hqp : 0 < q := by omega
  have hnR : (0:ℝ) < n := by positivity
  have hqR : (1:ℝ) ≤ q := by exact_mod_cast hq
  have hφ : (1:ℝ) ≤ q.totient := by exact_mod_cast Nat.totient_pos.mpr hqp
  have hβ : |β| ≤ 140/(n:ℝ) := by
    apply hb.trans
    unfold H
    apply div_le_div_of_nonneg_left (by norm_num) hnR
    simpa using mul_le_mul_of_nonneg_right hqR hnR.le
  have hδ : 0 ≤ δ n := by unfold δ; positivity
  have hB : 0 ≤ B n β := by linarith [Blarge n β]
  have hD : 0 ≤ B n β+9*δ n := by positivity
  by_cases hsmall : q ≤ 2
  · have hsum (i : ℕ) (hi : i ∈ A q) :
        ‖S n ((i:ℝ)/q+β)-M n q β‖ ≤ 2*B n β+8*δ n := by
      obtain ⟨hil,hic⟩ := mem_filter.mp hi
      have hq4 : q ∣ 4 := by interval_cases q <;> decide
      rw [errorGroup n 4 q i β (by decide) hqp hq4 (mem_range.mp hil) hic (Or.inr ⟨rfl,hsmall⟩)]
      have hterm (r : ℕ) (hr : r ∈ range 4) :
          ‖F n 4 r β*E ((i:ℝ)*(r:ℝ)/q)‖ ≤
            if Nat.Coprime r 4 then B n β else δ n := by
        rw [norm_mul,normE,mul_one]
        split_ifs with hc
        · exact unitError h n 4 r β (by decide) (by decide) (mem_range.mp hr) hc hn hβ
        · exact nonunitError n 4 r β (by decide) (by decide) (mem_range.mp hr) hc hn
      calc
        _ ≤ ∑ r ∈ range 4, ‖F n 4 r β*E ((i:ℝ)*(r:ℝ)/q)‖ := norm_sum_le _ _
        _ ≤ ∑ r ∈ range 4, if Nat.Coprime r 4 then B n β else δ n := sum_le_sum hterm
        _ = 2*B n β+2*δ n := by norm_num [sum_range_succ]; ring
        _ ≤ _ := by linarith
    have hh (i : ℕ) (hi : i ∈ A q) :
        ‖S n ((i:ℝ)/q+β)-M n q β‖ ≤
          (n:ℝ)*a q+c q*(22/7)* |β| *(n:ℝ)^2/(840*34) := by
      apply (hsum i hi).trans
      simpa [c,hsmall,show (10:ℝ)-2=8 by norm_num,show (10:ℝ)-1=9 by norm_num] using affineCompare n q β hnp hqp
    let W := (n:ℝ)*a q+c q*(22/7)* |β| *(n:ℝ)^2/(840*34)
    calc
      _ ≤ ∑ i ∈ A q, W^2 := sum_le_sum (fun i hi => pow_le_pow_left₀ (norm_nonneg _) (hh i hi) 2)
      _ = (q.totient:ℝ)*W^2 := by simp [cardA,nsmul_eq_mul]
      _ ≤ _ := by
        change _ ≤ (q:ℝ)*(q.totient:ℝ)*W^2
        have he := mul_le_mul_of_nonneg_right hqR (show 0 ≤ (q.totient:ℝ)*W^2 by positivity)
        linarith only [he]
  · have hq3 : 3 ≤ q := by omega
    have he (i : ℕ) (hi : i ∈ A q) :
        S n ((i:ℝ)/q+β)-M n q β =
          ∑ r ∈ range q, F n q r β*ph q i r :=
      errorGroup n q q i β hqp hqp dvd_rfl (mem_range.mp (mem_filter.mp hi).1)
        (mem_filter.mp hi).2 (Or.inl rfl)
    have hsum : (∑ r ∈ range q, ‖F n q r β‖^2) ≤
        (q.totient:ℝ)*(B n β)^2 + (q:ℝ)*(δ n)^2 := by
      calc
        _ ≤ ∑ r ∈ range q, ((if Nat.Coprime r q then (B n β)^2 else 0)+(δ n)^2) := by
          apply sum_le_sum
          intro r hr
          by_cases hc : Nat.Coprime r q
          · rw [if_pos hc]
            exact (pow_le_pow_left₀ (norm_nonneg _) (unitError h n q r β hq3 hq' (mem_range.mp hr) hc hn hβ) 2).trans
              (le_add_of_nonneg_right (sq_nonneg _))
          · rw [if_neg hc,zero_add]
            exact pow_le_pow_left₀ (norm_nonneg _) (nonunitError n q r β hq hq' (mem_range.mp hr) hc hn) 2
        _ = _ := by
          rw [sum_add_distrib, ← sum_filter]
          change (∑ r ∈ A q, (B n β)^2) + (∑ r ∈ range q, (δ n)^2) = _
          rw [sum_const, sum_const, cardA, card_range, nsmul_eq_mul, nsmul_eq_mul]
    have hbudget : (q.totient:ℝ)*(B n β)^2+(q:ℝ)*(δ n)^2 ≤
        (q.totient:ℝ)*(B n β+9*δ n)^2 := by
      have hq105 : (q:ℝ) ≤ 105 := by exact_mod_cast hq'
      have h0 := mul_le_mul_of_nonneg_right hq105 (sq_nonneg (δ n))
      have h1 := mul_le_mul_of_nonneg_right (Blarge n β) hδ
      have h2 : (105:ℝ)*(δ n)^2 ≤ (B n β+9*δ n)^2-(B n β)^2 := by
        nlinarith only [h1,sq_nonneg (δ n)]
      have h3 := mul_le_mul_of_nonneg_right hφ (show 0 ≤ (B n β+9*δ n)^2-(B n β)^2 by linarith [h2,sq_nonneg (δ n)])
      nlinarith only [h0,h2,h3]
    have hcomp : B n β+9*δ n ≤ (n:ℝ)*a q+c q*(22/7)* |β| *(n:ℝ)^2/(840*34) := by
      simpa [c,hsmall,show (10:ℝ)-1=9 by norm_num] using affineCompare n q β hnp hqp
    calc
      _ = ∑ i ∈ A q, ‖∑ r ∈ range q, F n q r β*ph q i r‖^2 := by
        apply sum_congr rfl
        intro i hi
        rw [he i hi]
      _ ≤ ∑ i ∈ range q, ‖∑ r ∈ range q, F n q r β*ph q i r‖^2 :=
        sum_le_sum_of_subset_of_nonneg (filter_subset _ _) (by intros; positivity)
      _ = (q:ℝ)*∑ r ∈ range q, ‖F n q r β‖^2 := parseval_range q _
      _ ≤ (q:ℝ)*((q.totient:ℝ)*(B n β+9*δ n)^2) :=
        mul_le_mul_of_nonneg_left (hsum.trans hbudget) (by positivity)
      _ ≤ _ := by
        rw [← mul_assoc]
        exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hD hcomp 2) (by positivity)



end GoldbachCollarBmor

theorem Conjectures.Goldbach.FiniteCollarBmorPointwise :
    (∀ (q a m : ℕ), 3 ≤ q → q ≤ 105 → a < q → Nat.Coprime a q → 8000000000 ≤ m →
      |(∑ k ∈ (Finset.range (m+1)).filter (fun k => k % q=a % q), ArithmeticFunction.vonMangoldt k) -
         (m:ℝ)/q.totient| ≤ (m:ℝ)/(840*Real.log (m:ℝ))) →
    let E := fun x : ℝ => Complex.exp (((2*Real.pi*x:ℝ):ℂ)*Complex.I)
    let V := fun (n : ℕ) (t : ℝ) => ∑ k∈Finset.Icc 1 n, E ((k:ℝ)*t)
    let S := fun (n : ℕ) (t : ℝ) => ∑ k∈Finset.Icc 1 n, (ArithmeticFunction.vonMangoldt k:ℂ)*E ((k:ℝ)*t)
    let M := fun (n q : ℕ) (t : ℝ) => ((ArithmeticFunction.moebius q:ℤ):ℂ)/(q.totient:ℂ)*V n t
    let c := fun q : ℕ => if q ≤ 2 then (2:ℝ) else 1
    ∀ n q : ℕ, 4000000000000000000 ≤ n → 1 ≤ q → q ≤ 105 → ∀ t : ℝ, |t| ≤ 140/((q:ℝ)*n) →
      (∑ i∈(Finset.range q).filter (fun i => Nat.Coprime i q), ‖S n ((i:ℝ)/q+t)-M n q t‖^2) ≤
        (q:ℝ)*(q.totient:ℝ)*((n:ℝ)*(c q/(840*42)+2/10^8)+c q*(22/7)* |t| *(n:ℝ)^2/(840*34))^2 := by
  intro h
  dsimp only
  intro n q hn hq hq' t ht
  exact GoldbachCollarBmor.energyPoint h n q t hn hq hq' ht

end

section

/-! The integral uses both physical intervals of the collar for each reduced
centre. At denominator one the two intervals meet opposite ends of the period.
The rational check integrates the affine error separately at each modulus. -/
noncomputable section
open Finset MeasureTheory
open scoped Interval
namespace GoldbachCollarError
open GoldbachCollarBmor


set_option maxRecDepth 10000 in
set_option maxHeartbeats 1600000 in
private def b (q : ℕ) : ℝ := c q*(22/7)/(840*34*q)
set_option maxRecDepth 10000 in
set_option maxHeartbeats 1600000 in
private def moment (x y : ℝ) : ℝ :=
  35*x^2 + x*y*(140^2-105^2) + y^2*(140^3-105^3)/3
set_option maxRecDepth 10000 in
set_option maxHeartbeats 1600000 in
private def budget (q : ℕ) : ℝ := 2*q.totient*moment (a q) (b q)

set_option maxRecDepth 10000 in
set_option maxHeartbeats 1600000 in
def rationalBudget (q : ℕ) : ℚ :=
  let c : ℚ := if q ≤ 2 then 2 else 1
  let x := c/(840*42)+2/10^8
  let y := c*(22/7)/(840*34*q)
  2*q.totient*(35*x^2+x*y*(140^2-105^2)+y^2*(140^3-105^3)/3)

set_option maxRecDepth 10000 in
set_option maxHeartbeats 1600000 in
private theorem numeric : (∑ q∈Icc 1 105, budget q) < 97078/1000000 := by
  have h : (∑ q∈Icc 1 105, rationalBudget q) < (97078/1000000:ℚ) := by decide +kernel
  have eq (q : ℕ) : (rationalBudget q:ℝ) = budget q := by
    by_cases small : q ≤ 2 <;> simp [rationalBudget,budget,moment,b,a,c,small]
  have hr : (((∑ q∈Icc 1 105, rationalBudget q):ℚ):ℝ) < ((97078/1000000:ℚ):ℝ) := by
    exact_mod_cast h
  simpa only [Rat.cast_sum,eq,Rat.cast_div,Rat.cast_ofNat] using hr

set_option maxRecDepth 10000 in
set_option maxHeartbeats 1600000 in
private theorem polynomial (X Y l u : ℝ) :
    (∫ t in l..u, (X+Y*t)^2) =
      (u-l)*X^2+X*Y*(u^2-l^2)+Y^2*(u^3-l^3)/3 := by
  have eq : (fun t : ℝ => (X+Y*t)^2) = fun t => X^2+(2*X*Y)*t+Y^2*t^2 := by
    funext t
    ring
  rw [eq,intervalIntegral.integral_add (by apply Continuous.intervalIntegrable; fun_prop)
      (by apply Continuous.intervalIntegrable; fun_prop),
    intervalIntegral.integral_add (by apply Continuous.intervalIntegrable; fun_prop)
      (by apply Continuous.intervalIntegrable; fun_prop)]
  rw [intervalIntegral.integral_const_mul,intervalIntegral.integral_const_mul,
    intervalIntegral.integral_const,integral_id,integral_pow]
  simp only [smul_eq_mul]
  norm_num
  ring

set_option maxRecDepth 10000 in
set_option maxHeartbeats 1600000 in
def error (n q i : ℕ) (t : ℝ) : ℝ := ‖S n ((i:ℝ)/q+t)-M n q t‖^2

set_option maxRecDepth 10000 in
set_option maxHeartbeats 1600000 in
def collar (n q : ℕ) : ℝ := ∑ i∈A q,
  ∫ t in (105/((q:ℝ)*n))..(140/((q:ℝ)*n)), error n q i t + error n q i (-t)

set_option maxRecDepth 10000 in
set_option maxHeartbeats 1600000 in
private theorem per_modulus (h : BMOR) (n q : ℕ) (hn : 4000000000000000000 ≤ n)
    (hq : 1 ≤ q) (hmax : q ≤ 105) : collar n q ≤ (n:ℝ)*budget q := by
  let l := 105/((q:ℝ)*n)
  let u := 140/((q:ℝ)*n)
  let X := (n:ℝ)*a q
  let Y := c q*(22/7)*(n:ℝ)^2/(840*34)
  let K := 2*(q:ℝ)*q.totient
  have hn0 : (0:ℝ) < n := by exact_mod_cast (by omega : 0<n)
  have hq0 : (0:ℝ) < q := by exact_mod_cast (by omega : 0<q)
  have hl : 0 ≤ l := by dsimp [l]; positivity
  have order : l ≤ u := div_le_div_of_nonneg_right (by norm_num) (by positivity)
  have cont (i : ℕ) : Continuous (error n q i) := by
    change Continuous (fun t : ℝ => ‖S n ((i:ℝ)/q+t)-M n q t‖^2)
    unfold S M V E
    fun_prop
  have both (i : ℕ) : Continuous (fun t => error n q i t+error n q i (-t)) :=
    (cont i).add ((cont i).comp continuous_neg)
  have sumcont : Continuous (fun t => ∑ i∈A q, (error n q i t+error n q i (-t))) :=
    continuous_finsetSum _ fun i _ => both i
  change (∑ i∈A q, ∫ t in l..u, error n q i t+error n q i (-t)) ≤ _
  rw [← intervalIntegral.integral_finsetSum (fun i _ => (both i).intervalIntegrable l u)]
  calc
    _ ≤ ∫ t in l..u, K*(X+Y*t)^2 := by
      apply intervalIntegral.integral_mono_on order (sumcont.intervalIntegrable _ _)
        (by apply Continuous.intervalIntegrable; fun_prop)
      intro t ht
      have pos := hl.trans ht.1
      have upper : |t| ≤ H n q := by
        rw [abs_of_nonneg pos]
        exact (show t ≤ 140/((q:ℝ)*n) from ht.2)
      have p := energyPoint h n q t hn hq hmax upper
      have m := energyPoint h n q (-t) hn hq hmax (by rwa [abs_neg])
      rw [abs_neg] at m
      rw [abs_of_nonneg pos] at m p
      rw [sum_add_distrib]
      change (∑ i∈A q, ‖S n ((i:ℝ)/q+t)-M n q t‖^2) +
        (∑ i∈A q, ‖S n ((i:ℝ)/q+(-t))-M n q (-t)‖^2) ≤ _
      apply (add_le_add p m).trans_eq
      dsimp only [K,X,Y]
      ring
    _ = _ := by
      rw [intervalIntegral.integral_const_mul,polynomial]
      unfold budget moment b
      dsimp only [K,X,Y,l,u]
      field_simp [hq0.ne',hn0.ne'] <;> ring

set_option maxRecDepth 10000 in
set_option maxHeartbeats 1600000 in
theorem energy (h : BMOR) (n : ℕ) (hn : 4000000000000000000 ≤ n) :
    (∑ q∈Icc 1 105, collar n q) < (97078/1000000:ℝ)*n := by
  calc
    _ ≤ ∑ q∈Icc 1 105, (n:ℝ)*budget q := sum_le_sum fun q hq =>
      per_modulus h n q hn (mem_Icc.mp hq).1 (mem_Icc.mp hq).2
    _ = (n:ℝ)*(∑ q∈Icc 1 105, budget q) := (mul_sum ..).symm
    _ < _ := by rw [mul_comm]; exact mul_lt_mul_of_pos_right numeric (by exact_mod_cast (by omega : 0<n))


set_option maxRecDepth 10000 in
set_option maxHeartbeats 1600000 in
theorem collar_le_rational (h : BMOR) (n q : ℕ) (hn : 4000000000000000000 ≤ n)
    (hq : 1 ≤ q) (hmax : q ≤ 105) :
    collar n q ≤ (n:ℝ)*(rationalBudget q:ℝ) := by
  have eq : (rationalBudget q:ℝ) = budget q := by
    by_cases small : q ≤ 2 <;> simp [rationalBudget,budget,moment,b,a,c,small]
  rw [eq]
  exact per_modulus h n q hn hq hmax

end GoldbachCollarError

set_option maxRecDepth 10000 in
theorem Conjectures.Goldbach.FiniteCollarBmorErrorEnergy :
    (∀ (q a m : ℕ), 3 ≤ q → q ≤ 105 → a < q → Nat.Coprime a q → 8000000000 ≤ m →
      |(∑ k ∈ (Finset.range (m+1)).filter (fun k => k % q=a % q), ArithmeticFunction.vonMangoldt k) -
        (m:ℝ)/q.totient| ≤ (m:ℝ)/(840*Real.log (m:ℝ))) →
    let E := fun x : ℝ => Complex.exp (((2*Real.pi*x:ℝ):ℂ)*Complex.I)
    let V := fun (n : ℕ) (t : ℝ) => ∑ k∈Finset.Icc 1 n, E ((k:ℝ)*t)
    let S := fun (n : ℕ) (t : ℝ) => ∑ k∈Finset.Icc 1 n, (ArithmeticFunction.vonMangoldt k:ℂ)*E ((k:ℝ)*t)
    let M := fun (n q : ℕ) (t : ℝ) => ((ArithmeticFunction.moebius q:ℤ):ℂ)/(q.totient:ℂ)*V n t
    let err := fun (n q i : ℕ) (t : ℝ) => ‖S n ((i:ℝ)/q+t)-M n q t‖^2
    ∀ n : ℕ, 4000000000000000000 ≤ n →
      (∑ q∈Finset.Icc 1 105, ∑ i∈(Finset.range q).filter (fun v => Nat.Coprime v q),
        ∫ t in (105/((q:ℝ)*n))..(140/((q:ℝ)*n)), err n q i t+err n q i (-t)) <
        (97078/1000000:ℝ)*n := GoldbachCollarError.energy

end

end

section

/-!
For each denominator q there are φ(q) reduced centres. Squaring the amplitude
μ(q)/φ(q) and summing the two sides of each collar leaves the coefficient
μ(q)²/φ(q). At the centre zero the two sides represent the two ends of the
period. The geometric sum used here contains exactly the exponents 1,...,n.
-/
noncomputable section
open scoped Interval
open MeasureTheory
namespace FiniteCollarModelEnergy


set_option maxRecDepth 6000 in
abbrev wave := B13BilateralVaughanReductionProof.DyadicMixedB4Geometric.wave
set_option maxRecDepth 6000 in
abbrev phase := B13BilateralVaughanReductionProof.DyadicMixedB4Geometric.phase

set_option maxRecDepth 6000 in
def signal (n : ℕ) (x : ℝ) := wave 1 0 n x

set_option maxRecDepth 6000 in
private theorem signal_bound (n : ℕ) {x : ℝ} (hx : 0 < |x|) (hx' : |x| ≤ 1/2) :
    ‖signal n x‖ ≤ 1/(2*|x|) := by
  have hpi := Real.pi_pos
  have hθ : |Real.pi*x| ≤ Real.pi/2 := by
    rw [abs_mul,abs_of_pos hpi]
    nlinarith [mul_le_mul_of_nonneg_left hx' hpi.le]
  have hj := Real.mul_abs_le_abs_sin hθ
  rw [abs_mul,abs_of_pos hpi] at hj
  have eq : 2/Real.pi*(Real.pi*|x|)=2*|x| := by field_simp
  rw [eq] at hj
  have pos : 0 < |Real.sin (Real.pi*x)| := lt_of_lt_of_le (by positivity) hj
  have h := B13BilateralVaughanReductionProof.DyadicMixedB4Geometric.wave_sin 1 0 n x
    (by simpa using (abs_pos.mp pos))
  exact (show ‖signal n x‖ ≤ 1/|Real.sin (Real.pi*x)| by simpa [signal] using h).trans
    (div_le_div_of_nonneg_left (by norm_num) (by positivity) hj)

set_option maxRecDepth 6000 in
private theorem continuous_signal (n : ℕ) : Continuous (signal n) := by
  change Continuous (fun x : ℝ => ∑ k∈Finset.Ioc 0 n,
    Complex.exp (((2*Real.pi*(((1*k:ℕ):ℝ)*x):ℝ):ℂ)*Complex.I))
  fun_prop

set_option maxRecDepth 6000 in
def sides (n : ℕ) (t : ℝ) := ‖signal n t‖^2 + ‖signal n (-t)‖^2

set_option maxRecDepth 6000 in
private theorem collar_integral (n : ℕ) (A : ℝ) (hA : 280 ≤ A) :
    (∫ t in (105/A)..(140/A), sides n t) ≤
      A*((1/105-1/140)/2) := by
  have hpos : 0 < A := by linarith
  let a := 105/A
  let b := 140/A
  have ha : 0 < a := by dsimp [a]; positivity
  have hb : 0 < b := by dsimp [b]; positivity
  have order : a ≤ b := div_le_div_of_nonneg_right (by norm_num) hpos.le
  have half : b ≤ 1/2 := (div_le_iff₀ hpos).mpr (by linarith)
  have hz : (0:ℝ) ∉ [[a,b]] := by rw [Set.uIcc_of_le order]; simp [ha.not_ge]
  have cont : Continuous (sides n) :=
    ((continuous_signal n).norm.pow 2).add (((continuous_signal n).comp continuous_neg).norm.pow 2)
  change (∫ t in a..b, sides n t) ≤ _
  calc
    _ ≤ ∫ t in a..b, (1/2:ℝ)*(t^(-2:ℤ)) := by
      apply intervalIntegral.integral_mono_on order (cont.intervalIntegrable _ _)
        ((intervalIntegral.intervalIntegrable_zpow (μ:=volume) (n:=-2) (Or.inr hz)).const_mul _)
      intro t ht
      have ht0 := ha.trans_le ht.1
      have ht1 := ht.2.trans half
      have hp : 0 < |t| := by rwa [abs_of_pos ht0]
      have hh : |t| ≤ 1/2 := by rwa [abs_of_pos ht0]
      have h1 := signal_bound n hp hh
      have h2 := signal_bound n (x:=-t) (by rwa [abs_neg]) (by rwa [abs_neg])
      rw [abs_neg] at h2
      rw [abs_of_pos ht0] at h1 h2
      have s1 := pow_le_pow_left₀ (norm_nonneg _) h1 2
      have s2 := pow_le_pow_left₀ (norm_nonneg _) h2 2
      calc
        sides n t ≤ (1/(2*t))^2+(1/(2*t))^2 := add_le_add s1 s2
        _ = _ := by norm_num [zpow_neg]; ring
    _ = _ := by
      rw [intervalIntegral.integral_const_mul,integral_zpow (n:=-2) (Or.inr ⟨by decide,hz⟩)]
      norm_num [a,b,zpow_neg]
      ring

set_option maxRecDepth 6000 in
private theorem sharp_signal (n : ℕ) {x : ℝ} (hx : 0 < |x|) (hx' : |x| ≤ 1/1000) :
    ‖signal n x‖ ≤ 1 / ((157/50:ℝ)*|x|) := by
  let y := Real.pi*|x|
  have hy : 0 < y := mul_pos Real.pi_pos hx
  have hy1 : y ≤ 1/250 := calc
    _ ≤ 4*(1/1000:ℝ) :=
      mul_le_mul Real.pi_le_four hx' hx.le (by norm_num)
    _ = _ := by norm_num
  have h2 : y^2 ≤ (1/250:ℝ)^2 := pow_le_pow_left₀ hy.le hy1 2
  have h3 := mul_le_mul_of_nonneg_left h2 hy.le
  have hpi := mul_le_mul_of_nonneg_right Real.pi_gt_d4.le hx.le
  change 3.1415*|x| ≤ y at hpi
  have lower : (157/50:ℝ)*|x| ≤ Real.sin y := by
    have hs := Real.sin_ge_sub_cube hy.le
    nlinarith only [hpi,h3,hs,hx.le]
  have arg : |Real.pi*x| ≤ Real.pi := by
    rw [abs_mul,abs_of_pos Real.pi_pos]
    calc
      _ ≤ Real.pi*1 := mul_le_mul_of_nonneg_left (by linarith) Real.pi_pos.le
      _ = _ := mul_one _
  have mag : |Real.sin (Real.pi*x)|=Real.sin y := by
    rw [Real.abs_sin_eq_sin_abs_of_abs_le_pi arg,abs_mul,abs_of_pos Real.pi_pos]
  rw [←mag] at lower
  have pos : 0 < |Real.sin (Real.pi*x)| := lt_of_lt_of_le (by positivity) lower
  have h := B13BilateralVaughanReductionProof.DyadicMixedB4Geometric.wave_sin 1 0 n x
    (by simpa using (abs_pos.mp pos))
  exact (show ‖signal n x‖ ≤ 1/|Real.sin (Real.pi*x)| by simpa [signal] using h).trans
    (div_le_div_of_nonneg_left (by norm_num) (by positivity) lower)

set_option maxRecDepth 6000 in
theorem sharp_integral (n : ℕ) (A : ℝ) (hA : 140000 ≤ A) :
    (∫ t in (105/A)..(140/A), sides n t) ≤
      A*(2/(157/50:ℝ)^2*(1/105-1/140)) := by
  have hpos : 0 < A := by linarith
  let a := 105/A
  let b := 140/A
  have ha : 0 < a := by dsimp [a]; positivity
  have hb : 0 < b := by dsimp [b]; positivity
  have order : a ≤ b := div_le_div_of_nonneg_right (by norm_num) hpos.le
  have half : b ≤ 1/1000 := (div_le_iff₀ hpos).mpr (by linarith)
  have hz : (0:ℝ) ∉ [[a,b]] := by rw [Set.uIcc_of_le order]; simp [ha.not_ge]
  have cont : Continuous (sides n) :=
    ((continuous_signal n).norm.pow 2).add (((continuous_signal n).comp continuous_neg).norm.pow 2)
  change (∫ t in a..b, sides n t) ≤ _
  calc
    _ ≤ ∫ t in a..b, (2/(157/50:ℝ)^2)*(t^(-2:ℤ)) := by
      apply intervalIntegral.integral_mono_on order (cont.intervalIntegrable _ _)
        ((intervalIntegral.intervalIntegrable_zpow (μ:=volume) (n:=-2) (Or.inr hz)).const_mul _)
      intro t ht
      have ht0 := ha.trans_le ht.1
      have ht1 := ht.2.trans half
      have hp : 0 < |t| := by rwa [abs_of_pos ht0]
      have hh : |t| ≤ 1/1000 := by rwa [abs_of_pos ht0]
      have h1 := sharp_signal n hp hh
      have h2 := sharp_signal n (x:=-t) (by rwa [abs_neg]) (by rwa [abs_neg])
      rw [abs_neg] at h2
      rw [abs_of_pos ht0] at h1 h2
      have s1 := pow_le_pow_left₀ (norm_nonneg _) h1 2
      have s2 := pow_le_pow_left₀ (norm_nonneg _) h2 2
      calc
        sides n t ≤ (1/((157/50:ℝ)*t))^2+(1/((157/50:ℝ)*t))^2 := add_le_add s1 s2
        _ = _ := by norm_num [zpow_neg]; ring
    _ = _ := by
      rw [intervalIntegral.integral_const_mul,integral_zpow (n:=-2) (Or.inr ⟨by decide,hz⟩)]
      norm_num [a,b,zpow_neg]
      ring

set_option maxRecDepth 6000 in
def weight (q : ℕ) : ℝ := ((ArithmeticFunction.moebius q:ℤ):ℝ)^2/(q.totient:ℝ)

set_option maxRecDepth 6000 in
private theorem coefficient :
    (∑ q∈Finset.Icc 1 105, weight q*q)*((1/105-1/140)/2) =
      (721579568522251:ℝ)/5629041722304000 := by
  have h : (∑ q∈Finset.Icc 1 105, ((ArithmeticFunction.moebius q:ℤ):ℚ)^2/(q.totient:ℚ)*q)*
      ((1/105-1/140)/2) = (721579568522251:ℚ)/5629041722304000 := by decide +kernel
  have hr := congrArg (fun x : ℚ => (x : ℝ)) h
  simpa only [weight,Rat.cast_sum,Rat.cast_mul,Rat.cast_div,Rat.cast_sub,Rat.cast_pow,
    Rat.cast_natCast,Rat.cast_intCast,Rat.cast_ofNat,Rat.cast_one] using hr

set_option maxRecDepth 6000 in
def energy (n : ℕ) : ℝ :=
  ∑ q∈Finset.Icc 1 105, weight q*(∫ t in (105/((q:ℝ)*n))..(140/((q:ℝ)*n)), sides n t)

set_option maxRecDepth 6000 in
theorem model (n : ℕ) (hn : 280 ≤ n) :
    energy n ≤ (721579568522251/5629041722304000:ℝ)*n ∧ energy n < (13/100:ℝ)*n := by
  have bound : energy n ≤ (721579568522251/5629041722304000:ℝ)*n := by
    calc
      _ ≤ ∑ q∈Finset.Icc 1 105, weight q*(((q:ℝ)*n)*((1/105-1/140)/2)) := by
        apply Finset.sum_le_sum
        intro q hq
        have h1 := (Finset.mem_Icc.mp hq).1
        have hqn : 280 ≤ q*n := hn.trans (Nat.le_mul_of_pos_left n (by omega))
        have hh : (280:ℝ) ≤ (q:ℝ)*n := by exact_mod_cast hqn
        exact mul_le_mul_of_nonneg_left (collar_integral n _ hh) (by unfold weight; positivity)
      _ = ((∑ q∈Finset.Icc 1 105, weight q*q)*((1/105-1/140)/2))*n := by
        simp only [Finset.sum_mul]
        apply Finset.sum_congr rfl
        intro _ _
        ring
      _ = _ := by rw [coefficient]
  have npos : (0:ℝ)<n := by exact_mod_cast (by omega : 0<n)
  have less : (721579568522251/5629041722304000:ℝ) < 13/100 := by norm_num
  exact ⟨bound,bound.trans_lt (mul_lt_mul_of_pos_right less npos)⟩

end FiniteCollarModelEnergy

theorem Conjectures.Goldbach.FiniteCollarModelEnergy :
    ∀ n : ℕ, 280 ≤ n →
      let U := fun t : ℝ => ∑ k∈Finset.Ioc 0 n, Complex.exp (((2*Real.pi*((k:ℝ)*t):ℝ):ℂ)*Complex.I)
      let B := ∑ q∈Finset.Icc 1 105, (((ArithmeticFunction.moebius q:ℤ):ℝ)^2/(q.totient:ℝ))*
        (∫ t in (105/((q:ℝ)*n))..(140/((q:ℝ)*n)), ‖U t‖^2+‖U (-t)‖^2)
      B ≤ (721579568522251/5629041722304000:ℝ)*n ∧ B < (13/100:ℝ)*n := by
  intro n hn
  simpa [FiniteCollarModelEnergy.energy,FiniteCollarModelEnergy.sides,FiniteCollarModelEnergy.weight,
    FiniteCollarModelEnergy.signal,B13BilateralVaughanReductionProof.DyadicMixedB4Geometric.wave,
    B13BilateralVaughanReductionProof.DyadicMixedB4Geometric.phase] using FiniteCollarModelEnergy.model n hn

end

end

section

/-! Periodic arcs centered at reduced fractions. The negative half at the
zero fraction is represented near one. This avoids charging it twice. -/
noncomputable section
open MeasureTheory Finset
open scoped Interval
namespace GoldbachCollarCover


set_option maxRecDepth 6000 in
set_option maxHeartbeats 1000000 in
def arcs (n : ℕ) (w : ℝ) : Set ℝ := {t | ∃ (q a : ℕ) (k : ℤ),
  1≤q ∧ q≤105 ∧ a<q ∧ a.Coprime q ∧ |t-((a:ℝ)/q+k)|≤w/((q:ℝ)*n)}

set_option maxRecDepth 6000 in
set_option maxHeartbeats 1000000 in
theorem measurable_arcs (n : ℕ) (w : ℝ) : MeasurableSet (arcs n w) := by
  unfold arcs
  simp only [Set.setOf_exists]
  apply MeasurableSet.iUnion
  intro q
  apply MeasurableSet.iUnion
  intro a
  apply MeasurableSet.iUnion
  intro k
  by_cases c : 1≤q ∧ q≤105 ∧ a<q ∧ a.Coprime q
  · obtain ⟨hq,hq',ha,hc⟩ := c
    simp only [hq,hq',ha,true_and]
    have eq : {x : ℝ | a.Coprime q ∧ |x-((a:ℝ)/q+k)|≤w/((q:ℝ)*n)} =
        {x : ℝ | |x-((a:ℝ)/q+k)|≤w/((q:ℝ)*n)} := by
      ext t
      exact ⟨And.right,fun ht => ⟨hc,ht⟩⟩
    rw [eq]
    exact (isClosed_le (f:=fun t : ℝ => |t-((a:ℝ)/q+k)|)
      (g:=fun _ => w/((q:ℝ)*n)) (by fun_prop) continuous_const).measurableSet
  · have eq : {t : ℝ | 1≤q ∧ q≤105 ∧ a<q ∧ a.Coprime q ∧
          |t-((a:ℝ)/q+k)|≤w/((q:ℝ)*n)} = ∅ := by
      ext t
      simp only [Set.mem_setOf_eq,Set.mem_empty_iff_false,iff_false]
      rintro ⟨h,h',j,j',_⟩
      exact c ⟨h,h',j,j'⟩
    rw [eq]
    exact MeasurableSet.empty

set_option maxRecDepth 6000 in
set_option maxHeartbeats 1000000 in
def indices : Finset (ℕ × ℕ) :=
  ((Icc 1 105) ×ˢ (range 105)).filter (fun p => p.2 < p.1 ∧ p.2.Coprime p.1)

set_option maxRecDepth 6000 in
set_option maxHeartbeats 1000000 in
theorem mem_indices {q a : ℕ} : (q,a)∈indices ↔ 1≤q ∧ q≤105 ∧ a<q ∧ a.Coprime q := by
  simp only [indices,mem_filter,Finset.mem_product,mem_Icc,mem_range]
  omega

set_option maxRecDepth 6000 in
set_option maxHeartbeats 1000000 in
def width (n q : ℕ) (w : ℝ) := w/((q:ℝ)*n)
set_option maxRecDepth 6000 in
set_option maxHeartbeats 1000000 in
def center (q a : ℕ) : ℝ := (a:ℝ)/q
set_option maxRecDepth 6000 in
set_option maxHeartbeats 1000000 in
def leftCenter (q a : ℕ) : ℝ := if a=0 then 1 else center q a
set_option maxRecDepth 6000 in
set_option maxHeartbeats 1000000 in
def right (n q a : ℕ) := Set.Icc (center q a+width n q 105) (center q a+width n q 140)
set_option maxRecDepth 6000 in
set_option maxHeartbeats 1000000 in
def left (n q a : ℕ) := Set.Icc (leftCenter q a-width n q 140) (leftCenter q a-width n q 105)
set_option maxRecDepth 6000 in
set_option maxHeartbeats 1000000 in
def band (n : ℕ) := (Set.Icc (0:ℝ) 1 \ arcs n 105) ∩ arcs n 140

set_option maxRecDepth 6000 in
set_option maxHeartbeats 1000000 in
theorem cover (n : ℕ) (hn : 281 ≤ n) : band n ⊆ ⋃ p∈indices, right n p.1 p.2 ∪ left n p.1 p.2 := by
  rintro t ⟨⟨⟨ht0,ht1⟩,hinner⟩,q,a,k,hq,hqmax,ha,hc,hout⟩
  let x := center q a
  let l := width n q 105
  let u := width n q 140
  have npos : (0:ℝ)<n := by exact_mod_cast (by omega : 0<n)
  have qpos : (0:ℝ)<q := by exact_mod_cast (by omega : 0<q)
  have u0 : 0≤u := by dsimp [u,width]; positivity
  have x0 : 0≤x := by dsimp [x,center]; positivity
  have uq : u<1/(q:ℝ) := by
    have hn' : (140:ℝ)<n := by exact_mod_cast (by omega : 140<n)
    dsimp [u,width]
    apply (div_lt_div_iff₀ (mul_pos qpos npos) qpos).mpr
    nlinarith [mul_lt_mul_of_pos_left hn' qpos]
  have xmax : x+1/(q:ℝ) ≤ 1 := by
    dsimp [x,center]
    rw [← add_div,div_le_one qpos]
    exact_mod_cast (by omega : a+1≤q)
  have u1 : u<1 := by linarith
  change |t-(x+(k:ℝ))|≤u at hout
  have hnear := abs_le.mp hout
  have far : l < |t-(x+(k:ℝ))| := by
    apply lt_of_not_ge
    intro h
    exact hinner ⟨q,a,k,hq,hqmax,ha,hc,h⟩
  have k0 : 0≤k := by
    by_contra! hk
    have kk : (k:ℝ)≤-1 := by exact_mod_cast (by omega : k≤-1)
    linarith [hnear.2]
  have k1 : k≤1 := by
    by_contra! hk
    have kk : (2:ℝ)≤k := by exact_mod_cast (by omega : 2≤k)
    linarith [hnear.1]
  have hi : (q,a)∈indices := mem_indices.mpr ⟨hq,hqmax,ha,hc⟩
  simp only [Set.mem_iUnion]
  refine ⟨(q,a),hi,?_⟩
  obtain rfl | rfl : k=0 ∨ k=1 := by omega
  · simp only [Int.cast_zero,add_zero] at hnear far
    by_cases hx : x≤t
    · left
      rw [abs_of_nonneg (sub_nonneg.mpr hx)] at far
      change x+l ≤ t ∧ t ≤ x+u
      constructor <;> linarith [hnear.2]
    · right
      have ha0 : a≠0 := by
        rintro rfl
        simp [x,center] at hx
        linarith
      rw [abs_of_neg (sub_neg.mpr (lt_of_not_ge hx))] at far
      change leftCenter q a-u≤t ∧ t≤leftCenter q a-l
      simp only [leftCenter,if_neg ha0]
      change x-u≤t ∧ t≤x-l
      constructor <;> linarith [hnear.1]
  · simp only [Int.cast_one] at hnear far
    have az : a=0 := by
      by_contra! hh
      have ax : 1/(q:ℝ) ≤ x := div_le_div_of_nonneg_right
        (by exact_mod_cast (by omega : 1≤a)) qpos.le
      linarith [hnear.1]
    subst a
    have zx : x=0 := by simp [x,center]
    rw [zx,zero_add,abs_of_nonpos (sub_nonpos.mpr ht1)] at far
    right
    change leftCenter q 0-u≤t ∧ t≤leftCenter q 0-l
    change 1-u≤t ∧ t≤1-l
    constructor <;> linarith [hnear.1]

set_option maxRecDepth 6000 in
set_option maxHeartbeats 1000000 in
theorem integral_le (n : ℕ) (hn : 281≤n) (f : ℝ → ℝ) (hf : Continuous f)
    (hnn : ∀ t, 0≤f t) (hp : Function.Periodic f 1) :
    (∫ t in band n, f t) ≤ ∑ p∈indices, ∫ t in (width n p.1 105)..(width n p.1 140),
      f (center p.1 p.2+t)+f (center p.1 p.2-t) := by
  let I := fun p : ℕ×ℕ => right n p.1 p.2 ∪ left n p.1 p.2
  have mi (p) : MeasurableSet (I p) := measurableSet_Icc.union measurableSet_Icc
  have integ (p) : IntegrableOn f (I p) := hf.integrableOn_Icc.union hf.integrableOn_Icc
  have nonneg {s : Set ℝ} : 0 ≤ᵐ[volume.restrict s] f := Filter.Eventually.of_forall hnn
  have union_bound (s t : Set ℝ) (mt : MeasurableSet t) (hs : IntegrableOn f s)
      (ht : IntegrableOn f t) : (∫ x in s∪t, f x) ≤ (∫ x in s, f x)+(∫ x in t, f x) := by
    have eq : s∪t=(s\t)∪t := by ext x; simp
    rw [eq,setIntegral_union disjoint_sdiff_self_left mt (hs.mono_set Set.sdiff_subset) ht]
    have sub : s\t ⊆ s := Set.sdiff_subset
    have le : (∫ x in s\t, f x) ≤ ∫ x in s, f x :=
      setIntegral_mono_set hs nonneg (Filter.Eventually.of_forall sub)
    linarith
  have finite_bound (P : Finset (ℕ×ℕ)) :
      (∫ x in ⋃ p∈P, I p, f x) ≤ ∑ p∈P, ∫ x in I p, f x := by
    classical
    induction P using Finset.induction_on with
    | empty => simp
    | insert j P hj ih =>
      rw [Finset.set_biUnion_insert,Finset.sum_insert hj]
      exact (union_bound _ _ (Finset.measurableSet_biUnion P (fun i _ => mi i)) (integ j)
        (integrableOn_finset_iUnion.mpr (fun i _ => integ i))).trans (add_le_add le_rfl ih)
  calc
    _ ≤ ∫ x in ⋃ p∈indices, I p, f x := setIntegral_mono_set
      (integrableOn_finset_iUnion.mpr (fun i _ => integ i)) nonneg (Filter.Eventually.of_forall (cover n hn))
    _ ≤ _ := finite_bound indices
    _ ≤ _ := by
      apply sum_le_sum
      rintro ⟨q,a⟩ hqa
      have hq := (mem_indices.mp hqa).1
      let l := width n q 105
      let u := width n q 140
      let x := center q a
      let y := leftCenter q a
      have order : l≤u := div_le_div_of_nonneg_right (by norm_num) (by positivity)
      have shift (t : ℝ) : f (y-t)=f (x-t) := by
        by_cases az : a=0
        · subst a
          simpa [x,y,center,leftCenter,sub_eq_add_neg,add_comm] using hp (-t)
        · simp [x,y,leftCenter,az]
      have hr : (∫ s in right n q a, f s)=∫ t in l..u, f (x+t) := by
        rw [intervalIntegral.integral_comp_add_left,intervalIntegral.integral_of_le (by linarith)]
        exact integral_Icc_eq_integral_Ioc
      have hl : (∫ s in left n q a, f s)=∫ t in l..u, f (x-t) := by
        simp_rw [← shift]
        rw [intervalIntegral.integral_comp_sub_left,intervalIntegral.integral_of_le (by linarith)]
        exact integral_Icc_eq_integral_Ioc
      change (∫ s in right n q a ∪ left n q a, f s) ≤ ∫ t in l..u, f (x+t)+f (x-t)
      have cr : Continuous (fun t : ℝ => f (x+t)) := hf.comp (continuous_const.add continuous_id)
      have cl : Continuous (fun t : ℝ => f (x-t)) := hf.comp (continuous_const.sub continuous_id)
      rw [intervalIntegral.integral_add (cr.intervalIntegrable l u) (cl.intervalIntegrable l u),←hr,←hl]
      exact union_bound _ _ measurableSet_Icc hf.integrableOn_Icc hf.integrableOn_Icc

end GoldbachCollarCover

theorem Conjectures.Goldbach.FiniteCollarPeriodicCover :
    ∀ n : ℕ, 281≤n → ∀ f : ℝ→ℝ, Continuous f → (∀ t, 0≤f t) → Function.Periodic f 1 →
    (∫ t in GoldbachCollarCover.band n, f t) ≤
      ∑ p∈GoldbachCollarCover.indices, ∫ t in (GoldbachCollarCover.width n p.1 105)..(GoldbachCollarCover.width n p.1 140),
        f (GoldbachCollarCover.center p.1 p.2+t)+f (GoldbachCollarCover.center p.1 p.2-t) :=
  GoldbachCollarCover.integral_le

end

end

section

noncomputable section
open MeasureTheory Finset
open scoped Interval
namespace GoldbachCollarSigned
open GoldbachCollarBmor GoldbachCollarCover


set_option maxRecDepth 12000 in
set_option maxHeartbeats 1400000 in
private theorem scont (n : ℕ) : Continuous (S n) := by
  unfold S E
  fun_prop

set_option maxRecDepth 12000 in
set_option maxHeartbeats 1400000 in
private theorem sper (n : ℕ) : Function.Periodic (S n) 1 := by
  intro t
  apply sum_congr rfl
  intro k hk
  congr 1
  have h : E ((k:ℝ)*(t+1))=E ((k:ℝ)*t)*E (k:ℝ) := by
    unfold E
    rw [← Complex.exp_add]
    congr 1
    push_cast
    ring
  have ht : E (k:ℝ)=1 := by
    unfold E
    rw [show (((2*Real.pi*(k:ℝ):ℝ):ℂ)*Complex.I) = (k:ℕ)*(2*Real.pi*Complex.I) by push_cast; ring,
      Complex.exp_nat_mul,Complex.exp_two_pi_mul_I,one_pow]
  rw [h,ht,mul_one]

set_option maxRecDepth 12000 in
set_option maxHeartbeats 1400000 in
private theorem index_sum (f : ℕ→ℕ→ℝ) : (∑ p∈indices, f p.1 p.2) =
    ∑ q∈Icc 1 105, ∑ i∈A q, f q i := by
  rw [indices,sum_filter,sum_product]
  apply sum_congr rfl
  intro q hq
  change (∑ a∈range 105, if a<q ∧ a.Coprime q then f q a else 0)=_
  rw [← sum_filter]
  have eq : (range 105).filter (fun a => a<q ∧ a.Coprime q)=A q := by
    ext a
    simp only [A,mem_filter,mem_range]
    have := (mem_Icc.mp hq).2
    omega
  rw [eq]

set_option maxRecDepth 12000 in
set_option maxHeartbeats 1400000 in
private theorem v_signal (n : ℕ) (t : ℝ) :
    V n t = FiniteCollarModelEnergy.signal n t := by
  have hi : Icc 1 n=Ioc 0 n := by ext k; simp only [mem_Icc,mem_Ioc]; omega
  simp [V,E,FiniteCollarModelEnergy.signal,FiniteCollarModelEnergy.wave,
    B13BilateralVaughanReductionProof.DyadicMixedB4Geometric.wave,
    B13BilateralVaughanReductionProof.DyadicMixedB4Geometric.phase,hi]

set_option maxRecDepth 12000 in
set_option maxHeartbeats 1400000 in
private def coeff (q : ℕ) : ℝ := ((ArithmeticFunction.moebius q:ℤ):ℝ)^2/(q.totient:ℝ)^2

set_option maxRecDepth 12000 in
set_option maxHeartbeats 1400000 in
private theorem model_sq (n q : ℕ) (t : ℝ) : ‖M n q t‖^2=coeff q*‖FiniteCollarModelEnergy.signal n t‖^2 := by
  have hp : ‖((ArithmeticFunction.moebius q:ℤ):ℂ)‖ = |((ArithmeticFunction.moebius q:ℤ):ℝ)| := by
    rw [← Complex.ofReal_intCast,Complex.norm_real,Real.norm_eq_abs]
  rw [M,norm_mul,norm_div,hp,Complex.norm_natCast,mul_pow,div_pow,sq_abs,v_signal]
  rfl

set_option maxRecDepth 12000 in
set_option maxHeartbeats 1400000 in
private theorem coeff_card (q : ℕ) (hq : 1≤q) :
    ((A q).card:ℝ)*coeff q=FiniteCollarModelEnergy.weight q := by
  have card : (A q).card=q.totient := by
    rw [Nat.totient_eq_card_coprime]
    apply congrArg Finset.card
    exact filter_congr (fun a _ => Nat.coprime_comm)
  have φ : (q.totient:ℝ)≠0 := by exact_mod_cast (Nat.totient_pos.mpr hq).ne'
  rw [card]
  unfold coeff FiniteCollarModelEnergy.weight
  field_simp

set_option maxRecDepth 12000 in
set_option maxHeartbeats 1400000 in
/-- A rational upper bound for the model's contribution at denominator q, divided by n. -/
private def modelBudget (q : ℕ) : ℚ :=
  ((ArithmeticFunction.moebius q:ℤ):ℚ)^2/q.totient*q *
    (2/(157/50:ℚ)^2*(1/105-1/140))

set_option maxRecDepth 12000 in
set_option maxHeartbeats 1400000 in
/-- Round the best Young weight up to a multiple of 1/64. Vanishing model
coefficients use a large weight, so their contribution is almost exactly the error. -/
private def tuning (q : ℕ) : ℚ :=
  if modelBudget q = 0 then 1024 else
    let ratio := 4096*GoldbachCollarError.rationalBudget q / modelBudget q
    (Nat.sqrt (ratio.num.toNat / ratio.den) + 1 : ℕ) / (64:ℚ)

set_option maxRecDepth 12000 in
set_option maxHeartbeats 1400000 in
private theorem tuning_pos (q : ℕ) : 0 < tuning q := by
  unfold tuning
  split <;> positivity

set_option maxRecDepth 12000 in
set_option maxHeartbeats 1400000 in
private def modelFactor (q : ℕ) : ℝ := 1+(tuning q:ℝ)
set_option maxRecDepth 12000 in
set_option maxHeartbeats 1400000 in
private def errorFactor (q : ℕ) : ℝ := 1+1/(tuning q:ℝ)

set_option maxRecDepth 12000 in
set_option maxHeartbeats 1400000 in
private def charge (q : ℕ) : ℚ :=
  (1+tuning q)*modelBudget q+(1+1/tuning q)*GoldbachCollarError.rationalBudget q

set_option maxRecDepth 12000 in
set_option maxHeartbeats 1400000 in
private theorem numericCharge : (∑ q∈Icc 1 105, charge q) < 9/40 := by
  set_option maxRecDepth 16000 in
  decide +kernel

set_option maxRecDepth 12000 in
set_option maxHeartbeats 1400000 in
private theorem split_sq (q : ℕ) (z m : ℂ) :
    ‖z‖^2 ≤ modelFactor q*‖m‖^2+errorFactor q*‖z-m‖^2 := by
  let s : ℝ := tuning q
  have hs : 0 < s := by
    change 0 < (tuning q : ℝ)
    exact_mod_cast tuning_pos q
  have h := norm_add_le m (z-m)
  rw [add_sub_cancel] at h
  have hsquare := pow_le_pow_left₀ (norm_nonneg z) h 2
  have hyoung : 2*‖m‖*‖z-m‖ ≤ s*‖m‖^2+‖z-m‖^2/s := by
    apply (mul_le_mul_iff_of_pos_right hs).mp
    rw [add_mul,div_mul_cancel₀ _ hs.ne']
    nlinarith only [sq_nonneg (s*‖m‖-‖z-m‖)]
  change ‖z‖^2 ≤ (1+s)*‖m‖^2+(1+1/s)*‖z-m‖^2
  rw [add_mul (1:ℝ) (1/s),one_div,←div_eq_inv_mul]
  linarith only [hyoung,hsquare]

set_option maxRecDepth 12000 in
set_option maxHeartbeats 1400000 in
private def I (n q : ℕ) (f : ℝ→ℝ) := ∫ t in (width n q 105)..(width n q 140), f t
set_option maxRecDepth 12000 in
set_option maxHeartbeats 1400000 in
private def main (n q a : ℕ) := I n q fun t =>
  ‖S n (center q a+t)‖^2+‖S n (center q a-t)‖^2
set_option maxRecDepth 12000 in
set_option maxHeartbeats 1400000 in
private def err (n q a : ℕ) := I n q fun t =>
  GoldbachCollarError.error n q a t+GoldbachCollarError.error n q a (-t)
set_option maxRecDepth 12000 in
set_option maxHeartbeats 1400000 in
private def model (n q : ℕ) := coeff q*I n q (FiniteCollarModelEnergy.sides n)

set_option maxRecDepth 12000 in
set_option maxHeartbeats 1400000 in
private theorem per (n q a : ℕ) : main n q a ≤ modelFactor q*model n q+errorFactor q*err n q a := by
  let x := center q a
  let g := fun t : ℝ => ‖S n (x+t)‖^2+‖S n (x-t)‖^2
  let v := FiniteCollarModelEnergy.sides n
  let e := fun t : ℝ => GoldbachCollarError.error n q a t+GoldbachCollarError.error n q a (-t)
  have sp : Continuous (fun t : ℝ => S n (x+t)) := (scont n).comp (continuous_const.add continuous_id)
  have sm : Continuous (fun t : ℝ => S n (x-t)) := (scont n).comp (continuous_const.sub continuous_id)
  have cg : Continuous g := (sp.norm.pow 2).add (sm.norm.pow 2)
  have cv : Continuous v := by
    change Continuous (fun t : ℝ => ‖FiniteCollarModelEnergy.signal n t‖^2+‖FiniteCollarModelEnergy.signal n (-t)‖^2)
    simp_rw [←v_signal]
    unfold V E
    fun_prop
  have ce : Continuous e := by
    unfold e GoldbachCollarError.error S M V E
    fun_prop
  have order : width n q 105≤width n q 140 := div_le_div_of_nonneg_right (by norm_num) (by positivity)
  have pt (t : ℝ) : g t ≤ (modelFactor q*coeff q)*v t+errorFactor q*e t := by
    have h1 := split_sq q (S n (x+t)) (M n q t)
    have h2 := split_sq q (S n (x+(-t))) (M n q (-t))
    rw [model_sq] at h1 h2
    dsimp only [g,v,FiniteCollarModelEnergy.sides,e,GoldbachCollarError.error,x,center] at h1 h2 ⊢
    simp only [sub_eq_add_neg] at h1 h2 ⊢
    linarith only [h1,h2]
  change I n q g ≤ modelFactor q*(coeff q*I n q v)+errorFactor q*I n q e
  unfold I
  calc
    _ ≤ ∫ t in (width n q 105)..(width n q 140), (modelFactor q*coeff q)*v t+errorFactor q*e t :=
      intervalIntegral.integral_mono_on order (cg.intervalIntegrable ..)
        (((continuous_const.mul cv).add (continuous_const.mul ce)).intervalIntegrable ..) (fun t _ => pt t)
    _ = _ := by
      have cv' : Continuous (fun t : ℝ => (modelFactor q*coeff q)*v t) := continuous_const.mul cv
      have ce' : Continuous (fun t : ℝ => errorFactor q*e t) := continuous_const.mul ce
      rw [intervalIntegral.integral_add (cv'.intervalIntegrable (width n q 105) (width n q 140))
        (ce'.intervalIntegrable (width n q 105) (width n q 140)),
        intervalIntegral.integral_const_mul,intervalIntegral.integral_const_mul]
      ring

set_option maxRecDepth 12000 in
set_option maxHeartbeats 1400000 in
private theorem denominator (h : BMOR) (n q : ℕ) (hn : 4000000000000000000 ≤ n)
    (hq : 1 ≤ q) (hmax : q ≤ 105) :
    (∑ i∈A q, main n q i) ≤ (n:ℝ)*(charge q:ℝ) := by
  have hqn : 140000 ≤ q*n := (show 140000≤n by omega).trans (Nat.le_mul_of_pos_left n hq)
  have hc : (140000:ℝ) ≤ (q:ℝ)*n := by exact_mod_cast hqn
  have castB : (modelBudget q:ℝ) = FiniteCollarModelEnergy.weight q*q*
      (2/(157/50:ℝ)^2*(1/105-1/140)) := by
    unfold modelBudget FiniteCollarModelEnergy.weight
    push_cast
    ring
  have hm : (∑ _i∈A q, model n q) ≤ (n:ℝ)*(modelBudget q:ℝ) := by
    simp only [sum_const,nsmul_eq_mul,model,←mul_assoc,coeff_card q hq]
    calc
      _ ≤ FiniteCollarModelEnergy.weight q*(((q:ℝ)*n)*(2/(157/50:ℝ)^2*(1/105-1/140))) :=
        mul_le_mul_of_nonneg_left (FiniteCollarModelEnergy.sharp_integral n _ hc)
          (by unfold FiniteCollarModelEnergy.weight; positivity)
      _ = _ := by rw [castB]; ring
  have he : (∑ i∈A q, err n q i) ≤ (n:ℝ)*(GoldbachCollarError.rationalBudget q:ℝ) :=
    GoldbachCollarError.collar_le_rational h n q hn hq hmax
  have ht : 0 < (tuning q:ℝ) := by exact_mod_cast tuning_pos q
  have hmf : 0 ≤ modelFactor q := by unfold modelFactor; positivity
  have hef : 0 ≤ errorFactor q := by unfold errorFactor; positivity
  calc
    _ ≤ ∑ i∈A q, (modelFactor q*model n q+errorFactor q*err n q i) :=
      sum_le_sum fun i _ => per n q i
    _ = modelFactor q*(∑ _i∈A q, model n q)+errorFactor q*(∑ i∈A q, err n q i) := by
      rw [sum_add_distrib,←mul_sum,←mul_sum]
    _ ≤ modelFactor q*((n:ℝ)*(modelBudget q:ℝ))+
        errorFactor q*((n:ℝ)*(GoldbachCollarError.rationalBudget q:ℝ)) :=
      by exact add_le_add (mul_le_mul_of_nonneg_left hm hmf) (mul_le_mul_of_nonneg_left he hef)
    _ = _ := by
      unfold charge modelFactor errorFactor
      push_cast
      ring

set_option maxRecDepth 12000 in
set_option maxHeartbeats 1400000 in
theorem band_energy (h : BMOR) (n : ℕ) (hn : 4000000000000000000≤n) :
    (∫ t in band n, ‖S n t‖^2) < (9/40:ℝ)*n := by
  have fper : Function.Periodic (fun t => ‖S n t‖^2) 1 :=
    fun t => congrArg (fun z : ℂ => ‖z‖^2) (sper n t)
  have hc := integral_le n (by omega) (fun t => ‖S n t‖^2) ((scont n).norm.pow 2)
    (fun t => sq_nonneg _) fper
  change _ ≤ ∑ p∈indices, main n p.1 p.2 at hc
  rw [index_sum] at hc
  have charge_bound : (∑ q∈Icc 1 105, (charge q:ℝ)) < (9/40:ℝ) := by
    have r : (((∑ q∈Icc 1 105, charge q):ℚ):ℝ) < ((9/40:ℚ):ℝ) := by
      exact_mod_cast numericCharge
    simpa only [Rat.cast_sum,Rat.cast_div,Rat.cast_ofNat] using r
  have hn0 : (0:ℝ)<n := by exact_mod_cast (by omega : 0<n)
  calc
    _ ≤ ∑ q∈Icc 1 105, ∑ i∈A q, main n q i := hc
    _ ≤ ∑ q∈Icc 1 105, (n:ℝ)*(charge q:ℝ) :=
      sum_le_sum fun q hq => denominator h n q hn (mem_Icc.mp hq).1 (mem_Icc.mp hq).2
    _ = _ := (mul_sum ..).symm
    _ < _ := (mul_lt_mul_of_pos_left charge_bound hn0).trans_eq (mul_comm ..)

set_option maxRecDepth 12000 in
set_option maxHeartbeats 1400000 in
def integrand (n : ℕ) (t : ℝ) := (S n t)^2*E (-(n:ℝ)*t)
set_option maxRecDepth 12000 in
set_option maxHeartbeats 1400000 in
def off (n : ℕ) (w : ℝ) := Set.Icc (0:ℝ) 1 \ arcs n w
set_option maxRecDepth 12000 in
set_option maxHeartbeats 1400000 in
def signedOff (n : ℕ) (w : ℝ) := (∫ t in off n w, integrand n t).re

set_option maxRecDepth 12000 in
set_option maxHeartbeats 1400000 in
theorem signed (h : BMOR) (n : ℕ) (hn : 4000000000000000000≤n) :
    -(9/40:ℝ)*n < (∫ t in band n, integrand n t).re ∧
      (-(63/40:ℝ)*n ≤ signedOff n 140 → -(9/5:ℝ)*n ≤ signedOff n 105) := by
  let f := integrand n
  have z : (∫ t in band n, ‖f t‖) = ∫ t in band n, ‖S n t‖^2 := by
    congr 1
    funext t
    simp only [f,integrand,norm_mul,norm_pow,E,Complex.norm_exp_ofReal_mul_I,mul_one]
  have nr := norm_integral_le_integral_norm (μ:=volume.restrict (band n)) f
  rw [z] at nr
  have hre : -(‖∫ t in band n, f t‖) ≤ (∫ t in band n, f t).re :=
    (neg_le_neg (Complex.abs_re_le_norm _)).trans (neg_abs_le _)
  have hb := band_energy h n hn
  have lower : -(9/40:ℝ)*n < (∫ t in band n, f t).re := by linarith only [nr,hre,hb]
  refine ⟨lower,?_⟩
  intro outer
  have sub : arcs n 105 ⊆ arcs n 140 := by
    rintro t ⟨q,a,k,hq,hq',ha,hc,ht⟩
    exact ⟨q,a,k,hq,hq',ha,hc,ht.trans (div_le_div_of_nonneg_right (by norm_num) (by positivity))⟩
  have eq : off n 105 \ arcs n 140 = off n 140 := by
    ext x
    change ((x∈Set.Icc (0:ℝ) 1 ∧ x∉arcs n 105) ∧ x∉arcs n 140) ↔
      x∈Set.Icc (0:ℝ) 1 ∧ x∉arcs n 140
    exact ⟨fun hx => ⟨hx.1.1,hx.2⟩,fun hx => ⟨⟨hx.1,fun h => hx.2 (sub h)⟩,hx.2⟩⟩
  have cf : Continuous f := by unfold f integrand S E; fun_prop
  have part := integral_inter_add_sdiff (μ:=volume) (f:=f) (s:=off n 105) (measurable_arcs n 140)
    (cf.integrableOn_Icc.mono_set Set.sdiff_subset)
  rw [eq] at part
  change (∫ t in band n,f t)+(∫ t in off n 140,f t)=∫ t in off n 105,f t at part
  have re := congrArg Complex.re part
  change _+_=(∫ t in off n 105,f t).re at re
  change -(63/40:ℝ)*n ≤ (∫ t in off n 140,f t).re at outer
  change -(9/5:ℝ)*n ≤ (∫ t in off n 105,f t).re
  linarith only [lower,outer,re]

end GoldbachCollarSigned

theorem Conjectures.Goldbach.FiniteCollarSignedBudget :
    GoldbachCollarBmor.BMOR → ∀ n : ℕ, 4000000000000000000≤n →
    (∫ t in GoldbachCollarCover.band n, ‖GoldbachCollarBmor.S n t‖^2) < (9/40:ℝ)*n ∧
    -(9/40:ℝ)*n < (∫ t in GoldbachCollarCover.band n, GoldbachCollarSigned.integrand n t).re ∧
    (-(63/40:ℝ)*n ≤ GoldbachCollarSigned.signedOff n 140 →
      -(9/5:ℝ)*n ≤ GoldbachCollarSigned.signedOff n 105) :=
  fun h n hn => ⟨GoldbachCollarSigned.band_energy h n hn, GoldbachCollarSigned.signed h n hn⟩

end

end
