import Mathlib
import Conjectures.Goldbach.FiniteWeightedSieveSupportedRegion

/-!
For q ≥ 5001, primality implies coprimality with 229!. For small denominators
round each reciprocal square up in units of 10⁻¹². Above 300000 bound the sum
over all integers by a telescoping sum. This also bounds any finite subfamily.
-/
namespace FiniteSievePrimeReciprocalTable


set_option maxHeartbeats 0 in
set_option maxRecDepth 12000 in
def weight (q : ℕ) : ℕ :=
  if q.Coprime (Nat.factorial 229) then 10^12/(q^2)+1 else 0

set_option maxHeartbeats 0 in
set_option maxRecDepth 12000 in
private def cost (j : ℕ) : ℕ :=
  ((List.range 250).map (fun i => weight (5001+250*j+i))).sum

set_option maxHeartbeats 0 in
set_option maxRecDepth 12000 in
private theorem finite_receipt :
    ((List.range 1180).map cost).sum=20986273 := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 12000 in
private theorem list_sum (f : ℕ → ℕ) (n : ℕ) :
    (∑ i∈Finset.range n, f i) = ((List.range n).map f).sum := by
  induction n with
  | zero => simp
  | succ n ih => simp [Finset.sum_range_succ,List.range_succ,ih]

set_option maxHeartbeats 0 in
set_option maxRecDepth 12000 in
private theorem grouped (f : ℕ → ℕ) (k m a : ℕ) :
    (∑ i∈Finset.range (k*m), f (a+i)) =
      ∑ j∈Finset.range k, ∑ i∈Finset.range m, f (a+m*j+i) := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [Nat.succ_mul,Finset.sum_range_add,Finset.sum_range_succ,ih]
    simp only [Nat.mul_comm m k, Nat.add_assoc]

set_option maxHeartbeats 0 in
set_option maxRecDepth 12000 in
private theorem table_sum :
    (∑ q∈Finset.Ico 5001 300001, weight q)=20986273 := by
  rw [Finset.sum_Ico_eq_sum_range]
  change (∑ i∈Finset.range (1180*250), weight (5001+i))=_
  rw [grouped weight 1180 250 5001]
  calc
    _ = ∑ j∈Finset.range 1180, cost j := Finset.sum_congr rfl (fun j _ => list_sum _ _)
    _ = _ := (list_sum cost 1180).trans finite_receipt

set_option maxHeartbeats 0 in
set_option maxRecDepth 12000 in
private theorem rounded {q : ℕ} (hq : q.Prime) (h : 5001 ≤ q) :
    1/(q:ℝ)^2 ≤ (weight q:ℝ)/10^12 := by
  have hcop := hq.coprime_factorial_of_lt (by omega : 229<q)
  have hq0 := hq.pos
  have hpow : 0<q^2 := by positivity
  have hr := Nat.mod_lt (10^12) hpow
  have hd := Nat.mod_add_div (10^12) (q^2)
  have hi : 10^12 ≤ (10^12/q^2+1)*q^2 := by rw [Nat.add_mul,Nat.one_mul,Nat.mul_comm _ (q^2)]; omega
  rw [weight, if_pos hcop]
  apply (div_le_div_iff₀ (by positivity) (by norm_num)).mpr
  rw [one_mul]
  exact_mod_cast hi

set_option maxHeartbeats 0 in
set_option maxRecDepth 12000 in
private theorem tail (m k : ℕ) (hm : 0 < m) :
    (∑ i∈Finset.range k, 1/((m+i+1:ℕ):ℝ)^2) ≤ 1/(m:ℝ)-1/((m+k:ℕ):ℝ) := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [Finset.sum_range_succ]
    have ht : (0:ℝ) < (m+k:ℕ) := by exact_mod_cast (by omega : 0 < m+k)
    have hs : 1/((m+k+1:ℕ):ℝ)^2 ≤ 1/((m+k:ℕ):ℝ)-1/((m+k+1:ℕ):ℝ) := by
      push_cast
      push_cast at ht
      field_simp
      nlinarith
    change (∑ i∈Finset.range k, 1/((m+i+1:ℕ):ℝ)^2) + 1/((m+k+1:ℕ):ℝ)^2 ≤
      1/(m:ℝ)-1/((m+k+1:ℕ):ℝ)
    linarith

set_option maxHeartbeats 0 in
set_option maxRecDepth 12000 in
theorem reciprocal (P : Finset ℕ) (hP : ∀ q∈P, q.Prime ∧ 5001 ≤ q) :
    (∑ q∈P, 1/(q:ℝ)^2) ≤ (72958819:ℝ)/3000000000000 := by
  classical
  let head := P.filter (fun q => q < 300001)
  let rest := P.filter (fun q => ¬q < 300001)
  have head_sub : head ⊆ Finset.Ico 5001 300001 := fun q hq =>
    Finset.mem_Ico.mpr ⟨(hP _ (Finset.mem_filter.mp hq).1).2,(Finset.mem_filter.mp hq).2⟩
  have head_cost : (∑ q∈head, 1/(q:ℝ)^2) ≤ 20986273/(10:ℝ)^12 := by
    calc
      _ ≤ ∑ q∈head, (weight q:ℝ)/10^12 := Finset.sum_le_sum fun q hq =>
        rounded (hP _ (Finset.mem_filter.mp hq).1).1 (hP _ (Finset.mem_filter.mp hq).1).2
      _ = ((∑ q∈head, weight q : ℕ):ℝ)/10^12 := by simp [Finset.sum_div]
      _ ≤ _ := by
        apply div_le_div_of_nonneg_right _ (by norm_num)
        exact_mod_cast (Finset.sum_le_sum_of_subset head_sub).trans_eq table_sum
  let k := P.sup id+1
  have sub : rest ⊆ Finset.Ico 300001 (300001+k) := by
    intro q hq
    obtain ⟨hmem,high⟩ := Finset.mem_filter.mp hq
    have hle : q ≤ P.sup id := Finset.le_sup (f:=id) hmem
    exact Finset.mem_Ico.mpr ⟨by omega,by dsimp [k]; omega⟩
  have rest_cost : (∑ q∈rest, 1/(q:ℝ)^2) ≤ 1/300000 := by
    calc
      _ ≤ ∑ q∈Finset.Ico 300001 (300001+k), 1/(q:ℝ)^2 :=
        Finset.sum_le_sum_of_subset_of_nonneg sub (fun _ _ _ => by positivity)
      _ = ∑ i∈Finset.range k, 1/((300000+i+1:ℕ):ℝ)^2 := by
        rw [Finset.sum_Ico_eq_sum_range]
        simp only [Nat.add_sub_cancel_left]
        apply Finset.sum_congr rfl
        intro i _
        rw [show 300001+i = 300000+i+1 by omega]
      _ ≤ 1/(300000:ℝ)-1/((300000+k:ℕ):ℝ) := tail _ _ (by decide)
      _ ≤ _ := sub_le_self _ (by positivity)
  have part : (∑ q∈head, 1/(q:ℝ)^2)+(∑ q∈rest, 1/(q:ℝ)^2) = ∑ q∈P, 1/(q:ℝ)^2 :=
    Finset.sum_filter_add_sum_filter_not P _ _
  linarith

end FiniteSievePrimeReciprocalTable

theorem Conjectures.Goldbach.FiniteSievePrimeReciprocalTable :
    ∀ P : Finset ℕ, (∀ q∈P, Nat.Prime q ∧ 5001 ≤ q) →
      (∑ q∈P, 1/(q:ℝ)^2) ≤ (72958819:ℝ)/3000000000000 :=
  FiniteSievePrimeReciprocalTable.reciprocal

noncomputable section
open Finset
namespace SiftedSquareLoss

private theorem phi_value : (30030:ℕ).totient=5760 := by
  change Nat.totient (2*(3*(5*(7*(11*13)))))=5760
  rw [Nat.totient_mul (by decide : Nat.Coprime 2 (3*(5*(7*(11*13))))),
      Nat.totient_mul (by decide : Nat.Coprime 3 (5*(7*(11*13)))),
      Nat.totient_mul (by decide : Nat.Coprime 5 (7*(11*13))),
      Nat.totient_mul (by decide : Nat.Coprime 7 (11*13)),
      Nat.totient_mul (by decide : Nat.Coprime 11 13)]
  norm_num [Nat.totient_prime (by decide : Nat.Prime 2), Nat.totient_prime (by decide : Nat.Prime 3),
    Nat.totient_prime (by decide : Nat.Prime 5), Nat.totient_prime (by decide : Nat.Prime 7),
    Nat.totient_prime (by decide : Nat.Prime 11), Nat.totient_prime (by decide : Nat.Prime 13)]

private theorem one_square (n q : ℕ) (A : Finset ℕ)
    (ha : ∀ p∈A, p<n ∧ Nat.Coprime 30030 (n-p)) :
    ((A.filter (fun p => q^2 ∣ n-p)).card:ℝ) ≤
      (5760/30030:ℝ)*((n:ℝ)/(q:ℝ)^2)+5760 := by
  let T := A.filter (fun p => q^2∣n-p)
  let m (p : ℕ) := (n-p)/q^2
  let f (p : ℕ) := (m p/30030,m p % 30030)
  let U := (range 30030).filter (Nat.Coprime 30030)
  let K := n/q^2/30030
  have maps : Set.MapsTo f (T : Set ℕ) ((range (K+1) ×ˢ U : Finset (ℕ × ℕ)) : Set (ℕ × ℕ)) := by
    intro p hp
    obtain ⟨mem,div⟩ := mem_filter.mp hp
    have h : Nat.Coprime 30030 (m p) := (ha p mem).2.coprime_dvd_right (Nat.div_dvd_of_dvd div)
    have hm : m p≤n/q^2 := Nat.div_le_div_right (Nat.sub_le n p)
    apply mem_product.mpr
    refine ⟨mem_range.mpr (Nat.lt_succ_of_le (Nat.div_le_div_right hm)),mem_filter.mpr ⟨?_,?_⟩⟩
    · exact mem_range.mpr (Nat.mod_lt _ (by decide))
    · change Nat.gcd 30030 (m p % 30030)=1
      rw [Nat.gcd_comm,←Nat.gcd_rec]
      exact h
  have inj : Set.InjOn f (T : Set ℕ) := by
    intro p hp r hr eq
    have d := congrArg Prod.fst eq
    have t := congrArg Prod.snd eq
    change m p/30030=m r/30030 at d
    change m p % 30030=m r % 30030 at t
    have mq : m p=m r := by
      have a := Nat.mod_add_div (m p) 30030
      have b := Nat.mod_add_div (m r) 30030
      omega
    have hmul := congrArg (fun k => k*q^2) mq
    change (n-p)/q^2*q^2=(n-r)/q^2*q^2 at hmul
    obtain ⟨pm,pd⟩ := mem_filter.mp hp
    obtain ⟨rm,rd⟩ := mem_filter.mp hr
    rw [Nat.div_mul_cancel pd,Nat.div_mul_cancel rd] at hmul
    have := (ha p pm).1
    have := (ha r rm).1
    omega
  have hu : U.card=5760 := (Nat.totient_eq_card_coprime 30030).symm.trans phi_value
  have hc : T.card≤(K+1)*5760 := by
    simpa only [card_product,card_range,hu] using card_le_card_of_injOn f maps inj
  have quot : (K:ℝ)≤(n:ℝ)/(q:ℝ)^2/30030 := by
    have a := (Nat.cast_div_le (α:=ℝ) (m:=n/q^2) (n:=30030))
    have b := (Nat.cast_div_le (α:=ℝ) (m:=n) (n:=q^2))
    push_cast at a b
    exact a.trans (div_le_div_of_nonneg_right b (by norm_num))
  have cast : (T.card:ℝ)≤((K:ℝ)+1)*5760 := by exact_mod_cast hc
  change (T.card:ℝ) ≤ _
  linarith

def z (n : ℕ) := ⌈(n:ℝ)^((1:ℝ)/5)⌉₊
def y (n : ℕ) := max ⌈(n:ℝ)^((1:ℝ)/3)⌉₊ ⌈Real.sqrt ((n:ℝ)/(z n:ℝ))⌉₊

private theorem parameters (n : ℕ) (hn : 4000000000000000000 < n) :
    5001 ≤ z n ∧ z n < y n ∧ n ≤ y n^3 ∧ n ≤ z n*y n^2 := by
  let a := (n:ℝ)^((1:ℝ)/5)
  have nn : (0:ℝ) ≤ n := Nat.cast_nonneg _
  have ha : 0 ≤ a := Real.rpow_nonneg nn _
  have a5 : a^5=(n:ℝ) := by
    dsimp [a]
    rw [← Real.rpow_mul_natCast nn,show (1/5:ℝ)*(5:ℕ)=1 by norm_num,Real.rpow_one]
  have a5000 : (5000:ℝ) < a := by
    by_contra! h
    have h5 := pow_le_pow_left₀ ha h 5
    rw [a5] at h5
    have hi : (4000000000000000000:ℝ) < n := by exact_mod_cast hn
    norm_num at h5
    linarith
  have zlo : 5001 ≤ z n := Nat.add_one_le_ceil_iff.mpr a5000
  have zpos : (0:ℝ) < z n := by exact_mod_cast (by omega : 0 < z n)
  have zhi : (z n:ℝ) < a+1 := Nat.ceil_lt_add_one ha
  have hc : (n:ℝ)^((1:ℝ)/3) ≤ (y n:ℝ) := (Nat.le_ceil _).trans
    (by exact_mod_cast (le_max_left _ _ : ⌈(n:ℝ)^((1:ℝ)/3)⌉₊ ≤ y n))
  have hpow := pow_le_pow_left₀ (Real.rpow_nonneg nn _) hc 3
  rw [← Real.rpow_mul_natCast nn,show (1/3:ℝ)*(3:ℕ)=1 by norm_num,Real.rpow_one] at hpow
  have hzlt : z n < y n := by
    by_contra! h
    have hy : (y n:ℝ) ≤ 2*a := (show (y n:ℝ) ≤ z n by exact_mod_cast h).trans (by linarith)
    have h3 := pow_le_pow_left₀ (Nat.cast_nonneg _) hy 3
    have h2 : 8 < a^2 := by nlinarith [sq_nonneg (a-3)]
    have hgt := mul_lt_mul_of_pos_right h2 (by positivity : 0<a^3)
    nlinarith
  have hs : Real.sqrt ((n:ℝ)/(z n:ℝ)) ≤ (y n:ℝ) := (Nat.le_ceil _).trans
    (by exact_mod_cast (le_max_right _ _ : ⌈Real.sqrt ((n:ℝ)/(z n:ℝ))⌉₊ ≤ y n))
  have hsq := pow_le_pow_left₀ (Real.sqrt_nonneg _) hs 2
  rw [Real.sq_sqrt (div_nonneg nn zpos.le)] at hsq
  have last := (div_le_iff₀ zpos).mp hsq
  exact ⟨zlo,hzlt,by exact_mod_cast hpow,by rw [mul_comm]; exact_mod_cast last⟩

private theorem exp_small : Real.exp (19/5) < 45 := by
  by_contra! h
  have hp := pow_le_pow_left₀ (by norm_num : (0:ℝ) ≤ 45) h 5
  have eq : Real.exp (19/5)^5 = Real.exp 1^19 := by
    rw [← Real.exp_nat_mul,← Real.exp_nat_mul]
    norm_num
  rw [eq] at hp
  have bound := pow_lt_pow_left₀ Real.exp_one_lt_d9 (Real.exp_pos 1).le (by decide : 19≠0)
  norm_num at bound hp
  linarith



private theorem y_bound (n : ℕ) (hn : 4000000000000000000<n)
    (hu : (n:ℝ)<Real.exp (Real.exp (19/5))) : y n≤100000000 := by
  have num : Real.exp (45:ℝ)<50000000000000000000 := by
    have h := pow_lt_pow_left₀ Real.exp_one_lt_d9 (Real.exp_pos 1).le (by decide : 45≠0)
    rw [← Real.exp_nat_mul] at h
    norm_num at h
    linarith
  have lim := hu.trans ((Real.exp_lt_exp.mpr exp_small).trans num)
  have nn : 0≤(n:ℝ) := Nat.cast_nonneg _
  have cub : (n:ℝ)^((1:ℝ)/3)≤100000000 := by
    by_contra! bad
    have h := pow_lt_pow_left₀ bad (by norm_num : (0:ℝ)≤100000000) (by decide : 3≠0)
    rw [← Real.rpow_mul_natCast nn,show (1/3:ℝ)*(3:ℕ)=1 by norm_num,Real.rpow_one] at h
    linarith
  have hz : (5001:ℝ)≤z n := by exact_mod_cast (parameters n hn).1
  have sq : Real.sqrt ((n:ℝ)/(z n:ℝ))≤100000000 := by
    apply Real.sqrt_le_iff.mpr
    refine ⟨by norm_num,(div_le_iff₀ (by linarith : (0:ℝ)<z n)).mpr ?_⟩
    linarith
  exact max_le (Nat.ceil_le.mpr (by exact_mod_cast cub)) (Nat.ceil_le.mpr (by exact_mod_cast sq))

theorem result (n : ℕ) (hn : 4000000000000000000<n) (hu : (n:ℝ)<Real.exp (Real.exp (19/5))) :
    let A := (range (n+1)).filter (fun p => p.Prime ∧ ¬p∣n ∧
      ((Ico 2 (z n)).filter (fun q => Nat.Prime q ∧ q∣n-p))=∅)
    let B := A.filter (fun p => 2≤n-p)
    2<z n ∧ z n<y n ∧ n≤y n^3 ∧ n≤z n*y n^2 ∧
    (∑ q∈(Ico (z n) (y n)).filter Nat.Prime, ((B.filter (fun p => q^2∣n-p)).card:ℝ)) <
      (n:ℝ)/(100*(Real.log n)^2) := by
  intro A B
  obtain ⟨hz,hy,h3,h2⟩ := parameters n hn
  refine ⟨by omega,hy,h3,h2,?_⟩
  have ha : ∀ p∈B, p<n ∧ Nat.Coprime 30030 (n-p) := by
    intro p hp
    obtain ⟨mem,large⟩ := mem_filter.mp hp
    obtain ⟨_,_,_,empty⟩ := mem_filter.mp mem
    refine ⟨by omega,Nat.coprime_of_dvd ?_⟩
    intro r pr dw dv
    have hi : r≤13 := by
      change r ∣ 2*(3*(5*(7*(11*13)))) at dw
      simp only [Nat.Prime.dvd_mul pr] at dw
      rcases dw with h|h|h|h|h|h
      all_goals exact (Nat.le_of_dvd (by decide) h).trans (by decide)
    have hmem : r∈(Ico 2 (z n)).filter (fun q => q.Prime ∧ q∣n-p) :=
      mem_filter.mpr ⟨mem_Ico.mpr ⟨pr.two_le,by omega⟩,pr,dv⟩
    simp only [empty,notMem_empty] at hmem
  let P := (Ico (z n) (y n)).filter Nat.Prime
  have hq : ∀ q∈P, Nat.Prime q ∧ 5001≤q := fun q h =>
    ⟨(mem_filter.mp h).2,hz.trans (mem_Ico.mp (mem_filter.mp h).1).1⟩
  have hs := Conjectures.Goldbach.FiniteSievePrimeReciprocalTable P hq
  have hc : P.card≤100000000 := by
    apply (card_le_card (filter_subset _ _)).trans
    rw [Nat.card_Ico]
    exact (Nat.sub_le _ _).trans (y_bound n hn hu)
  have hcr : (P.card:ℝ)≤100000000 := by exact_mod_cast hc
  have nl : (4000000000000000000:ℝ)<n := by exact_mod_cast hn
  have pos : (0:ℝ)<n := by linarith
  have lp : 0<Real.log n := Real.log_pos (by linarith)
  have lu := ((Real.log_lt_iff_lt_exp pos).mpr hu).trans exp_small
  have ls : (Real.log n)^2≤2025 := by nlinarith [mul_nonneg (sub_nonneg.mpr lu.le) (show 0≤45+Real.log n by linarith)]
  change (∑ q∈P, _) < _
  calc
    _ ≤ ∑ q∈P, ((5760/30030:ℝ)*((n:ℝ)/(q:ℝ)^2)+5760) :=
      sum_le_sum fun q _ => one_square n q B ha
    _ = ((5760/30030:ℝ)*n)*(∑ q∈P,1/(q:ℝ)^2)+5760*(P.card:ℝ) := by
      rw [sum_add_distrib,Finset.mul_sum]
      simp [div_eq_mul_inv, mul_assoc, mul_comm, mul_left_comm]
    _ ≤ ((5760/30030:ℝ)*n)*(72958819/3000000000000)+5760*100000000 := by
      exact add_le_add (mul_le_mul_of_nonneg_left hs (by positivity)) (by linarith)
    _ < (n:ℝ)/(100*2025) := by linarith
    _ ≤ _ := div_le_div_of_nonneg_left pos.le (by positivity) (by linarith)

end SiftedSquareLoss


theorem Conjectures.Goldbach.FiniteSiftedSquareBudget :
∀ n : ℕ, 4000000000000000000 < n → (n:ℝ) < Real.exp (Real.exp (19/5)) →
      let z := ⌈(n:ℝ)^((1:ℝ)/5)⌉₊
      let y := max ⌈(n:ℝ)^((1:ℝ)/3)⌉₊ ⌈Real.sqrt ((n:ℝ)/(z:ℝ))⌉₊
      let A := (Finset.range (n+1)).filter (fun p => p.Prime ∧ ¬ p ∣ n ∧
        ((Finset.Ico 2 z).filter (fun q => Nat.Prime q ∧ q ∣ n-p))=∅)
      let B := A.filter (fun p => 2 ≤ n-p)
      2 < z ∧ z < y ∧ n ≤ y^3 ∧ n ≤ z*y^2 ∧
      (∑ q∈(Finset.Ico z y).filter Nat.Prime, (((B.filter (fun p => q^2 ∣ n-p)).card):ℝ)) <
        (n:ℝ)/(100*(Real.log n)^2) :=
  SiftedSquareLoss.result

theorem Conjectures.Goldbach.FiniteSiftedSquareCostHandoff :
∀ n : ℕ, 4000000000000000000<n → (n:ℝ)<Real.exp (Real.exp (19/5)) →
let z := ⌈(n:ℝ)^((1:ℝ)/5)⌉₊
let y := max ⌈(n:ℝ)^((1:ℝ)/3)⌉₊ ⌈Real.sqrt ((n:ℝ)/(z:ℝ))⌉₊
let A := (Finset.range (n+1)).filter (fun p => p.Prime ∧ ¬p∣n ∧
  ((Finset.Ico 2 z).filter (fun q => q.Prime ∧ q∣n-p))=∅)
let B := A.filter (fun p => 2≤n-p)
let P := (Finset.Ico z y).filter Nat.Prime
let W (s : ℕ) : ℤ := 2-((P.filter (fun q => q∣s)).card:ℤ)-
  ((P.filter (fun q => q^2∣s)).card:ℤ)
2<z ∧ z<y ∧ n≤y^3 ∧ n≤z*y^2 ∧
(∑ q∈P, ((B.filter (fun p => q^2∣n-p)).card:ℝ)) < (n:ℝ)/(100*(Real.log n)^2) ∧
((n:ℝ)/(100*(Real.log n)^2) ≤ 2*(B.card:ℝ)-
  (∑ q∈P, ((B.filter (fun p => q∣n-p)).card:ℝ)) →
  0<(∑ p∈B,W (n-p))) := by
  intro n hn hu z y A B P W
  obtain ⟨hz,hy,h3,h2,loss⟩ := Conjectures.Goldbach.FiniteSiftedSquareBudget n hn hu
  refine ⟨hz,hy,h3,h2,loss,?_⟩
  intro main
  obtain ⟨identity,_⟩ := Conjectures.Goldbach.FiniteWeightedSieveSupportedRegion n z y (by omega) hz hy
  change (∑ p∈B,W (n-p)) = 2*(B.card:ℤ)-
    (∑ q∈P, ((B.filter (fun p => q∣n-p)).card:ℤ))-
    (∑ q∈P, ((B.filter (fun p => q^2∣n-p)).card:ℤ)) at identity
  have cast := congrArg (fun x : ℤ => (x:ℝ)) identity
  push_cast at cast
  change (∑ q∈P, ((B.filter (fun p => q^2∣n-p)).card:ℝ)) < _ at loss
  have positive : (0:ℝ)<((∑ p∈B,W (n-p):ℤ):ℝ) := by
    rw [Int.cast_sum]
    linarith only [cast,loss,main]
  exact_mod_cast positive
