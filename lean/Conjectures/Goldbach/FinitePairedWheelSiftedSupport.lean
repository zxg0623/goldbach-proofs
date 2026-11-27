import Mathlib
import PEqualNP.Outside.L_goldbach_finite_rough_factor_power

namespace PartitionedGoldbachWheel

def small : Finset ℕ := {7,11,13,17,19,23,29}
def pairs : Finset (ℕ × ℕ) := {(31,37),(41,43),(47,53),(59,61),(67,71),(73,79),(83,89),(97,101),(103,107),(109,113)}
def singles : Finset ℕ := (Finset.Ico 114 7643).filter Nat.Prime
def row (H : Finset ℕ) : Finset ℕ := (Finset.Icc 30 1926574681).filter fun p =>
  p.Prime ∧ ∀ q∈small, (q∈H ↔ q/2<p % q)
def one (S : Finset ℕ) (q : ℕ) : ℕ := (Finset.range q).sup fun a =>
  (S.filter (fun p => p % q=a)).card
def two (S : Finset ℕ) (d : ℕ × ℕ) : ℕ := ((Finset.range d.1) ×ˢ (Finset.range d.2)).sup fun ab =>
  (S.filter (fun p => p % d.1=ab.1 ∨ p % d.2=ab.2)).card
def balance (H : Finset ℕ) : ℕ := (row H).card -
  ((∑ q∈singles,one (row H) q)+(∑ d∈pairs,two (row H) d))
def separate (H : Finset ℕ) : ℕ := (row H).card -
  ((∑ q∈singles,one (row H) q)+(∑ d∈pairs,(one (row H) d.1+one (row H) d.2)))
def floor : ℕ := small.powerset.inf' (Finset.powerset_nonempty small) balance
def individual : ℕ := small.powerset.inf' (Finset.powerset_nonempty small) separate

private theorem survivors (S E : Finset ℕ) (D : Finset (ℕ × ℕ)) (m n : ℕ)
    (h1 : ∀ q∈E, 0<q) (h2 : ∀ d∈D, 0<d.1 ∧ 0<d.2)
    (hcount : m≤S.card-((∑ q∈E,one S q)+(∑ d∈D,two S d))) :
    ∃ T : Finset ℕ, m≤T.card ∧ T⊆S ∧ ∀ p∈T,
      (∀ q∈E, p % q≠n % q) ∧ (∀ d∈D, p % d.1≠n % d.1 ∧ p % d.2≠n % d.2) := by
  let A (q : ℕ) := S.filter (fun p => p % q=n % q)
  let B (d : ℕ × ℕ) := S.filter (fun p => p % d.1=n % d.1 ∨ p % d.2=n % d.2)
  let bad := E.biUnion A ∪ D.biUnion B
  have hA : (E.biUnion A).card ≤ ∑ q∈E,one S q := by
    apply Finset.card_biUnion_le.trans
    apply Finset.sum_le_sum
    intro q hq
    exact Finset.le_sup (f:=fun a => (S.filter (fun p => p % q=a)).card)
      (Finset.mem_range.mpr (Nat.mod_lt n (h1 q hq)))
  have hB : (D.biUnion B).card ≤ ∑ d∈D,two S d := by
    apply Finset.card_biUnion_le.trans
    apply Finset.sum_le_sum
    intro d hd
    apply Finset.le_sup (f:=fun ab : ℕ × ℕ => (S.filter (fun p => p % d.1=ab.1 ∨ p % d.2=ab.2)).card)
      (b:=(n % d.1,n % d.2))
    exact Finset.mem_product.mpr ⟨Finset.mem_range.mpr (Nat.mod_lt n (h2 d hd).1),
      Finset.mem_range.mpr (Nat.mod_lt n (h2 d hd).2)⟩
  have hbad := Finset.card_union_le (E.biUnion A) (D.biUnion B)
  change bad.card≤_ at hbad
  have hrem := Finset.card_le_card_sdiff_add_card (s:=S) (t:=bad)
  refine ⟨S \ bad,by omega,Finset.sdiff_subset,?_⟩
  intro p hp
  obtain ⟨hs,hh⟩ := Finset.mem_sdiff.mp hp
  constructor
  · intro q hq eq
    exact hh (Finset.mem_union_left _ (Finset.mem_biUnion.mpr ⟨q,hq,Finset.mem_filter.mpr ⟨hs,eq⟩⟩))
  · intro d hd
    have clear : ¬(p % d.1=n % d.1 ∨ p % d.2=n % d.2) := fun hit =>
      hh (Finset.mem_union_right _ (Finset.mem_biUnion.mpr ⟨d,hd,Finset.mem_filter.mpr ⟨hs,hit⟩⟩))
    exact ⟨fun eq => clear (Or.inl eq),fun eq => clear (Or.inr eq)⟩

private theorem prime_class (q : ℕ) (hq : q.Prime) (low : q<7643) :
    q∣30 ∨ q∈small ∨ (∃ d∈pairs, q=d.1 ∨ q=d.2) ∨ q∈singles := by
  by_cases h : q<114
  · have all : ∀ i : Fin 114, i.val.Prime →
        i.val∣30 ∨ i.val∈small ∨ ∃ d∈pairs, i.val=d.1 ∨ i.val=d.2 := by decide
    rcases all ⟨q,h⟩ hq with a|b|c
    · exact Or.inl a
    · exact Or.inr (Or.inl b)
    · exact Or.inr (Or.inr (Or.inl c))
  · exact Or.inr (Or.inr (Or.inr (Finset.mem_filter.mpr ⟨Finset.mem_Ico.mpr ⟨by omega,low⟩,hq⟩)))

theorem rough (n : ℕ) (hn : 1926574683≤n) (div : 30∣n) :
    ∃ T : Finset ℕ, floor≤T.card ∧ ∀ p∈T, p.Prime ∧ p≤1926574681 ∧ 2≤n-p ∧
      ∀ q : ℕ, q.Prime → q∣n-p → 7643≤q := by
  let H := small.filter fun q => n % q≤q/2
  have hH : H∈small.powerset := Finset.mem_powerset.mpr (Finset.filter_subset _ _)
  have epos : ∀ q∈singles, 0<q := fun _ hq => (Finset.mem_filter.mp hq).2.pos
  have dpos : ∀ d∈pairs, 0<d.1 ∧ 0<d.2 := by decide
  obtain ⟨T,count,sub,clear⟩ := survivors (row H) singles pairs floor n epos dpos (Finset.inf'_le balance hH : floor≤balance H)
  refine ⟨T,count,?_⟩
  intro p hp
  obtain ⟨bounds,prime,flags⟩ := Finset.mem_filter.mp (sub hp)
  obtain ⟨left,right⟩ := Finset.mem_Icc.mp bounds
  refine ⟨prime,right,by omega,?_⟩
  intro q hq hd
  by_contra! low
  have modEq := (Nat.modEq_zero_iff_dvd.mpr hd).add (Nat.ModEq.refl p)
  have eq : p % q=n % q := by
    simpa [Nat.ModEq,Nat.sub_add_cancel (by omega : p≤n)] using modEq.symm
  rcases prime_class q hq low with dq|sm|pair|single
  · have z : n % q=0 := Nat.mod_eq_zero_of_dvd (dq.trans div)
    have pd : q∣p := Nat.dvd_of_mod_eq_zero (eq.trans z)
    have qp := (Nat.dvd_prime prime).mp pd
    have ls := Nat.le_of_dvd (by decide : 0<30) dq
    have less : q≠30 := by intro e; subst q; exact (by decide : ¬Nat.Prime 30) hq
    rcases qp with u|u
    · exact hq.ne_one u
    · omega
  · have iff1 := flags q sm
    have iff2 : q∈H ↔ n % q≤q/2 := by simp [H,sm]
    rw [iff2,eq] at iff1
    omega
  · obtain ⟨d,hm,h⟩ := pair
    rcases h with rfl|rfl
    · exact (clear p hp).2 d hm |>.1 eq
    · exact (clear p hp).2 d hm |>.2 eq
  · exact (clear p hp).1 q single eq

private theorem expNat {k : ℕ} (hk : k≠0) : Real.exp k < (193/71 : ℝ)^k := by
  rw [show (k:ℝ)=k*1 by ring,Real.exp_nat_mul]
  exact pow_lt_pow_left₀ (Real.exp_one_lt_d9.trans (by norm_num)) (Real.exp_pos 1).le hk

set_option maxRecDepth 12000 in
set_option maxHeartbeats 1800000 in
private theorem log_bound : (152/17:ℝ)<Real.log 7643 := by
  apply (Real.lt_log_iff_exp_lt (by norm_num : (0:ℝ)<7643)).mpr
  by_contra! h
  have lower : (7643:ℝ)^17≤(Real.exp (152/17))^17 :=
    pow_le_pow_left₀ (by norm_num) h 17
  have eq : (Real.exp (152/17))^17=Real.exp 152 := by
    rw [← Real.exp_nat_mul]
    norm_num
  rw [eq] at lower
  have ints : (193:ℕ)^152 < 7643^17*71^152 := by decide +kernel
  have reals : (193:ℝ)^152 < (7643:ℝ)^17*71^152 := by exact_mod_cast ints
  have top : Real.exp 152 < (7643:ℝ)^17 :=
    (expNat (k:=152) (by decide)).trans (by
      rw [div_pow,div_lt_iff₀ (by positivity)]
      exact reals)
  exact (not_le_of_gt top) lower

private theorem numeric : Real.exp (19/5)<5*Real.log 7643 ∧ Real.exp 5<17*Real.log 7643 := by
  have small : Real.exp (19/5)<5*(152/17:ℝ) := by
    by_contra! h
    have lower := pow_le_pow_left₀ (by norm_num : (0:ℝ)≤5*(152/17)) h 5
    have eq : (Real.exp (19/5))^5=Real.exp 19 := by rw [← Real.exp_nat_mul]; norm_num
    rw [eq] at lower
    exact (not_le_of_gt ((expNat (k:=19) (by decide)).trans
      (by norm_num : (193/71:ℝ)^19<(5*(152/17))^5))) lower
  have large : Real.exp 5<17*(152/17:ℝ) :=
    (expNat (k:=5) (by decide)).trans (by norm_num)
  constructor <;> linarith [log_bound]

private theorem exp_power {x : ℝ} {j : ℕ} (h : Real.exp x<j*Real.log 7643) :
    Real.exp (Real.exp x)<(7643:ℝ)^j := by
  calc
    _ < Real.exp (j*Real.log 7643) := Real.exp_lt_exp.mpr h
    _ = _ := by rw [Real.exp_nat_mul,Real.exp_log (by norm_num)]



theorem eligible : ∀ n : ℕ, 4000000000000000000<n → 30∣n → (n:ℝ)<Real.exp (Real.exp (19/5)) →
  ∃ T : Finset ℕ, floor-4≤T.card ∧ ∀ p∈T, p.Prime ∧ p≤1926574681 ∧ ¬p∣n ∧ 2≤n-p ∧
    (n-p).primeFactorsList.length≤4 ∧ ((Finset.Ico 2 7643).filter
      (fun q => Nat.Prime q ∧ q∣n-p))=∅ := by
  intro n lower hd upper
  have realcut : (n:ℝ)<(7643:ℝ)^5 := upper.trans (exp_power numeric.1)
  have ncut : n<7643^5 := by exact_mod_cast realcut
  obtain ⟨S,count,hs⟩ := rough n (by omega) hd
  let D := S.filter fun p => p∣n
  have facts : ∀ p∈D, p∈n.primeFactors ∧ 7643≤p := by
    intro p hp
    obtain ⟨hm,dv⟩ := Finset.mem_filter.mp hp
    obtain ⟨pr,_,_,r⟩ := hs p hm
    exact ⟨Nat.mem_primeFactors.mpr ⟨pr,dv,by omega⟩,r p pr (Nat.dvd_sub dv (dvd_refl p))⟩
  have sub : D⊆n.primeFactors := fun p hp => (facts p hp).1
  have product : (∏ p∈D,p)∣n :=
    (Finset.prod_dvd_prod_of_subset _ _ _ sub).trans (Nat.prod_primeFactors_dvd n)
  have bound : 7643^D.card≤∏ p∈D,p := by
    calc 7643^D.card = ∏ _p∈D,(7643:ℕ) := by simp
         _ ≤ _ := Finset.prod_le_prod (fun p hp => (facts p hp).2)
  have few : D.card≤4 := by
    by_contra! more
    exact (not_le_of_gt ncut) ((Nat.pow_le_pow_right (by decide : 0<7643) more).trans
      (bound.trans (Nat.le_of_dvd (by omega) product)))
  have remain := Finset.card_le_card_sdiff_add_card (s:=S) (t:=D)
  refine ⟨S \ D,by omega,?_⟩
  intro p hp
  obtain ⟨hm,other⟩ := Finset.mem_sdiff.mp hp
  obtain ⟨pr,pb,s2,hr⟩ := hs p hm
  have power := PEqualNP.Outside.L_goldbach_finite_rough_factor_power _ _ s2 (by decide) hr
  refine ⟨pr,pb,fun d => other (Finset.mem_filter.mpr ⟨hm,d⟩),s2,?_,?_⟩
  · by_contra! more
    exact (not_le_of_gt ncut) ((Nat.pow_le_pow_right (by decide : 0<7643) more).trans
      (power.trans (Nat.sub_le _ _)))
  · apply Finset.eq_empty_iff_forall_notMem.mpr
    intro q hq
    obtain ⟨mem,prime,dvd⟩ := Finset.mem_filter.mp hq
    exact (not_le_of_gt (Finset.mem_Ico.mp mem).2) (hr q prime dvd)


private theorem pair_le (S : Finset ℕ) (d : ℕ × ℕ) : two S d≤one S d.1+one S d.2 := by
  apply Finset.sup_le
  intro ab hab
  obtain ⟨ha,hb⟩ := Finset.mem_product.mp hab
  have eq : S.filter (fun p => p % d.1=ab.1 ∨ p % d.2=ab.2) =
      S.filter (fun p => p % d.1=ab.1) ∪ S.filter (fun p => p % d.2=ab.2) := by
    ext p
    simp only [Finset.mem_filter,Finset.mem_union]
    tauto
  rw [eq]
  apply (Finset.card_union_le _ _).trans
  exact Nat.add_le_add (Finset.le_sup (f:=fun a => (S.filter (fun p => p % d.1=a)).card) ha)
    (Finset.le_sup (f:=fun b => (S.filter (fun p => p % d.2=b)).card) hb)

theorem dominates : individual≤floor := by
  apply Finset.le_inf'
  intro H hH
  apply (Finset.inf'_le separate hH).trans
  change (row H).card - _ ≤ (row H).card - _
  have bound := Finset.sum_le_sum (s:=pairs) (fun d _ => pair_le (row H) d)
  omega

def evenSmall : Finset ℕ := {3,5,7,11,13,17,19}
def evenSingles : Finset ℕ := (Finset.Ico 20 1721).filter Nat.Prime
def evenRow (H : Finset ℕ) : Finset ℕ := (Finset.Icc 20 100000000).filter fun p =>
  p.Prime ∧ ∀ q∈evenSmall, (q∈H ↔ q/2<p % q)
def evenBalance (H : Finset ℕ) : ℕ := (evenRow H).card - ∑ q∈evenSingles,one (evenRow H) q
def evenFloor : ℕ := evenSmall.powerset.inf' (Finset.powerset_nonempty evenSmall) evenBalance

theorem all_even (n : ℕ) (hn : 100000002≤n) (en : Even n) :
    ∃ T : Finset ℕ, evenFloor≤T.card ∧ ∀ p∈T, p.Prime ∧ p≤100000000 ∧ 2≤n-p ∧
      ∀ q : ℕ, q.Prime → q∣n-p → 1721≤q := by
  let H := evenSmall.filter fun q => n % q≤q/2
  have hH : H∈evenSmall.powerset := Finset.mem_powerset.mpr (Finset.filter_subset _ _)
  have epos : ∀ q∈evenSingles, 0<q := fun _ hq => (Finset.mem_filter.mp hq).2.pos
  have bound : evenFloor≤evenBalance H := Finset.inf'_le evenBalance hH
  have zero : (∑ d∈(∅ : Finset (ℕ × ℕ)),two (evenRow H) d)=0 := Finset.sum_empty
  have count : evenFloor≤(evenRow H).card-((∑ q∈evenSingles, one (evenRow H) q)+
      (∑ d∈(∅ : Finset (ℕ × ℕ)),two (evenRow H) d)) := by
    rw [zero,Nat.add_zero]
    exact bound
  obtain ⟨T,size,sub,clear⟩ := survivors (evenRow H) evenSingles ∅ evenFloor n epos
    (fun _ hd => False.elim (Finset.notMem_empty _ hd)) count
  refine ⟨T,size,?_⟩
  intro p hp
  obtain ⟨interval,prime,flags⟩ := Finset.mem_filter.mp (sub hp)
  obtain ⟨left,right⟩ := Finset.mem_Icc.mp interval
  refine ⟨prime,right,by omega,?_⟩
  intro q hq hd
  by_contra! low
  have modEq := (Nat.modEq_zero_iff_dvd.mpr hd).add (Nat.ModEq.refl p)
  have eq : p % q=n % q := by simpa [Nat.ModEq,Nat.sub_add_cancel (by omega : p≤n)] using modEq.symm
  by_cases sm : q<20
  · have listed : ∀ i : Fin 20, i.val.Prime → i.val=2 ∨ i.val∈evenSmall := by decide
    rcases listed ⟨q,sm⟩ hq with a|b
    · change q=2 at a
      subst q
      have dvd : 2∣p := Nat.dvd_of_mod_eq_zero (eq.trans (Nat.mod_eq_zero_of_dvd (even_iff_two_dvd.mp en)))
      have cases := (Nat.dvd_prime prime).mp dvd
      omega
    · have iff1 := flags q b
      have iff2 : q∈H ↔ n % q≤q/2 := by simp [H,b]
      rw [iff2,eq] at iff1
      omega
  · have mem : q∈evenSingles := Finset.mem_filter.mpr ⟨Finset.mem_Ico.mpr ⟨by omega,low⟩,hq⟩
    exact (clear p hp).1 q mem eq

end PartitionedGoldbachWheel

set_option maxRecDepth 5000 in
set_option maxHeartbeats 1600000 in
theorem Conjectures.Goldbach.FinitePairedWheelSiftedSupport :
let small : Finset ℕ := {7,11,13,17,19,23,29}
let pairs : Finset (ℕ × ℕ) := {(31,37),(41,43),(47,53),(59,61),(67,71),(73,79),(83,89),(97,101),(103,107),(109,113)}
let singles : Finset ℕ := (Finset.Ico 114 7643).filter Nat.Prime
let row (H : Finset ℕ) : Finset ℕ := (Finset.Icc 30 1926574681).filter fun p =>
  p.Prime ∧ ∀ q∈small, (q∈H ↔ q/2<p % q)
let one (S : Finset ℕ) (q : ℕ) : ℕ := (Finset.range q).sup fun a =>
  (S.filter (fun p => p % q=a)).card
let two (S : Finset ℕ) (d : ℕ × ℕ) : ℕ := ((Finset.range d.1) ×ˢ (Finset.range d.2)).sup fun ab =>
  (S.filter (fun p => p % d.1=ab.1 ∨ p % d.2=ab.2)).card
let balance (H : Finset ℕ) : ℕ := (row H).card -
  ((∑ q∈singles,one (row H) q)+(∑ d∈pairs,two (row H) d))
let separate (H : Finset ℕ) : ℕ := (row H).card -
  ((∑ q∈singles,one (row H) q)+(∑ d∈pairs,(one (row H) d.1+one (row H) d.2)))
let floor : ℕ := small.powerset.inf' (Finset.powerset_nonempty small) balance
let individual : ℕ := small.powerset.inf' (Finset.powerset_nonempty small) separate
let evenSmall : Finset ℕ := {3,5,7,11,13,17,19}
let evenSingles : Finset ℕ := (Finset.Ico 20 1721).filter Nat.Prime
let evenRow (H : Finset ℕ) : Finset ℕ := (Finset.Icc 20 100000000).filter fun p =>
  p.Prime ∧ ∀ q∈evenSmall, (q∈H ↔ q/2<p % q)
let evenBalance (H : Finset ℕ) : ℕ := (evenRow H).card - ∑ q∈evenSingles,one (evenRow H) q
let evenFloor : ℕ := evenSmall.powerset.inf' (Finset.powerset_nonempty evenSmall) evenBalance
individual≤floor ∧
(∀ n : ℕ, 100000002≤n → Even n →
  ∃ T : Finset ℕ, evenFloor≤T.card ∧ ∀ p∈T, p.Prime ∧ p≤100000000 ∧ 2≤n-p ∧
    ∀ q : ℕ, q.Prime → q∣n-p → 1721≤q) ∧
(∀ n : ℕ, 1926574683≤n → 30∣n →
  ∃ T : Finset ℕ, floor≤T.card ∧ ∀ p∈T, p.Prime ∧ p≤1926574681 ∧ 2≤n-p ∧
    ∀ q : ℕ, q.Prime → q∣n-p → 7643≤q) ∧
(∀ n : ℕ, 4000000000000000000<n → 30∣n → (n:ℝ)<Real.exp (Real.exp (19/5)) →
  ∃ T : Finset ℕ, floor-4≤T.card ∧ ∀ p∈T, p.Prime ∧ p≤1926574681 ∧ ¬p∣n ∧ 2≤n-p ∧
    (n-p).primeFactorsList.length≤4 ∧ ((Finset.Ico 2 7643).filter
      (fun q => Nat.Prime q ∧ q∣n-p))=∅) := by
  intro small pairs singles row one two balance separate floor individual evenSmall evenSingles evenRow evenBalance evenFloor
  have smallEq : small = PartitionedGoldbachWheel.small := rfl
  have pairsEq : pairs = PartitionedGoldbachWheel.pairs := rfl
  have singlesEq : singles = PartitionedGoldbachWheel.singles := rfl
  let makeRow (small : Finset ℕ) : Finset ℕ → Finset ℕ :=
    fun (H : Finset ℕ) =>
    (Finset.Icc 30 1926574681).filter fun p =>
      p.Prime ∧ ∀ q∈small, (q∈H ↔ q/2<p % q)
  have rowEq : row = PartitionedGoldbachWheel.row :=
    congrArg makeRow smallEq
  have oneEq : one = PartitionedGoldbachWheel.one := rfl
  have twoEq : two = PartitionedGoldbachWheel.two := rfl
  let makeBalance (pairs : Finset (ℕ × ℕ)) (singles : Finset ℕ) (row : Finset ℕ → Finset ℕ) (one : Finset ℕ → ℕ → ℕ) (two : Finset ℕ → (ℕ × ℕ) → ℕ) : Finset ℕ → ℕ :=
    fun (H : Finset ℕ) =>
    (row H).card -
      ((∑ q∈singles,one (row H) q)+(∑ d∈pairs,two (row H) d))
  have balanceEq : balance = PartitionedGoldbachWheel.balance :=
    congr (congr (congr (congr (congrArg makeBalance pairsEq) singlesEq) rowEq) oneEq) twoEq
  let makeSeparate (pairs : Finset (ℕ × ℕ)) (singles : Finset ℕ) (row : Finset ℕ → Finset ℕ) (one : Finset ℕ → ℕ → ℕ) : Finset ℕ → ℕ :=
    fun (H : Finset ℕ) =>
    (row H).card -
      ((∑ q∈singles,one (row H) q)+(∑ d∈pairs,(one (row H) d.1+one (row H) d.2)))
  have separateEq : separate = PartitionedGoldbachWheel.separate :=
    congr (congr (congr (congrArg makeSeparate pairsEq) singlesEq) rowEq) oneEq
  let makeFloor (small : Finset ℕ) (balance : Finset ℕ → ℕ) : ℕ :=
    small.powerset.inf' (Finset.powerset_nonempty small) balance
  have floorEq : floor = PartitionedGoldbachWheel.floor := by
    have lifted := congr (congrArg makeFloor smallEq) balanceEq
    dsimp only [makeFloor] at lifted
    dsimp only [floor, PartitionedGoldbachWheel.floor]
    exact lifted
  let makeIndividual (small : Finset ℕ) (separate : Finset ℕ → ℕ) : ℕ :=
    small.powerset.inf' (Finset.powerset_nonempty small) separate
  have individualEq : individual = PartitionedGoldbachWheel.individual := by
    have lifted := congr (congrArg makeIndividual smallEq) separateEq
    dsimp only [makeIndividual] at lifted
    dsimp only [individual, PartitionedGoldbachWheel.individual]
    exact lifted
  have evenSmallEq : evenSmall = PartitionedGoldbachWheel.evenSmall := rfl
  have evenSinglesEq : evenSingles = PartitionedGoldbachWheel.evenSingles := rfl
  let makeEvenRow (evenSmall : Finset ℕ) : Finset ℕ → Finset ℕ :=
    fun (H : Finset ℕ) =>
    (Finset.Icc 20 100000000).filter fun p =>
      p.Prime ∧ ∀ q∈evenSmall, (q∈H ↔ q/2<p % q)
  have evenRowEq : evenRow = PartitionedGoldbachWheel.evenRow :=
    congrArg makeEvenRow evenSmallEq
  let makeEvenBalance (one : Finset ℕ → ℕ → ℕ) (evenSingles : Finset ℕ) (evenRow : Finset ℕ → Finset ℕ) : Finset ℕ → ℕ :=
    fun (H : Finset ℕ) =>
    (evenRow H).card - ∑ q∈evenSingles,one (evenRow H) q
  have evenBalanceEq : evenBalance = PartitionedGoldbachWheel.evenBalance :=
    congr (congr (congrArg makeEvenBalance oneEq) evenSinglesEq) evenRowEq
  let makeEvenFloor (evenSmall : Finset ℕ) (evenBalance : Finset ℕ → ℕ) : ℕ :=
    evenSmall.powerset.inf' (Finset.powerset_nonempty evenSmall) evenBalance
  have evenFloorEq : evenFloor = PartitionedGoldbachWheel.evenFloor := by
    have lifted := congr (congrArg makeEvenFloor evenSmallEq) evenBalanceEq
    dsimp only [makeEvenFloor] at lifted
    dsimp only [evenFloor, PartitionedGoldbachWheel.evenFloor]
    exact lifted
  let conclusion (individual floor evenFloor : ℕ) : Prop :=
    individual≤floor ∧
    (∀ n : ℕ, 100000002≤n → Even n →
      ∃ T : Finset ℕ, evenFloor≤T.card ∧ ∀ p∈T, p.Prime ∧ p≤100000000 ∧ 2≤n-p ∧
        ∀ q : ℕ, q.Prime → q∣n-p → 1721≤q) ∧
    (∀ n : ℕ, 1926574683≤n → 30∣n →
      ∃ T : Finset ℕ, floor≤T.card ∧ ∀ p∈T, p.Prime ∧ p≤1926574681 ∧ 2≤n-p ∧
        ∀ q : ℕ, q.Prime → q∣n-p → 7643≤q) ∧
    (∀ n : ℕ, 4000000000000000000<n → 30∣n → (n:ℝ)<Real.exp (Real.exp (19/5)) →
      ∃ T : Finset ℕ, floor-4≤T.card ∧ ∀ p∈T, p.Prime ∧ p≤1926574681 ∧ ¬p∣n ∧ 2≤n-p ∧
        (n-p).primeFactorsList.length≤4 ∧ ((Finset.Ico 2 7643).filter
          (fun q => Nat.Prime q ∧ q∣n-p))=∅)
  have eq : conclusion individual floor evenFloor =
      conclusion PartitionedGoldbachWheel.individual PartitionedGoldbachWheel.floor PartitionedGoldbachWheel.evenFloor :=
    congr (congr (congrArg conclusion individualEq) floorEq) evenFloorEq
  exact eq.mpr ⟨PartitionedGoldbachWheel.dominates, PartitionedGoldbachWheel.all_even,
    PartitionedGoldbachWheel.rough, PartitionedGoldbachWheel.eligible⟩
