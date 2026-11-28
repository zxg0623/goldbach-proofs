import Mathlib

open Finset Filter
open scoped BigOperators Topology

namespace CentralDesertDensity

private def countSet (M a b : ℕ) :=
  (Ioc a b).filter (fun p : ℕ => p.Prime ∧ p ≡ M-1 [MOD M])

private noncomputable def weight (M a b : ℕ) := ∑ p ∈ countSet M a b, Real.log (p:ℝ)

private theorem weight_add (M x : ℕ) : weight M 0 (3*x) + weight M (3*x) (4*x) = weight M 0 (4*x) := by
  have split : countSet M 0 (3*x) ∪ countSet M (3*x) (4*x) = countSet M 0 (4*x) := by
    unfold countSet
    rw [← Finset.filter_union, Finset.Ioc_union_Ioc_eq_Ioc (Nat.zero_le (3*x)) (by omega)]
  have dis : Disjoint (countSet M 0 (3*x)) (countSet M (3*x) (4*x)) := by
    apply Finset.disjoint_left.mpr
    intro p hp hq
    have a := (mem_Ioc.mp (mem_filter.mp hp).1).2
    have b := (mem_Ioc.mp (mem_filter.mp hq).1).1
    omega
  unfold weight
  rw [← Finset.sum_union dis, split]

private theorem plentiful (M : ℕ) (hM : 0 < M) :
    ∃ N : ℕ, ∀ m ≥ N, 8*m^6 ≤ (countSet M (3*m^8) (4*m^8)).card ∧ ((m^8:ℕ):ℝ) < 4*(M.totient:ℝ)*((countSet M (3*m^8) (4*m^8)).card:ℝ)*Real.log (4*((m^8:ℕ):ℝ)) := by
  let : NeZero M := ⟨hM.ne'⟩
  have unit : (M-1).Coprime M := (Nat.coprime_self_sub_left (by omega)).2 (by simp)
  have hφ : 0 < (M.totient:ℝ) := by exact_mod_cast Nat.totient_pos.mpr hM
  let F : ℝ → ℝ := fun t => (M.totient:ℝ)*(weight M 0 ⌊t⌋₊/t)
  have lim : Tendsto F atTop (𝓝 1) := by
    have h := (Chebyshev.tendsto_sum_log_prime_modEq_div_atTop unit).const_mul (M.totient:ℝ)
    simpa [F,weight,countSet,hφ.ne'] using h
  have low := (tendsto_order.1 lim).1 (9/10:ℝ) (by norm_num)
  have high := (tendsto_order.1 lim).2 (11/10:ℝ) (by norm_num)
  obtain ⟨bound,hbound⟩ := eventually_atTop.1 (low.and high)
  obtain ⟨b,hb⟩ := exists_nat_gt bound
  refine ⟨b+320*M.totient+2,?_⟩
  intro m hm
  have hm1 : 1 ≤ m := by omega
  have hmR : (1:ℝ) ≤ m := by exact_mod_cast hm1
  have hmx : m ≤ m^8 := Nat.le_self_pow (by decide) _
  have hxl : bound ≤ (m^8:ℕ) := by exact le_trans hb.le (by exact_mod_cast (show b ≤ m^8 by omega))
  let x := m^8
  have hx : (0:ℝ) < x := by dsimp [x]; positivity
  have hx3 : (0:ℝ) < 3*x := by positivity
  have hx4 : (0:ℝ) < 4*x := by positivity
  have lx := (hbound (4*x) (by change bound ≤ 4*(m^8:ℕ); linarith)).1
  have ux := (hbound (3*x) (by change bound ≤ 3*(m^8:ℕ); linarith)).2
  change (9:ℝ)/10 < (M.totient:ℝ)*(weight M 0 ⌊(4*(x:ℝ))⌋₊/(4*x)) at lx
  change (M.totient:ℝ)*(weight M 0 ⌊(3*(x:ℝ))⌋₊/(3*x)) < (11:ℝ)/10 at ux
  rw [show (4:ℝ)*x = ((4*x:ℕ):ℝ) by push_cast; ring, Nat.floor_natCast] at lx
  rw [show (3:ℝ)*x = ((3*x:ℕ):ℝ) by push_cast; ring, Nat.floor_natCast] at ux
  push_cast at ux lx
  rw [← mul_div_assoc] at ux lx
  have u := (div_lt_iff₀ hx3).mp ux
  have l := (lt_div_iff₀ hx4).mp lx
  have add := weight_add M x
  have lowWeight : (x:ℝ) < 4*(M.totient:ℝ)*weight M (3*x) (4*x) := by
    rw [← add] at l
    linarith
  have wlog : weight M (3*x) (4*x) ≤ ((countSet M (3*x) (4*x)).card:ℝ)*Real.log (4*(x:ℝ)) := by
    unfold weight
    calc
      _ ≤ ∑ _p ∈ countSet M (3*x) (4*x), Real.log (4*(x:ℝ)) := by
        apply sum_le_sum
        intro p hp
        have hp' := (mem_filter.mp hp).2.1.pos
        apply Real.log_le_log (by positivity)
        exact_mod_cast (mem_Ioc.mp (mem_filter.mp hp).1).2
      _ = _ := by simp
  have raw : (x:ℝ) < 4*(M.totient:ℝ)*((countSet M (3*x) (4*x)).card:ℝ)*Real.log (4*(x:ℝ)) := by
    have h := lowWeight.trans_le (mul_le_mul_of_nonneg_left wlog (by positivity))
    linarith only [h]
  have upper : weight M (3*x) (4*x) ≤ ((countSet M (3*x) (4*x)).card:ℝ)*(10*m) := by
    unfold weight
    calc
      _ ≤ ∑ _p ∈ countSet M (3*x) (4*x), (10*(m:ℝ)) := by
        apply sum_le_sum
        intro p hp
        have hp' := (mem_filter.mp hp).2.1.pos
        have less := (mem_Ioc.mp (mem_filter.mp hp).1).2
        have step : Real.log (p:ℝ) ≤ Real.log (4*(m:ℝ)^8) := by
          apply Real.log_le_log (by positivity)
          exact_mod_cast less
        rw [Real.log_mul (by norm_num) (by positivity),Real.log_pow] at step
        have twoPos : (0:ℝ)<4 := by norm_num
        have mPos : 0<(m:ℝ) := by linarith
        norm_num1 at step
        linarith only [step, Real.log_le_sub_one_of_pos twoPos, Real.log_le_sub_one_of_pos mPos, hmR]
      _ = _ := by simp
  have ineq : (m:ℝ)^8 < 4*(M.totient:ℝ)*(((countSet M (3*x) (4*x)).card:ℝ)*(10*m)) := by
    rw [← Nat.cast_pow]
    exact lowWeight.trans_le (mul_le_mul_of_nonneg_left upper (by positivity))
  have big : (320:ℝ)*M.totient ≤ m := by exact_mod_cast (show 320*M.totient ≤ m by omega)
  have aux : (40*(M.totient:ℝ)*m)*(8*(m:ℝ)^6) ≤ (m:ℝ)^8 := calc
    _ = (320*(M.totient:ℝ))*m^7 := by ring
    _ ≤ (m:ℝ)*m^7 := by gcongr
    _ = _ := by ring
  have strict : 40*(M.totient:ℝ)*m*(8*(m:ℝ)^6) < 40*(M.totient:ℝ)*m*((countSet M (3*x) (4*x)).card:ℝ) := by
    exact aux.trans_lt (by convert ineq using 1 <;> ring)
  have cancel := (mul_lt_mul_iff_right₀ (show 0 < 40*(M.totient:ℝ)*m by positivity)).mp strict
  exact ⟨by exact_mod_cast cancel.le,raw⟩

private def centralReps (n : ℕ) := (range (n+1)).filter (fun p =>
  p < n-p ∧ n ≤ 3*p ∧ 3*p ≤ 2*n ∧ p.Prime ∧ (n-p).Prime)

private theorem heavy {α : Type*} [Fintype α] [DecidableEq α]
    (T : Finset ℕ) (f : α → ℕ) (Z D U : ℕ)
    (maps : ∀ a ∈ (univ : Finset α), f a ∈ T)
    (cap : ∀ n ∈ T, ((univ : Finset α).filter (fun a => f a = n)).card ≤ U)
    (mass : T.card*Z+D*U < Fintype.card α) :
    D ≤ (T.filter (fun n => Z < ((univ : Finset α).filter (fun a => f a=n)).card)).card := by
  classical
  let F := fun n => ((univ : Finset α).filter (fun a => f a=n)).card
  let J := T.filter (fun n => Z < F n)
  change D ≤ J.card
  by_contra! small
  have bound : ∀ n ∈ T, F n ≤ Z+(if Z<F n then U else 0) := by
    intro n hn
    by_cases h : Z<F n
    · rw [if_pos h]; exact (cap n hn).trans (by omega)
    · rw [if_neg h]; omega
  have total : Fintype.card α = ∑ n ∈ T, F n := by
    simpa [F] using card_eq_sum_card_fiberwise (f:=f) (s:=(univ : Finset α)) (t:=T) maps
  have dj : (∑ n ∈ T, if Z < F n then U else 0) = J.card*U := by
    dsimp only [J]
    rw [← Finset.sum_filter]
    simp
  have upper := Finset.sum_le_sum bound
  rw [Finset.sum_add_distrib, dj, Finset.sum_const, Nat.nsmul_eq_mul] at upper
  have small' := Nat.mul_le_mul_right U small.le
  omega

private theorem forbidden (B H n : ℕ) (ap : (B+H+2).factorial ∣ n+2)
    (size : 2*(B+H)+10 ≤ n) :
    Even n ∧ ∀ d ≤ H, ∀ p : ℕ, p.Prime → p ≤ B → ¬ (n-d-p).Prime ∧ ¬ (n+2-d-p).Prime := by
  have two : 2 ∣ (B+H+2).factorial := Nat.dvd_factorial (by decide) (by omega)
  constructor
  · obtain ⟨v,hv⟩ := two.trans ap
    exact ⟨v-1,by omega⟩
  intro d hd p hp bound
  have p2 := hp.two_le
  have kill (v k : ℕ) (vk : v+k=n+2) (vpos : 1<v) (small : v≤B+H+2) (lt : v<k) : ¬ k.Prime := by
    have div := (Nat.dvd_factorial (by omega : 0<v) small).trans ap
    rw [← vk] at div
    have hk := (Nat.dvd_add_right (dvd_refl v)).mp div
    intro prime
    rcases (Nat.dvd_prime prime).mp hk with e | e <;> omega
  exact ⟨kill (p+d+2) (n-d-p) (by omega) (by omega) (by omega) (by omega),
         kill (p+d) (n+2-d-p) (by omega) (by omega) (by omega) (by omega)⟩

theorem result : ∀ B H : ℕ, ∃ N : ℕ, ∀ m ≥ N, ∃ J : Finset ℕ, ((m^8:ℕ):ℝ) ≤ 96*((B+H+2).factorial.totient:ℝ)*(J.card:ℝ)*Real.log (4*((m^8:ℕ):ℝ)) ∧ ∀ n ∈ J, 6*m^8 < n ∧ n ≤ 8*m^8 ∧ Even n ∧ ((m^8:ℕ):ℝ) ≤ 4608*((B+H+2).factorial.totient:ℝ)^2*(((Finset.range (n+1)).filter (fun p => p < n-p ∧ n ≤ 3*p ∧ 3*p ≤ 2*n ∧ p.Prime ∧ (n-p).Prime)).card:ℝ)*(Real.log (4*((m^8:ℕ):ℝ)))^2 ∧ ∀ d ≤ H, ∀ p : ℕ, p.Prime → p ≤ B → ¬ (n-d-p).Prime ∧ ¬ (n+2-d-p).Prime := by
  classical
  intro B H
  let M := (B+H+2).factorial
  have hM : 0 < M := Nat.factorial_pos _
  obtain ⟨N,hN⟩ := plentiful M hM
  refine ⟨N+2*(B+H)+12,?_⟩
  intro m hm
  let x := m^8
  let S := countSet M (3*x) (4*x)
  let k := S.card/2
  let T := range (8*x+1)
  have m1 : 1 ≤ m := by omega
  have enough := hN m (by omega)
  have bigS : 8*m^6 ≤ S.card := enough.1
  have room : 2*k ≤ S.card := by dsimp [k]; omega
  have kmin : 4*m^6 ≤ k := by dsimp [k]; omega
  have mx : m ≤ x := Nat.le_self_pow (by decide) _
  have xpos : 0 < x := by omega
  have xp : 0 < (x:ℝ) := by exact_mod_cast xpos
  have kp : 1 ≤ k := by have h : 0 < m^6 := pow_pos (by omega) _; omega
  have smax : S.card ≤ x := by
    have h := card_le_card (filter_subset (fun p : ℕ => p.Prime ∧ p ≡ M-1 [MOD M]) (Ioc (3*x) (4*x)))
    change S.card ≤ (Ioc (3*x) (4*x)).card at h
    rw [Nat.card_Ioc] at h
    omega
  have kmax : k ≤ x := by omega
  let Z := k*k/(16*x)
  have den : 0 < 16*x := by omega
  have lb : 16*x ≤ k*k := calc
    16*x ≤ 16*m^12 := Nat.mul_le_mul_left 16 (Nat.pow_le_pow_right (by omega) (by decide))
    _ = (4*m^6)*(4*m^6) := by ring
    _ ≤ k*k := Nat.mul_le_mul kmin kmin
  have zpos : 0 < Z := Nat.div_pos lb den
  have divlow : Z*(16*x) ≤ k*k := Nat.div_mul_le_self _ _
  have rem := Nat.mod_lt (k*k) den
  have er : k*k % (16*x) + (16*x)*Z = k*k := Nat.mod_add_div _ _
  have dmin := Nat.mul_le_mul_left (16*x) (show 1 ≤ Z by omega)
  have kupper : k*k ≤ 32*x*Z := by nlinarith only [rem,er,dmin]
  have sc : S.card ≤ 3*k := by dsimp [k] at kp ⊢; omega
  have scR : (S.card:ℝ) ≤ 3*k := by exact_mod_cast sc
  have phi : 0 < (M.totient:ℝ) := by exact_mod_cast Nat.totient_pos.mpr hM
  have xl : 1 < 4*(x:ℝ) := by exact_mod_cast (show 1 < 4*x by omega)
  have ln : 0 < Real.log (4*(x:ℝ)) := Real.log_pos xl
  have raw : (x:ℝ) < 4*(M.totient:ℝ)*S.card*Real.log (4*(x:ℝ)) := enough.2
  have xm : (x:ℝ) < 12*(M.totient:ℝ)*k*Real.log (4*(x:ℝ)) := calc
    _ < _ := raw
    _ ≤ 4*(M.totient:ℝ)*(3*k)*Real.log (4*(x:ℝ)) := by gcongr
    _ = _ := by ring
  have square := mul_self_lt_mul_self xp.le xm
  have ku : (k:ℝ)*k ≤ 32*(x:ℝ)*Z := by exact_mod_cast kupper
  have cancelled : (x:ℝ)*(x:ℝ) ≤ (x:ℝ)*(4608*(M.totient:ℝ)^2*Z*(Real.log (4*(x:ℝ)))^2) := calc
    _ ≤ (144*(M.totient:ℝ)^2*(Real.log (4*(x:ℝ)))^2)*((k:ℝ)*k) := by nlinarith only [square]
    _ ≤ (144*(M.totient:ℝ)^2*(Real.log (4*(x:ℝ)))^2)*(32*(x:ℝ)*Z) := mul_le_mul_of_nonneg_left ku (by positivity)
    _ = _ := by ring
  have target (t : ℕ) (ht : Z ≤ t) : (x:ℝ) ≤ 4608*(M.totient:ℝ)^2*t*(Real.log (4*(x:ℝ)))^2 := by
    have z := (mul_le_mul_iff_right₀ xp).mp cancelled
    exact z.trans (by gcongr)
  let ix (i : Fin k) : Fin S.card := ⟨i.val,by omega⟩
  let jx (j : Fin k) : Fin S.card := ⟨k+j.val,by omega⟩
  let P (i : Fin k) := S.orderEmbOfFin rfl (ix i)
  let Q (j : Fin k) := S.orderEmbOfFin rfl (jx j)
  have pm (i : Fin k) : P i ∈ S := S.orderEmbOfFin_mem rfl _
  have qm (j : Fin k) : Q j ∈ S := S.orderEmbOfFin_mem rfl _
  have pq (i j : Fin k) : P i < Q j := (S.orderEmbOfFin rfl).strictMono (show ix i < jx j by change i.val < k+j.val; omega)
  let f (a : Fin k × Fin k) := P a.1+Q a.2
  let fiber (n : ℕ) := (univ : Finset (Fin k × Fin k)).filter (fun a => f a=n)
  have coords (i j : Fin k) : (3*x<P i ∧ P i≤4*x) ∧ (3*x<Q j ∧ Q j≤4*x) :=
    ⟨mem_Ioc.mp (mem_filter.mp (pm i)).1,mem_Ioc.mp (mem_filter.mp (qm j)).1⟩
  have identifies (n : ℕ) {a b : Fin k × Fin k} (ha : a ∈ fiber n) (hb : b ∈ fiber n)
      (i : a.1=b.1) : a=b := by
    have ea := (mem_filter.mp ha).2
    have eb := (mem_filter.mp hb).2
    change P a.1+Q a.2=n at ea
    change P b.1+Q b.2=n at eb
    rw [i] at ea
    have qq : Q a.2=Q b.2 := by omega
    have j := (S.orderEmbOfFin rfl).injective qq
    have j' : k+a.2.val=k+b.2.val := congrArg Fin.val j
    exact Prod.ext i (Fin.ext (by omega))
  have maps (a : Fin k × Fin k) (_ : a ∈ (univ : Finset (Fin k × Fin k))) : f a ∈ T := by
    have c := coords a.1 a.2
    apply mem_range.mpr
    change P a.1+Q a.2 < 8*x+1
    omega
  have cap (n : ℕ) (_ : n ∈ T) : (fiber n).card ≤ k := by
    calc
      (fiber n).card ≤ (univ : Finset (Fin k)).card := by
        apply card_le_card_of_injOn (fun a : Fin k × Fin k => a.1) (fun _ _ => mem_univ _)
        intro a ha b hb hab
        exact identifies n ha hb hab
      _ = k := by simp
  let D := k/4
  have k4 : 4 ≤ k := by have h : 1 ≤ m^6 := Nat.one_le_pow _ _ (by omega); omega
  have d4 : 4*D ≤ k := by dsimp [D]; omega
  have kd : k ≤ 8*D := by dsimp [D]; omega
  have mass : T.card*Z+D*k < Fintype.card (Fin k × Fin k) := by
    simp only [T,card_range,Fintype.card_prod,Fintype.card_fin]
    have za : 16*x*Z ≤ k*k := by simpa [Nat.mul_comm] using divlow
    have da := Nat.mul_le_mul_right k d4
    have spare : Z ≤ x*Z := by simpa using Nat.mul_le_mul_right Z (show 1 ≤ x by omega)
    have positive : 0 < k*k := Nat.mul_pos (by omega) (by omega)
    nlinarith only [za,da,spare,positive]
  let J := T.filter (fun n => Z < (fiber n).card)
  have hj : D ≤ J.card := heavy T f Z D k maps cap mass
  have many : (x:ℝ) ≤ 96*(M.totient:ℝ)*(J.card:ℝ)*Real.log (4*(x:ℝ)) := calc
    _ ≤ 12*(M.totient:ℝ)*k*Real.log (4*(x:ℝ)) := xm.le
    _ ≤ 12*(M.totient:ℝ)*(8*(J.card:ℝ))*Real.log (4*(x:ℝ)) := by
      have use : k ≤ 8*J.card := kd.trans (Nat.mul_le_mul_left 8 hj)
      have use' : (k:ℝ) ≤ 8*(J.card:ℝ) := by exact_mod_cast use
      gcongr
    _ = _ := by ring
  refine ⟨J,many,?_⟩
  intro n hn
  have large := (mem_filter.mp hn).2
  change Z < (fiber n).card at large
  obtain ⟨a,ha⟩ := card_pos.mp (by omega : 0 < (fiber n).card)
  have sum := (mem_filter.mp ha).2
  change P a.1+Q a.2=n at sum
  have c := coords a.1 a.2
  have lo : 6*x < n := by omega
  have hi : n ≤ 8*x := by omega
  have tozero (p : ℕ) (h : p ≡ M-1 [MOD M]) : M ∣ p+1 := by
    have eq := h.add_right 1
    rw [show M-1+1=M by omega] at eq
    exact Nat.modEq_zero_iff_dvd.mp (eq.trans (dvd_refl M).modEq_zero_nat)
  have ap' := dvd_add (tozero _ (mem_filter.mp (pm a.1)).2.2) (tozero _ (mem_filter.mp (qm a.2)).2.2)
  have ap : M ∣ n+2 := by convert ap' using 1 <;> omega
  have bad := forbidden B H n ap (by omega)
  have inj : (fiber n).card ≤ (centralReps n).card := by
    apply card_le_card_of_injOn (fun ij => P ij.1)
    · intro ij hh
      have eq := (mem_filter.mp hh).2
      change P ij.1+Q ij.2=n at eq
      have t := coords ij.1 ij.2
      have lt := pq ij.1 ij.2
      have right : n-P ij.1=Q ij.2 := by omega
      change P ij.1 ∈ (range (n+1)).filter (fun p => p < n-p ∧ n ≤ 3*p ∧ 3*p ≤ 2*n ∧ p.Prime ∧ (n-p).Prime)
      apply mem_filter.mpr
      refine ⟨mem_range.mpr (by omega),by omega,by omega,by omega,(mem_filter.mp (pm ij.1)).2.1,?_⟩
      rw [right]
      exact (mem_filter.mp (qm ij.2)).2.1
    · intro ij ha uv hb hp
      have eq := (S.orderEmbOfFin rfl).injective (show P ij.1=P uv.1 from hp)
      have ev : (ix ij.1).val = (ix uv.1).val := congrArg (fun a : Fin S.card => a.val) eq
      exact identifies n ha hb (Fin.ext ev)
  exact ⟨lo,hi,bad.1,target _ (large.le.trans inj),bad.2⟩

private theorem close_powers (j : ℕ) (hj : 32 ≤ j) : 2*(j+1)^8 ≤ 3*j^8 := by
  have first : 32*(j+1) ≤ 33*j := by omega
  have step := Nat.pow_le_pow_left first 8
  have cmp : 2*33^8 ≤ 3*(32:ℕ)^8 := by decide
  have trans : (2*(j+1)^8)*(32:ℕ)^8 ≤ (3*j^8)*32^8 := calc
    _ = 2*(32*(j+1))^8 := by ring
    _ ≤ 2*(33*j)^8 := Nat.mul_le_mul_left 2 step
    _ = (2*33^8)*j^8 := by ring
    _ ≤ (3*32^8)*j^8 := Nat.mul_le_mul_right _ cmp
    _ = _ := by ring
  exact Nat.le_of_mul_le_mul_right trans (by decide)

theorem dyadic : ∀ B H : ℕ, ∃ C : ℝ, 0 < C ∧ ∃ N : ℕ, ∀ X ≥ N, ∃ J : Finset ℕ, (X:ℝ) ≤ C*(J.card:ℝ)*Real.log (X:ℝ) ∧ ∀ n ∈ J, X ≤ n ∧ n ≤ 2*X ∧ Even n ∧ (X:ℝ) ≤ C*(((Finset.range (n+1)).filter (fun p => p < n-p ∧ n ≤ 3*p ∧ 3*p ≤ 2*n ∧ p.Prime ∧ (n-p).Prime)).card:ℝ)*(Real.log (X:ℝ))^2 ∧ ∀ d ≤ H, ∀ p : ℕ, p.Prime → p ≤ B → ¬ (n-d-p).Prime ∧ ¬ (n+2-d-p).Prime := by
  classical
  intro B H
  let M := (B+H+2).factorial
  have ph : 0 < (M.totient:ℝ) := by exact_mod_cast Nat.totient_pos.mpr (Nat.factorial_pos _)
  refine ⟨max (576*(M.totient:ℝ)) (27648*(M.totient:ℝ)^2),lt_of_lt_of_le (by positivity : 0 < 576*(M.totient:ℝ)) (le_max_left _ _),?_⟩
  obtain ⟨N,hN⟩ := result B H
  refine ⟨6*(N+33)^8+1,?_⟩
  intro X hX
  have ex : ∃ t : ℕ, X ≤ 6*t^8 := ⟨X+1,by
    have big : X+1 ≤ (X+1)^8 := Nat.le_self_pow (by decide) _
    omega⟩
  let m := Nat.find ex
  have above : X ≤ 6*m^8 := Nat.find_spec ex
  have large : N+33 < m := by
    by_contra! no
    have a := Nat.pow_le_pow_left no 8
    omega
  have mpos : 0 < m := by omega
  obtain ⟨j,eq⟩ := Nat.exists_eq_succ_of_ne_zero mpos.ne'
  have before : 6*j^8 < X := by
    have less : j < Nat.find ex := by change j < m; omega
    exact Nat.lt_of_not_ge (Nat.find_min ex less)
  have close := close_powers j (by omega)
  have upper : 8*m^8 ≤ 2*X := by
    rw [eq]
    change 8*(j+1)^8 ≤ 2*X
    omega
  obtain ⟨J,amount,hJ⟩ := hN m (by omega)
  have xb : 4*m^8 ≤ X := by omega
  have xp : 0 < (m:ℝ)^8 := by positivity
  have mpow : 0 < m^8 := pow_pos mpos _
  have ln : 0 ≤ Real.log (4*(m:ℝ)^8) := Real.log_nonneg (by exact_mod_cast (show 1 ≤ 4*m^8 by omega))
  have logle : Real.log (4*(m:ℝ)^8) ≤ Real.log (X:ℝ) := Real.log_le_log (by positivity) (by exact_mod_cast xb)
  have sq (t : ℕ) (h : ((m^8:ℕ):ℝ) ≤ 4608*(M.totient:ℝ)^2*t*(Real.log (4*((m^8:ℕ):ℝ)))^2) :
       (X:ℝ) ≤ 27648*(M.totient:ℝ)^2*t*(Real.log (X:ℝ))^2 := by
    push_cast at h
    calc
      (X:ℝ) ≤ 6*(m:ℝ)^8 := by exact_mod_cast above
      _ ≤ 6*(4608*(M.totient:ℝ)^2*t*(Real.log (4*(m:ℝ)^8))^2) := mul_le_mul_of_nonneg_left h (by norm_num)
      _ ≤ 6*(4608*(M.totient:ℝ)^2*t*(Real.log (X:ℝ))^2) := by gcongr
      _ = _ := by ring
  have count : (X:ℝ) ≤ max (576*(M.totient:ℝ)) (27648*(M.totient:ℝ)^2)*(J.card:ℝ)*Real.log (X:ℝ) := by
    push_cast at amount
    have logpos := ln.trans logle
    calc
      (X:ℝ) ≤ 6*(m:ℝ)^8 := by exact_mod_cast above
      _ ≤ 6*(96*(M.totient:ℝ)*(J.card:ℝ)*Real.log (4*(m:ℝ)^8)) := mul_le_mul_of_nonneg_left amount (by norm_num)
      _ = 576*(M.totient:ℝ)*(J.card:ℝ)*Real.log (4*(m:ℝ)^8) := by ring
      _ ≤ _ := by gcongr; exact le_max_left _ _
  refine ⟨J,count,?_⟩
  intro n hn
  obtain ⟨lo,hi,even,rep,excluded⟩ := hJ n hn
  refine ⟨by omega,by omega,even,(sq _ rep).trans ?_,excluded⟩
  gcongr
  exact le_max_right _ _

end CentralDesertDensity

theorem Conjectures.Goldbach.BinaryShiftAbundantCentralDesert : ∀ B H : ℕ, ∃ C : ℝ, 0 < C ∧ ∃ N : ℕ, ∀ X ≥ N, ∃ J : Finset ℕ, (X:ℝ) ≤ C*(J.card:ℝ)*Real.log (X:ℝ) ∧ ∀ n ∈ J, X ≤ n ∧ n ≤ 2*X ∧ Even n ∧ (X:ℝ) ≤ C*(((Finset.range (n+1)).filter (fun p => p < n-p ∧ n ≤ 3*p ∧ 3*p ≤ 2*n ∧ p.Prime ∧ (n-p).Prime)).card:ℝ)*(Real.log (X:ℝ))^2 ∧ ∀ d ≤ H, ∀ p : ℕ, p.Prime → p ≤ B → ¬ (n-d-p).Prime ∧ ¬ (n+2-d-p).Prime := CentralDesertDensity.dyadic
