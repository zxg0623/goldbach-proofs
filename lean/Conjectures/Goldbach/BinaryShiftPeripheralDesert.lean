import Mathlib

open Finset Filter
open scoped BigOperators Topology

namespace ShiftedPeripheralDesert

/-- Two disjoint blocks of primes in the same progression, each longer than
the square root of the search range by any specified constant factor. -/
private theorem many (M C : ℕ) (hM : 0 < M) :
    ∃ m : ℕ, 1 ≤ m ∧ 4*(C+1)*m^2 ≤
      ((Ioc 0 (m^4)).filter (fun p => p.Prime ∧ p ≡ M-1 [MOD M])).card := by
  let : NeZero M := ⟨hM.ne'⟩
  have unit : (M-1).Coprime M := (Nat.coprime_self_sub_left (by omega)).2 (by simp)
  let F : ℝ → ℝ := fun x => (((Ioc 0 ⌊x⌋₊).filter (fun p : ℕ => p.Prime ∧ p ≡ M-1 [MOD M])).card : ℝ) * Real.log x / x
  have lim : Tendsto F atTop (𝓝 ((M.totient:ℝ)⁻¹)) := Nat.tendsto_card_prime_modEq_mul_log_div_atTop unit
  have hφ : 0 < (M.totient:ℝ) := by exact_mod_cast Nat.totient_pos.mpr hM
  have ev : ∀ᶠ x in atTop, 1/(2*(M.totient:ℝ)) < F x := (tendsto_order.1 lim).1 _ (by rw [inv_eq_one_div]; gcongr <;> linarith)
  obtain ⟨x₀,hx⟩ := eventually_atTop.1 ev
  obtain ⟨b,hb⟩ := exists_nat_gt x₀
  let m := b+32*M.totient*(C+1)+2
  have hm : 1 ≤ m := by dsimp [m]; omega
  have hr : 1 ≤ (m:ℝ) := by exact_mod_cast hm
  have hm0 : 0 < (m:ℝ) := by linarith
  have hb' : (b:ℝ) ≤ m := by exact_mod_cast (show b ≤ m by dsimp [m]; omega)
  have powle : (m:ℝ) ≤ (m:ℝ)^4 := by nlinarith [sq_nonneg ((m:ℝ)^2-1),sq_nonneg ((m:ℝ)-1)]
  let S := (Ioc 0 (m^4)).filter (fun p : ℕ => p.Prime ∧ p ≡ M-1 [MOD M])
  have W := hx ((m:ℝ)^4) (by linarith)
  change 1/(2*(M.totient:ℝ)) < _ * _ / _ at W
  have fl : ⌊(m:ℝ)^4⌋₊=m^4 := by rw [← Nat.cast_pow, Nat.floor_natCast]
  rw [fl,Real.log_pow] at W
  change 1/(2*(M.totient:ℝ)) < (S.card:ℝ) * (4*Real.log (m:ℝ)) / (m:ℝ)^4 at W
  have W' := (div_lt_div_iff₀ (by positivity) (by positivity)).mp W
  have logs : Real.log (m:ℝ) ≤ m := by linarith [Real.log_le_sub_one_of_pos hm0]
  have bound : (m:ℝ)^4 < m*(8*(M.totient:ℝ)*S.card) := calc
    (m:ℝ)^4 < (S.card:ℝ) * (4*Real.log (m:ℝ)) * (2*(M.totient:ℝ)) := by linarith
    _ ≤ (S.card:ℝ) * (4*m) * (2*(M.totient:ℝ)) := by gcongr
    _ = _ := by ring
  have cubic : (m:ℝ)^3 < 8*(M.totient:ℝ)*S.card := by
    apply (mul_lt_mul_iff_right₀ hm0).mp
    convert bound using 1 <;> ring
  have bigNat : 32*M.totient*(C+1) ≤ m := by dsimp [m]; omega
  have big : 32*(M.totient:ℝ)*((C:ℝ)+1) ≤ m := by exact_mod_cast bigNat
  have lhs : (8*(M.totient:ℝ)) * (4*((C:ℝ)+1)*m^2) ≤ m^3 := calc
    _ = (32*(M.totient:ℝ)*((C:ℝ)+1))*m^2 := by ring
    _ ≤ (m:ℝ)*m^2 := by gcongr
    _ = _ := by ring
  have smaller := (mul_lt_mul_iff_right₀ (by positivity : 0 < 8*(M.totient:ℝ))).mp (lhs.trans_lt cubic)
  refine ⟨m,hm,?_⟩
  exact_mod_cast smaller.le

private def representations (n : ℕ) := (range (n+1)).filter (fun p => p < n-p ∧ p.Prime ∧ (n-p).Prime)

/-- Count distinct unordered representations by splitting the ordered list of
AP primes at its median and applying the pigeonhole principle to their sums. -/
private theorem rich (M K : ℕ) (hM : 0<M) :
    ∃ n : ℕ, M ∣ n+2 ∧ K < (representations n).card := by
  obtain ⟨m,hm,number⟩ := many M K hM
  let S := (Ioc 0 (m^4)).filter (fun p : ℕ => p.Prime ∧ p ≡ M-1 [MOD M])
  let k := 2*(K+1)*m^2
  have room : 2*k ≤ S.card := by change 2*(2*(K+1)*m^2) ≤ _; convert number using 1 <;> ring
  let ix (i : Fin k) : Fin S.card := ⟨i.val,by omega⟩
  let jx (j : Fin k) : Fin S.card := ⟨k+j.val,by omega⟩
  let P (i : Fin k) := S.orderEmbOfFin rfl (ix i)
  let Q (j : Fin k) := S.orderEmbOfFin rfl (jx j)
  have pm (i : Fin k) : P i ∈ S := S.orderEmbOfFin_mem rfl _
  have qm (j : Fin k) : Q j ∈ S := S.orderEmbOfFin_mem rfl _
  have pq (i j : Fin k) : P i < Q j := (S.orderEmbOfFin rfl).strictMono (show ix i < jx j from (by change i.val < k+j.val; omega))
  let f (ij : Fin k × Fin k) := P ij.1+Q ij.2
  have maps (ij : Fin k × Fin k) (_ : ij ∈ (univ : Finset (Fin k × Fin k))) : f ij ∈ range (2*m^4+1) := by
    have left := (mem_Ioc.mp (mem_filter.mp (pm ij.1)).1).2
    have right := (mem_Ioc.mp (mem_filter.mp (qm ij.2)).1).2
    apply mem_range.mpr
    dsimp [f]
    omega
  have size : (range (2*m^4+1)).card*K < (univ : Finset (Fin k × Fin k)).card := by
    simp only [card_range,card_univ,Fintype.card_prod,Fintype.card_fin]
    dsimp [k]
    have hpow : 1 ≤ m^4 := Nat.one_le_pow 4 m (by omega)
    nlinarith [Nat.mul_le_mul_left K hpow,Nat.zero_le (K^2*m^4)]
  obtain ⟨n,_,h⟩ := exists_lt_card_fiber_of_mul_lt_card_of_maps_to maps size
  let fiber := (univ : Finset (Fin k × Fin k)).filter (fun z => f z=n)
  change K < fiber.card at h
  have bound : fiber.card ≤ (representations n).card := by
    apply card_le_card_of_injOn (fun ij => P ij.1)
    · intro ij hi
      change P ij.1 ∈ (range (n+1)).filter (fun p => p < n-p ∧ p.Prime ∧ (n-p).Prime)
      have sum := (mem_filter.mp hi).2
      change P ij.1+Q ij.2=n at sum
      have lt := pq ij.1 ij.2
      have eq : n-P ij.1=Q ij.2 := by omega
      exact mem_filter.mpr ⟨mem_range.mpr (by omega),by omega,(mem_filter.mp (pm ij.1)).2.1,eq ▸ (mem_filter.mp (qm ij.2)).2.1⟩
    · intro a ha b hb hp
      have pa : P a.1=P b.1 := hp
      have ixe := (S.orderEmbOfFin rfl).injective pa
      have first : a.1=b.1 := Fin.ext (show (ix a.1).val=(ix b.1).val from congrArg Fin.val ixe)
      have aa := (mem_filter.mp ha).2
      have bb := (mem_filter.mp hb).2
      change P a.1+Q a.2=n at aa
      change P b.1+Q b.2=n at bb
      have qe : Q a.2=Q b.2 := by omega
      have jxe := congrArg Fin.val ((S.orderEmbOfFin rfl).injective qe)
      have second : a.2=b.2 := Fin.ext (by change k+a.2.val=k+b.2.val at jxe; omega)
      exact Prod.ext first second
  obtain ⟨ij,hi⟩ := card_pos.mp (by omega : 0 < fiber.card)
  have eq := (mem_filter.mp hi).2
  change P ij.1 + Q ij.2=n at eq
  have left := (mem_filter.mp (pm ij.1)).2.2
  have right := (mem_filter.mp (qm ij.2)).2.2
  have tozero (p : ℕ) (hh : p ≡ M-1 [MOD M]) : M ∣ p+1 := by
    have eq := hh.add_right 1
    rw [show M-1+1=M by omega] at eq
    exact Nat.modEq_zero_iff_dvd.mp (eq.trans (dvd_refl M).modEq_zero_nat)
  have div := dvd_add (tozero _ left) (tozero _ right)
  refine ⟨n,?_,h.trans_le bound⟩
  convert div using 1 <;> omega

theorem result : ∀ B H K X : ℕ, ∃ n : ℕ, X ≤ n ∧ Even n ∧ K ≤ ((Finset.range (n+1)).filter (fun p => p < n-p ∧ p.Prime ∧ (n-p).Prime)).card ∧ ∀ d ≤ H, ∀ p : ℕ, p.Prime → p ≤ B → ¬ (n-d-p).Prime ∧ ¬ (n+2-d-p).Prime := by
  intro B H K X
  let M := (B+H+2).factorial
  have hM : 0<M := Nat.factorial_pos _
  obtain ⟨n,ap,rep⟩ := rich M (X+K+2*(B+H)+12) hM
  have size : (representations n).card ≤ n+1 := by
    simpa [representations] using (card_le_card (filter_subset (fun p => p < n-p ∧ p.Prime ∧ (n-p).Prime) (range (n+1))))
  have two : 2 ∣ M := Nat.dvd_factorial (by decide) (by omega)
  have even : Even n := by
    obtain ⟨l,hl⟩ := two.trans ap
    exact ⟨l-1,by omega⟩
  refine ⟨n,by omega,even,by change K ≤ (representations n).card; omega,?_⟩
  intro d hd p hp bound
  have p2 := hp.two_le
  have kill (v k : ℕ) (vk : v+k=n+2) (vpos : 1<v) (small : v ≤ B+H+2) (lt : v<k) : ¬ k.Prime := by
    have dividesM : v ∣ M := Nat.dvd_factorial (by omega) small
    have divides := dividesM.trans ap
    rw [← vk] at divides
    have hk : v ∣ k := (Nat.dvd_add_right (dvd_refl v)).mp divides
    intro prime
    rcases (Nat.dvd_prime prime).mp hk with h | h <;> omega
  exact ⟨kill (p+d+2) (n-d-p) (by omega) (by omega) (by omega) (by omega),
         kill (p+d) (n+2-d-p) (by omega) (by omega) (by omega) (by omega)⟩

end ShiftedPeripheralDesert

theorem Conjectures.Goldbach.BinaryShiftPeripheralDesert : ∀ B H K X : ℕ, ∃ n : ℕ, X ≤ n ∧ Even n ∧ K ≤ ((Finset.range (n+1)).filter (fun p => p < n-p ∧ p.Prime ∧ (n-p).Prime)).card ∧ ∀ d ≤ H, ∀ p : ℕ, p.Prime → p ≤ B → ¬ (n-d-p).Prime ∧ ¬ (n+2-d-p).Prime := ShiftedPeripheralDesert.result
