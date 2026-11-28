import Mathlib
namespace CutpointRightShifts

/-- All nineteen shifts in the specified range simultaneously preserve two
representations on both sides of the same target. -/
theorem shared_of_cover (cover : ∀ n : ℕ, 10^316 ≤ n → n < 10^316 + 2097152 → Even n → ∃ q r : ℕ, q < r ∧ r ≤ 2712663 ∧ q.Prime ∧ r.Prime ∧ (n-q).Prime ∧ (n-r).Prime) : let G := fun m : ℕ => ((Finset.range (m+1)).filter (fun p => Nat.Prime p ∧ Nat.Prime (m-p))).card; ∀ n : ℕ, 10^316 + 1048576 ≤ n → n < 10^316 + 2097152 → Even n → ∀ e : ℕ, 2 ≤ e → e ≤ 20 → (2^e)^2 ≤ n ∧ 2 ≤ G (n-2^e) ∧ 2 ≤ G (n+2-2^e) := by
  dsimp only
  intro n lo hi he e low high
  have four : 4 ≤ (2:ℕ)^e := by
    calc 4 = (2:ℕ)^2 := by decide
         _ ≤ _ := Nat.pow_le_pow_right (by decide) low
  have cap : (2:ℕ)^e ≤ 1048576 := by
    calc (2:ℕ)^e ≤ 2^20 := Nat.pow_le_pow_right (by decide) high
         _ = 1048576 := by decide
  have evenPower : Even ((2:ℕ)^e) := (show Even (2:ℕ) from ⟨1,rfl⟩).pow_of_ne_zero (by omega)
  change 10000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000001048576 ≤ n at lo
  change n < 10000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000002097152 at hi
  have smallPow : ((2:ℕ)^e)^2 ≤ n := by
    have le := Nat.mul_le_mul cap cap
    rw [pow_two]
    omega
  have counted (m : ℕ) (hm : 10000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 ≤ m) (ht : m < 10000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000002097152) (ev : Even m) :
      2 ≤ ((Finset.range (m+1)).filter (fun p => p.Prime ∧ (m-p).Prime)).card := by
    obtain ⟨q,r,qr,bd,pq,pr,cq,cr⟩ := cover m hm ht ev
    apply Finset.one_lt_card.mpr
    exact ⟨q,Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (by omega),pq,cq⟩,
           r,Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (by omega),pr,cr⟩,ne_of_lt qr⟩
  obtain ⟨k,hk⟩ := he
  obtain ⟨l,hl⟩ := evenPower
  exact ⟨smallPow,
    counted (n-2^e) (by omega) (by omega) ⟨k-l,by omega⟩,
    counted (n+2-2^e) (by omega) (by omega) ⟨k+1-l,by omega⟩⟩

end CutpointRightShifts

theorem Conjectures.Goldbach.CutpointSharedExponents : (∀ n : ℕ, 10^316 ≤ n → n < 10^316 + 2097152 → Even n → ∃ q r : ℕ, q < r ∧ r ≤ 2712663 ∧ q.Prime ∧ r.Prime ∧ (n-q).Prime ∧ (n-r).Prime) → (let G := fun m : ℕ => ((Finset.range (m+1)).filter (fun p => Nat.Prime p ∧ Nat.Prime (m-p))).card; ∀ n : ℕ, 10^316 + 1048576 ≤ n → n < 10^316 + 2097152 → Even n → ∀ e : ℕ, 2 ≤ e → e ≤ 20 → (2^e)^2 ≤ n ∧ 2 ≤ G (n-2^e) ∧ 2 ≤ G (n+2-2^e)) := CutpointRightShifts.shared_of_cover
