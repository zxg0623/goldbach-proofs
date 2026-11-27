import Conjectures.Goldbach.DeepThreeQuartersExceptionalZeroCriterion
import Conjectures.Goldbach.EstermannAlmostAllPolylog

open Goldbach

/-! A uniform prime number theorem in reduced residue classes, allowing one
exceptional real zero. The logarithmic derivative, a first Riesz mean,
unsmoothing and character orthogonality give the stated bound.
Classical context: Montgomery and Vaughan, Multiplicative Number Theory I,
Chapter 11, Theorem 11.16 and Corollary 11.17. -/

namespace Conjectures.Goldbach.ExceptionalZeroProgressionsProof.ExceptionalZeroCatalogue

open Complex Set Filter DirichletCharacter
open scoped Topology Classical

noncomputable def regular {r : ℕ} [NeZero r] (χ : DirichletCharacter ℂ r) : ℂ → ℂ :=
  if χ=1 then LFunctionTrivChar₁ r else LFunction χ

def genuine {r : ℕ} [NeZero r] (χ : DirichletCharacter ℂ r) (z : ℂ) : Prop :=
  (χ ≠ 1 ∨ z ≠ 1) ∧ LFunction χ z=0

theorem differentiable_regular {r : ℕ} [NeZero r] (χ : DirichletCharacter ℂ r) :
    Differentiable ℂ (regular χ) := by
  by_cases h : χ=1
  · rw [regular,ite_eq_left h]
    exact differentiable_LFunctionTrivChar₁ r
  · rw [regular,ite_eq_right h]
    exact differentiable_LFunction h

theorem regular_zero {r : ℕ} [NeZero r] (χ : DirichletCharacter ℂ r) (z : ℂ) :
    regular χ z=0 ↔ genuine χ z := by
  classical
  by_cases h : χ=1
  · subst χ
    rw [regular,ite_eq_left rfl]
    by_cases atone : z=1
    · subst z
      exact iff_of_false (LFunctionTrivChar₁_apply_one_ne_zero r) (by simp [genuine])
    · rw [LFunctionTrivChar₁,Function.update_of_ne atone]
      simp [genuine,atone,sub_ne_zero.mpr atone,LFunctionTrivChar]
  · simp [regular,h,genuine]

theorem regular_ne {r : ℕ} [NeZero r] (χ : DirichletCharacter ℂ r) (z : ℂ)
    (h : 1 ≤ z.re) : regular χ z ≠ 0 := by
  intro H
  obtain ⟨ok,zero⟩ := (regular_zero χ z).mp H
  exact LFunction_ne_zero_of_one_le_re χ ok h zero

/-- Zeros on any compact set are finite, with their true analytic orders. -/
theorem zeros_finite {r : ℕ} [NeZero r] (χ : DirichletCharacter ℂ r) {K : Set ℂ} (hK : IsCompact K) :
    {z : ℂ | z ∈ K ∧ genuine χ z}.Finite := by
  have H : AnalyticOnNhd ℂ (regular χ) univ := fun z _ => (differentiable_regular χ).analyticAt z
  have no := H.preimage_zero_mem_codiscrete (regular_ne χ 1 (by simp))
  have nearK : (regular χ) ⁻¹' ({0} : Set ℂ)ᶜ ∈ codiscreteWithin K :=
    (Filter.codiscreteWithin_mono (subset_univ K)) no
  have f := hK.finite_sdiff_of_mem_codiscreteWithin nearK
  apply f.subset
  intro z hz
  exact ⟨hz.1,by simp [(regular_zero χ z).mpr hz.2]⟩

theorem order_positive {r : ℕ} [NeZero r] (χ : DirichletCharacter ℂ r) {z : ℂ} (h : genuine χ z) :
    0 < analyticOrderNatAt (regular χ) z ∧
      analyticOrderAt (regular χ) z=(analyticOrderNatAt (regular χ) z : ℕ∞) := by
  have A (w : ℂ) := (differentiable_regular χ).analyticAt w
  have fne : regular χ ≠ 0 := fun eqn => regular_ne χ 1 (by simp) (congrFun eqn 1)
  have finite := mt (AnalyticOnNhd.analyticOrderAt_eq_top_iff_eq_zero z A).mp fne
  have val := Nat.cast_analyticOrderNatAt finite
  refine ⟨?_,val.symm⟩
  by_contra! hz
  have top : analyticOrderAt (regular χ) z=0 := by rw [← val,show analyticOrderNatAt (regular χ) z=0 by omega]; rfl
  exact ((A z).analyticOrderAt_eq_zero.mp top) ((regular_zero χ z).mpr h)

/-- Every actual zero is repeated exactly its analytic multiplicity. -/
theorem zero_multiset {r : ℕ} [NeZero r] (χ : DirichletCharacter ℂ r) {K : Set ℂ}
    (hK : IsCompact K) : ∃ Z : Multiset ℂ,
      (∀ z : ℂ, z ∈ Z ↔ z ∈ K ∧ genuine χ z) ∧
      ∀ z ∈ Z, (Z.count z : ℕ∞)=analyticOrderAt (regular χ) z := by
  classical
  let A := (zeros_finite χ hK).toFinset
  let Z := ∑ z ∈ A, Multiset.replicate (analyticOrderNatAt (regular χ) z) z
  have mult (z : ℂ) : Z.count z = if z ∈ A then analyticOrderNatAt (regular χ) z else 0 := by
    simp only [Z,Multiset.count_sum',Multiset.count_replicate,Finset.sum_ite_eq']
  have mem (z : ℂ) : z ∈ Z ↔ z ∈ K ∧ genuine χ z := by
    rw [← Multiset.count_pos,mult]
    by_cases hz : z ∈ A
    · have H : z ∈ K ∧ genuine χ z := (zeros_finite χ hK).mem_toFinset.mp hz
      exact iff_of_true (by simpa [hz] using (order_positive χ H.2).1) H
    · have H : ¬(z ∈ K ∧ genuine χ z) := fun h => hz ((zeros_finite χ hK).mem_toFinset.mpr h)
      simp [hz,H]
  refine ⟨Z,mem,?_⟩
  intro z hz
  have H := (mem z).mp hz
  rw [mult,ite_eq_left ((zeros_finite χ hK).mem_toFinset.mpr H)]
  exact (order_positive χ H.2).2.symm

/-- One open neighborhood works simultaneously for every character at
every positive modulus up to R, including the regularized principals. -/
theorem bounded_strip (R : ℕ) (T : ℝ) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ (r : ℕ) [NeZero r], r ≤ R → ∀ (χ : DirichletCharacter ℂ r) (z : ℂ),
      |z.im| ≤ T → 1-δ ≤ z.re → ¬genuine χ z := by
  classical
  let U : Set ℂ := ⋂ (k : Fin R) (χ : DirichletCharacter ℂ (k.val+1)), (regular χ) ⁻¹' ({0} : Set ℂ)ᶜ
  have hu : IsOpen U := isOpen_iInter_of_finite (fun k => isOpen_iInter_of_finite (fun χ =>
    isClosed_singleton.isOpen_compl.preimage (differentiable_regular χ).continuous))
  let v (t : ℝ) := (1:ℂ)+(t:ℂ)*I
  let line := v '' Icc (-T) T
  have comp : IsCompact line := isCompact_Icc.image (by dsimp [v]; fun_prop)
  have sub : line ⊆ U := by
    rintro z ⟨t,_,rfl⟩
    refine mem_iInter.mpr fun k => mem_iInter.mpr fun χ => ?_
    exact regular_ne χ _ (by simp [v])
  obtain ⟨δ,hd,inside⟩ := comp.exists_cthickening_subset_open hu sub
  refine ⟨δ,hd,?_⟩
  intro r _ hr χ z ht hz
  by_cases right : 1 ≤ z.re
  · exact mt (regular_zero χ z).mpr (regular_ne χ z right)
  have imag : v z.im ∈ line := ⟨z.im,abs_le.mp ht,rfl⟩
  have E : z-v z.im=((z.re-1:ℝ):ℂ) := by apply Complex.ext <;> simp [v]
  have dist : dist z (v z.im) ≤ δ := by
    rw [dist_eq_norm,E,Complex.norm_real,Real.norm_eq_abs,abs_of_nonpos (by linarith)]
    linarith
  have u := inside (Metric.mem_cthickening_of_dist_le z (v z.im) δ line imag dist)
  cases r with
  | zero => exact (NeZero.ne 0 rfl).elim
  | succ n =>
    let i : Fin R := ⟨n,by omega⟩
    have H : regular χ z ≠ 0 := mem_iInter.mp (mem_iInter.mp u i) χ
    exact mt (regular_zero χ z).mpr H

end Conjectures.Goldbach.ExceptionalZeroProgressionsProof.ExceptionalZeroCatalogue

namespace Conjectures.Goldbach.ExceptionalZeroProgressionsProof.NearOneZeroMultiplicity

open Complex DirichletCharacter Metric Set Filter
open GoldbachSmoothing
open scoped Classical Topology

theorem right_majorant {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)
    {σ : ℝ} (hσ : 1 < σ) (t : ℝ) :
    ‖logDeriv (LFunction χ) (⟨σ,t⟩ : ℂ)‖ ≤ (-logDeriv riemannZeta (σ:ℂ)).re := by
  let f : ℕ → ℂ := fun n => (ArithmeticFunction.vonMangoldt n : ℂ)
  let s : ℂ := ⟨σ,t⟩
  have hf : Summable (LSeries.term f (σ:ℂ)) :=
    ArithmeticFunction.LSeriesSummable_vonMangoldt (by simpa using hσ)
  have hm (n : ℕ) : ‖LSeries.term (twistedCoefficient χ) s n‖ ≤ ‖LSeries.term f (σ:ℂ) n‖ := by
    rw [show ‖LSeries.term f (σ:ℂ) n‖ = ‖LSeries.term f s n‖ by simp [LSeries.norm_term_eq,s]]
    apply LSeries.norm_term_le
    change ‖χ (n:ZMod q)*(ArithmeticFunction.vonMangoldt n:ℂ)‖ ≤ ‖(ArithmeticFunction.vonMangoldt n:ℂ)‖
    rw [norm_mul]
    exact mul_le_of_le_one_left (norm_nonneg _) (χ.norm_le_one _)
  have hn := hf.norm.of_nonneg_of_le (fun _ => norm_nonneg _) hm
  have real_term (n : ℕ) : (LSeries.term f (σ:ℂ) n).re = ‖LSeries.term f (σ:ℂ) n‖ := by
    open scoped ComplexOrder in
    have nonneg := LSeries.term_nonneg (a:=f) (n:=n)
      (show 0 ≤ f n from Complex.zero_le_real.mpr ArithmeticFunction.vonMangoldt_nonneg) σ
    exact congrArg Complex.re (Complex.eq_coe_norm_of_nonneg nonneg)
  have hzeta : LSeries f (σ:ℂ) = -logDeriv riemannZeta (σ:ℂ) := by
    simpa [logDeriv, neg_div] using
      (ArithmeticFunction.LSeries_vonMangoldt_eq_deriv_riemannZeta_div (s:=(σ:ℂ)) (by simpa using hσ))
  calc
    _ = ‖LSeries (twistedCoefficient χ) s‖ := by
      rw [LSeries_twistedCoefficient_eq χ (show 1<s.re from hσ),norm_neg]
    _ ≤ ∑' n, ‖LSeries.term f (σ:ℂ) n‖ := (norm_tsum_le_tsum_norm hn).trans (hn.tsum_le_tsum hm hf.norm)
    _ = (LSeries f (σ:ℂ)).re := by rw [LSeries,Complex.re_tsum hf]; simp_rw [real_term]
    _ = _ := congrArg Complex.re hzeta

/-- Isolate the pole of zeta on the whole real segment [1,2]. -/
theorem right_edge :
    ∃ D : ℝ, 0 ≤ D ∧ ∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q)
      (η t : ℝ), 0 < η → η ≤ 1 →
        ‖logDeriv (LFunction χ) (⟨1+η,t⟩ : ℂ)‖ ≤ 1/η + D := by
  let P : DirichletCharacter ℂ 1 := 1
  let f := regularizedL P
  have analytic (z : ℂ) := analytic_regularizedL P z (mem_univ z)
  have cont : ContinuousOn (fun x : ℝ => ‖logDeriv f (x:ℂ)‖) (Icc 1 2) := by
    intro x hx
    have ne : f (x:ℂ) ≠ 0 := ExceptionalZeroCatalogue.regular_ne P _ hx.1
    have c := (analytic _).deriv.continuousAt.div (analytic _).continuousAt ne
    exact (c.comp (Complex.continuous_ofReal.continuousAt)).norm.continuousWithinAt
  obtain ⟨D,hD⟩ := isCompact_Icc.bddAbove_image cont
  refine ⟨max D 0,le_max_right _ _,?_⟩
  intro q _ χ η t hη hη'
  let x := 1+η
  have hx : 1<x := by dsimp [x]; linarith
  have hxc : (x:ℂ) ≠ 1 := by exact_mod_cast hx.ne'
  have hζ : LFunction P (x:ℂ) ≠ 0 := LFunction_ne_zero_of_one_le_re P (Or.inr hxc) hx.le
  have eqn := logDeriv_regularizedL_eq P hxc hζ
  have eqn' : -logDeriv riemannZeta (x:ℂ) = ((1/η:ℝ):ℂ)-logDeriv f (x:ℂ) := by
    rw [LFunction_modOne_eq] at eqn
    have sub : (x:ℂ)-1=(η:ℂ) := by simp [x]
    simpa [f,P,principalFlag,sub] using (show -logDeriv riemannZeta (x:ℂ) =
      principalFlag P / ((x:ℂ)-1)-logDeriv (regularizedL P) (x:ℂ) by rw [eqn]; ring)
  have H := hD (mem_image_of_mem (fun u : ℝ => ‖logDeriv f (u:ℂ)‖)
    (show x ∈ Icc 1 2 from ⟨hx.le,by dsimp [x];linarith⟩))
  refine (right_majorant χ hx t).trans ?_
  rw [eqn',sub_re,ofReal_re]
  linarith [neg_le_abs (logDeriv f (x:ℂ)).re,abs_re_le_norm (logDeriv f (x:ℂ)),le_max_left D 0]

/-- The regularized logarithmic derivative and all zeros in the disk
of radius 33/25 have an error at most 694400 times the log-height. -/
theorem local_expansion {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) (t : ℝ) :
    ∃ Z : Finset ℂ, (∀ z, z ∈ Z ↔ z ∈ closedBall (⟨2,t⟩:ℂ) (33/25) ∧
        ExceptionalZeroCatalogue.genuine χ z) ∧
      ∀ η : ℝ, 0 < η → η ≤ 1 → let s : ℂ := ⟨1+η,t⟩
        ‖logDeriv (regularizedL χ) s - ∑ z ∈ Z, (analyticOrderNatAt (regularizedL χ) z : ℂ)/(s-z)‖
          ≤ 694400 * logHeight q t := by
  let f := regularizedL χ
  let c : ℂ := ⟨2,t⟩
  let H := 2*(q:ℝ)*(2+|t|)
  have hq : (1:ℝ) ≤ q := by exact_mod_cast NeZero.pos q
  have ht := abs_nonneg t
  have hK : 2+|t| ≤ H := by dsimp [H]; nlinarith [mul_nonneg (sub_nonneg.mpr hq) (by positivity : 0≤2+|t|)]
  have hH : 4 ≤ H := by dsimp [H]; nlinarith [mul_nonneg (by positivity : 0 ≤ (q:ℝ)) ht]
  have hqH : (q:ℝ) ≤ H := by dsimp [H]; nlinarith [mul_nonneg (by positivity : 0 ≤ (q:ℝ)) ht]
  have hpos : 0 < H := by linarith
  have hAnchor : (1/4:ℝ) ≤ ‖f c‖ := norm_regularizedL_anchor χ t
  have hn : f c ≠ 0 := norm_pos_iff.mp (by linarith)
  have growth (w : ℂ) (hw : w ∈ closedBall c (24/25*(3/2))) : ‖f w‖ ≤ H^8 * ‖f c‖ := by
    have dist := mem_closedBall_iff_norm.mp hw
    have hre := abs_le.mp ((abs_re_le_norm (w-c)).trans dist)
    change -_ ≤ w.re-2 ∧ _ at hre
    have hr : (1/8:ℝ) ≤ w.re := by linarith [hre.1]
    have hg := GoldbachGrhGrowth.norm_regularizedLFunction_le χ hr
    have hraw : ‖f w‖ ≤ 25*q*(1+‖w‖)^2 := by
      by_cases hχ : χ=1 <;> simpa [f,regularizedL,hχ] using hg
    have hcn : ‖c‖ ≤ 2+|t| := by simpa [c] using norm_le_abs_re_add_abs_im c
    have hwH : 1+‖w‖ ≤ 3*H := by linarith only [norm_le_norm_sub_add w c,dist,hcn,hK,hH]
    have h5 : (4:ℝ)^5 ≤ H^5 := pow_le_pow_left₀ (by norm_num) hH 5
    calc
      _ ≤ 25*q*(1+‖w‖)^2 := hraw
      _ ≤ 25*H*(3*H)^2 := by gcongr
      _ = 225*H^3 := by ring
      _ ≤ (H^5/4)*H^3 := mul_le_mul_of_nonneg_right (by norm_num at h5;linarith) (by positivity)
      _ = H^8*(1/4) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left hAnchor (by positivity)
  obtain ⟨Z,hZ,_,approx⟩ := GoldbachGrhLogDerivative.logDeriv_partial_fraction_disk
    (c:=c) (R:=(3/2:ℝ)) (f:=f) (B:=H^8) (by norm_num)
    ((analytic_regularizedL χ).mono (subset_univ _)) hn
    (le_trans (by norm_num : (2:ℝ)≤4^8) (pow_le_pow_left₀ (by norm_num) hH 8)) growth
  refine ⟨Z,?_,?_⟩
  · intro z
    change z ∈ (↑Z : Set ℂ) ↔ _
    rw [hZ]
    change (_ ∧ f z=0) ↔ _
    rw [show (22/25*(3/2):ℝ)=33/25 by norm_num]
    exact and_congr_right fun _ => ExceptionalZeroCatalogue.regular_zero χ z
  · intro η hη hη'
    let s : ℂ := ⟨1+η,t⟩
    have sub : s-c=((η-1:ℝ):ℂ) := by apply Complex.ext <;> simp [s,c] <;> ring
    have mem : s ∈ closedBall c (83/100*(3/2)) := by
      rw [mem_closedBall_iff_norm,sub,Complex.norm_real,Real.norm_eq_abs,abs_of_nonpos (by linarith)]
      linarith
    have hs : f s ≠ 0 := ExceptionalZeroCatalogue.regular_ne χ s (by change 1≤1+η;linarith)
    have h := approx s mem hs
    rw [Real.log_pow] at h
    change _ ≤ 694400 * Real.log H
    convert h using 1 <;> norm_num <;> ring

noncomputable def kernel (s z : ℂ) : ℝ := (s-z).re / Complex.normSq (s-z)

theorem kernel_eq (s z : ℂ) (n : ℕ) :
    ((n:ℂ)/(s-z)).re = n*kernel s z := by
  simp [kernel,Complex.div_re,mul_div_assoc]

theorem disk_potential :
    ∃ D : ℝ, 0 ≤ D ∧ ∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q)
      (t η : ℝ), 0 < η → η ≤ 1 → ∀ S : Finset ℂ,
        (∀ z ∈ S, z ∈ closedBall (⟨2,t⟩:ℂ) (33/25) ∧ ExceptionalZeroCatalogue.genuine χ z) →
        let s : ℂ := ⟨1+η,t⟩
        ∑ z ∈ S, (analyticOrderNatAt (regularizedL χ) z : ℝ)*kernel s z ≤
          (logDeriv (LFunction χ) s).re + (principalFlag χ/(s-1)).re + 694400*logHeight q t ∧
        ∑ z ∈ S, (analyticOrderNatAt (regularizedL χ) z : ℝ)*kernel s z ≤
          2/η + D + 694400*logHeight q t := by
  obtain ⟨D,hD,right⟩ := right_edge
  refine ⟨D,hD,?_⟩
  intro q _ χ t η hη hη' S hS s
  obtain ⟨Z,mem,apr⟩ := local_expansion χ t
  have hs : 1<s.re := by change 1<1+η;linarith
  have hn : s ≠ 1 := fun e => (by simpa [e] using hs : False)
  have hL := LFunction_ne_zero_of_one_le_re χ (Or.inr hn) hs.le
  let weight := fun z => (analyticOrderNatAt (regularizedL χ) z : ℝ)*kernel s z
  have sub : S ⊆ Z := fun z hz => (mem z).mpr (hS z hz)
  have hw (z : ℂ) (hz : z ∈ Z) : 0 ≤ weight z := by
    have h := ((mem z).mp hz).2
    have hzre : z.re < 1 := lt_of_not_ge fun e => ExceptionalZeroCatalogue.regular_ne χ z e
      ((ExceptionalZeroCatalogue.regular_zero χ z).mpr h)
    exact mul_nonneg (Nat.cast_nonneg _) (div_nonneg (sub_nonneg.mpr (hzre.trans hs).le) (normSq_nonneg _))
  have cmp : ∑ z ∈ S, weight z ≤ ∑ z ∈ Z, weight z :=
    Finset.sum_le_sum_of_subset_of_nonneg sub fun z hz _ => hw z hz
  let total : ℂ := ∑ z ∈ Z, (analyticOrderNatAt (regularizedL χ) z : ℂ)/(s-z)
  have reTot : total.re = ∑ z ∈ Z, weight z := by simp [total,Complex.re_sum,kernel_eq,weight]
  have major := abs_re_le_norm (logDeriv (regularizedL χ) s-total)
  have below := (abs_le.mp (major.trans (apr η hη hη'))).1
  rw [sub_re,reTot,logDeriv_regularizedL_eq χ hn hL,add_re] at below
  have bound : ∑ z ∈ S, weight z ≤ (logDeriv (LFunction χ) s).re +
      (principalFlag χ/(s-1)).re + 694400*logHeight q t := by linarith
  refine ⟨bound,?_⟩
  have flag : ‖principalFlag χ‖ ≤ 1 := by by_cases e : χ=1 <;> simp [principalFlag,e]
  have dist : η ≤ ‖s-1‖ := by
    have a := (le_abs_self (s-1).re).trans (abs_re_le_norm (s-1))
    simpa [s] using a
  have pf := (re_le_norm (principalFlag χ/(s-1))).trans
    (by rw [norm_div];exact div_le_div₀ zero_le_one flag hη dist : ‖principalFlag χ/(s-1)‖ ≤ 1/η)
  have r := (re_le_norm (logDeriv (LFunction χ) s)).trans (right q χ η t hη hη')
  change ∑ z ∈ S, weight z ≤ _
  linarith [show (2:ℝ)/η = 1/η+1/η by ring]

/-- Each near-one zero contributes almost its full multiplicity to the
Poisson kernel at horizontal distance 8h. -/
theorem near_kernel {t h : ℝ} (hh : 0<h) {z : ℂ}
    (lo : 1-h ≤ z.re) (hi : z.re ≤ 1) (ht : |z.im-t| ≤ h) :
    3 ≤ 32*h*kernel (⟨1+8*h,t⟩:ℂ) z := by
  let a := 1+8*h-z.re
  let b := t-z.im
  have a0 : 8*h ≤ a := by dsimp [a];linarith
  have a1 : a ≤ 9*h := by dsimp [a];linarith
  have ap : 0 < a := by linarith
  have b1 : |b| ≤ h := by simpa [b,abs_sub_comm] using ht
  have sq1 := pow_le_pow_left₀ ap.le a1 2
  have sq2 := (sq_le_sq₀ (abs_nonneg b) hh.le).mpr b1
  rw [sq_abs] at sq2
  change 3 ≤ 32*h*(a/(a*a+b*b))
  rw [← mul_div_assoc,le_div_iff₀ (add_pos_of_pos_of_nonneg (mul_pos ap ap) (mul_self_nonneg b))]
  nlinarith only [sq1,sq2,mul_le_mul_of_nonneg_left a0 hh.le,sq_nonneg h]

theorem rectangle_mass :
    ∃ D : ℝ, 0 ≤ D ∧ ∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q)
      (t h : ℝ), 0<h → h≤1/8 → ∀ S : Finset ℂ,
      (∀ z ∈ S, 1-h ≤ z.re ∧ |z.im-t| ≤ h ∧ ExceptionalZeroCatalogue.genuine χ z) →
      let M := (∑ z ∈ S, analyticOrderNatAt (regularizedL χ) z : ℕ)
      3*(M:ℝ) ≤ 8+32*h*(D+694400*logHeight q t) ∧
        (χ ≠ 1 → 3*(M:ℝ) ≤ 4+32*h*(D+694400*logHeight q t)) := by
  obtain ⟨D,hD,potential⟩ := disk_potential
  obtain ⟨A,hA,right⟩ := right_edge
  refine ⟨max D A,hD.trans (le_max_left _ _),?_⟩
  intro q _ χ t h hh hh' S hS M
  let s : ℂ := ⟨1+8*h,t⟩
  have upper (z : ℂ) (hz : z ∈ S) : z.re ≤ 1 := le_of_lt (lt_of_not_ge fun e =>
    ExceptionalZeroCatalogue.regular_ne χ z e ((ExceptionalZeroCatalogue.regular_zero χ z).mpr (hS z hz).2.2))
  have inside (z : ℂ) (hz : z ∈ S) :
      z ∈ closedBall (⟨2,t⟩:ℂ) (33/25) ∧ ExceptionalZeroCatalogue.genuine χ z := by
    refine ⟨?_,(hS z hz).2.2⟩
    rw [mem_closedBall_iff_norm]
    have k := norm_le_abs_re_add_abs_im (z-(⟨2,t⟩:ℂ))
    change ‖_‖ ≤ |z.re-2|+|z.im-t| at k
    rw [abs_of_nonpos (by linarith [upper z hz] : z.re-2 ≤ 0)] at k
    linarith [(hS z hz).1,(hS z hz).2.1]
  let W := ∑ z ∈ S, (analyticOrderNatAt (regularizedL χ) z:ℝ)*kernel s z
  have weighted : 3*(M:ℝ) ≤ 32*h*W := by
    dsimp only [M,W]
    push_cast
    rw [Finset.mul_sum,Finset.mul_sum]
    refine Finset.sum_le_sum fun z hz => ?_
    have k := near_kernel hh (hS z hz).1 (upper z hz) (hS z hz).2.1
    calc
      _ ≤ (32*h*kernel s z)*(analyticOrderNatAt (regularizedL χ) z:ℝ) :=
        mul_le_mul_of_nonneg_right k (Nat.cast_nonneg _)
      _ = _ := by ring
  have h8 : 0<8*h := by positivity
  have h8' : 8*h≤1 := by linarith
  obtain ⟨p₁,p₂⟩ := potential q χ t (8*h) h8 h8' S inside
  have simp2 : 32*h*(2/(8*h))=8 := by field_simp;ring
  have simp1 : 32*h*(1/(8*h))=4 := by field_simp;ring
  constructor
  · calc
      _ ≤ 32*h*W := weighted
      _ ≤ 32*h*(2/(8*h)+D+694400*logHeight q t) := mul_le_mul_of_nonneg_left p₂ (by positivity)
      _ = 8+32*h*(D+694400*logHeight q t) := by linarith only [simp2]
      _ ≤ _ := by gcongr; exact le_max_left _ _
  · intro hn
    have P := (re_le_norm (logDeriv (LFunction χ) s)).trans (right q χ (8*h) t h8 h8')
    change W ≤ (logDeriv (LFunction χ) s).re + (principalFlag χ/(s-1)).re + _ at p₁
    simp [principalFlag,hn] at p₁
    have p : W ≤ 1/(8*h)+A+694400*logHeight q t := by linarith
    calc
      _ ≤ 32*h*W := weighted
      _ ≤ 32*h*(1/(8*h)+A+694400*logHeight q t) := mul_le_mul_of_nonneg_left p (by positivity)
      _ = 4+32*h*(A+694400*logHeight q t) := by linarith only [simp1]
      _ ≤ _ := by gcongr; exact le_max_right _ _

/-- In a logarithmically shrinking box every nonprincipal character
has at most one zero counted with multiplicity, uniformly in height. -/
theorem isolated :
    ∃ c : ℝ, 0<c ∧ ∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q)
      (t : ℝ) (S : Finset ℂ), let h := c/logHeight q t
      (∀ z ∈ S, 1-h ≤ z.re ∧ |z.im-t| ≤ h ∧ ExceptionalZeroCatalogue.genuine χ z) →
      let M := ∑ z ∈ S, analyticOrderNatAt (regularizedL χ) z
      M ≤ 2 ∧ (χ ≠ 1 → M ≤ 1) := by
  obtain ⟨D,hD,rect⟩ := rectangle_mass
  let A := D+694401
  have hA : 1 ≤ A := by dsimp [A];linarith
  have hAp : 0<A := by linarith
  let c := 1/(64*A)
  have hc : 0<c := by dsimp [c];positivity
  refine ⟨c,hc,?_⟩
  intro q _ χ t S h hS M
  let L := logHeight q t
  have hL : 1 ≤ L := logHeight_ge_one q t
  have hLp : 0<L := by linarith
  have hh : 0<h := div_pos hc hLp
  have hh' : h≤1/8 := by
    change 1/(64*A)/L ≤ 1/8
    rw [div_div]
    apply one_div_le_one_div_of_le (by norm_num)
    nlinarith [one_le_mul_of_one_le_of_one_le hA hL]
  have bound : D+694400*L ≤ A*L := by
    dsimp [A];nlinarith [mul_nonneg hD (sub_nonneg.mpr hL)]
  have cost : 32*h*(D+694400*L) ≤ 1/2 := calc
    _ ≤ 32*h*(A*L) := mul_le_mul_of_nonneg_left bound (by positivity)
    _ = 1/2 := by change 32*(1/(64*A)/L)*(A*L)=_;field_simp;ring
  have ⟨p₁,p₂⟩ := rect q χ t h hh hh' S hS
  change 3*(M:ℝ) ≤ 8+32*h*(D+694400*L) at p₁
  constructor
  · by_contra! H
    have H' : (3:ℝ) ≤ M := by exact_mod_cast (show 3≤M by omega)
    linarith
  · intro hn
    have p : 3*(M:ℝ) ≤ 4+32*h*(D+694400*L) := p₂ hn
    by_contra! H
    have H' : (2:ℝ) ≤ M := by exact_mod_cast (show 2≤M by omega)
    linarith

end Conjectures.Goldbach.ExceptionalZeroProgressionsProof.NearOneZeroMultiplicity

namespace Conjectures.Goldbach.ExceptionalZeroProgressionsProof.ExceptionalQuadraticUniqueness

open Complex DirichletCharacter Metric Set Filter
open GoldbachSmoothing
open ExceptionalZeroCatalogue NearOneZeroMultiplicity
open scoped Classical Topology ComplexConjugate

private theorem four_character {q : ℕ} [NeZero q] (χ ψ : DirichletCharacter ℂ q)
    (hχ : χ.IsQuadratic) (hψ : ψ.IsQuadratic) {x : ℝ} (hx : 1<x) :
    (logDeriv riemannZeta (x:ℂ)).re + (logDeriv (LFunction χ) (x:ℂ)).re +
      (logDeriv (LFunction ψ) (x:ℂ)).re + (logDeriv (LFunction (χ*ψ)) (x:ℂ)).re ≤ 0 := by
  let f : ℕ → ℂ := fun n => (ArithmeticFunction.vonMangoldt n : ℂ)
  let g := f + twistedCoefficient χ + twistedCoefficient ψ + twistedCoefficient (χ*ψ)
  have hs : 1<(x:ℂ).re := hx
  have hf : LSeriesSummable f (x:ℂ) := ArithmeticFunction.LSeriesSummable_vonMangoldt hs
  have hsum (θ : DirichletCharacter ℂ q) : LSeriesSummable (twistedCoefficient θ) (x:ℂ) :=
    θ.LSeriesSummable_twist_vonMangoldt hs
  have summ : LSeriesSummable g (x:ℂ) := ((hf.add (hsum χ)).add (hsum ψ)).add (hsum _)
  have pos : 0 ≤ (LSeries g (x:ℂ)).re := by
    open scoped ComplexOrder in
    have coeff (n : ℕ) : 0 ≤ g n := by
      have oneplus (θ : DirichletCharacter ℂ q) (hθ : θ.IsQuadratic) : 0≤1+θ (n:ZMod q) := by
        rcases hθ (n:ZMod q) with e|e|e <;> rw [e] <;> norm_num
      have fac : g n = ((1+χ (n:ZMod q))*(1+ψ (n:ZMod q)))*f n := by
        simp [g,twistedCoefficient,f,MulChar.mul_apply];ring
      rw [fac]
      exact mul_nonneg (mul_nonneg (oneplus χ hχ) (oneplus ψ hψ))
        (Complex.zero_le_real.mpr ArithmeticFunction.vonMangoldt_nonneg)
    rw [LSeries,Complex.re_tsum summ]
    exact tsum_nonneg fun n => (LSeries.term_nonneg (coeff n) x).1
  have zeta : LSeries f (x:ℂ) = -logDeriv riemannZeta (x:ℂ) := by
    simpa [logDeriv,neg_div] using ArithmeticFunction.LSeries_vonMangoldt_eq_deriv_riemannZeta_div hs
  dsimp only [g] at pos
  rw [LSeries_add ((hf.add (hsum χ)).add (hsum ψ)) (hsum _),
    LSeries_add (hf.add (hsum χ)) (hsum ψ),LSeries_add hf (hsum χ),zeta,
    LSeries_twistedCoefficient_eq χ hs,LSeries_twistedCoefficient_eq ψ hs,
    LSeries_twistedCoefficient_eq (χ*ψ) hs] at pos
  simp only [add_re,neg_re] at pos
  linarith

private theorem disk_at_zero {h : ℝ} {z : ℂ} (hh : h≤1/8)
    (lo : 1-h ≤ z.re) (hi : z.re ≤ 1) (ht : |z.im|≤h) :
    z ∈ closedBall (⟨2,0⟩:ℂ) (33/25) := by
  rw [mem_closedBall_iff_norm]
  have k := norm_le_abs_re_add_abs_im (z-(⟨2,0⟩:ℂ))
  change ‖_‖ ≤ |z.re-2|+|z.im-0| at k
  rw [sub_zero,abs_of_nonpos (by linarith : z.re-2 ≤ 0)] at k
  linarith

/-- Two distinct quadratic nonprincipal characters at the same modulus
cannot each contribute a zero to the same small box about 1. -/
theorem one_character_at_level :
    ∃ c : ℝ, 0<c ∧ ∀ (q : ℕ) [NeZero q] (χ ψ : DirichletCharacter ℂ q),
      χ.IsQuadratic → ψ.IsQuadratic → χ ≠ 1 → ψ ≠ 1 →
      ∀ (h : ℝ) (z w : ℂ), 0<h → h≤c/logHeight q 0 →
        1-h≤z.re → |z.im|≤h → genuine χ z → 1-h≤w.re → |w.im|≤h → genuine ψ w → χ=ψ := by
  obtain ⟨_,_,potential⟩ := disk_potential
  obtain ⟨D,hD,right⟩ := right_edge
  let C := D+3*694400+1
  have hC : 1 ≤ C := by dsimp [C];linarith
  have Cp : 0<C := by linarith
  let c := 1/(64*C)
  have hc : 0<c := by dsimp [c];positivity
  refine ⟨c,hc,?_⟩
  intro q _ χ ψ hχ hψ nχ nψ h z w hp hsmall hz hiz zz hw hiw zw
  by_contra diff
  have nprod : χ*ψ ≠ 1 := by
    intro e
    exact diff ((eq_inv_of_mul_eq_one_left e).trans hψ.inv)
  let L := logHeight q 0
  have hL : 1 ≤ L := logHeight_ge_one q 0
  have Lp : 0<L := by linarith
  have cap : h ≤ 1/(64*(C*L)) := by
    convert hsmall using 1
    dsimp [c,L];rw [div_div];ring
  have limit : 64*(C*L)*h ≤ 1 := by
    rw [mul_comm];exact (le_div_iff₀ (by positivity)).mp cap
  have h8 : 0<8*h := by positivity
  have h' : h≤1/8 := by
    apply cap.trans
    apply one_div_le_one_div_of_le (by norm_num)
    linarith [one_le_mul_of_one_le_of_one_le hC hL]
  have h8' : 8*h≤1 := by linarith
  let s : ℂ := ⟨1+8*h,0⟩
  let LD := fun (θ : DirichletCharacter ℂ q) => (logDeriv (LFunction θ) s).re
  let E := 694400*L
  have single (θ : DirichletCharacter ℂ q) (nθ : θ ≠ 1) (v : ℂ) (lo : 1-h≤v.re)
      (ti : |v.im|≤h) (zero : genuine θ v) : 3 ≤ 32*h*(LD θ+E) := by
    have upper : v.re ≤ 1 := le_of_lt (lt_of_not_ge fun e => regular_ne θ v e ((regular_zero θ v).mpr zero))
    have k := near_kernel hp lo upper (by simpa using ti : |v.im-0|≤h)
    have pot := (potential q θ 0 (8*h) h8 h8' {v} (by
      intro v' hv; obtain rfl := Finset.mem_singleton.mp hv;exact ⟨disk_at_zero h' lo upper ti,zero⟩)).1
    change _ ≤ LD θ + (principalFlag θ/(s-1)).re + E at pot
    simp [principalFlag,nθ] at pot
    have m : (1:ℝ) ≤ (analyticOrderNatAt (regularizedL θ) v:ℝ) := by
      exact_mod_cast (order_positive θ zero).1
    have kn : 0 ≤ kernel s v := by
      change 0 ≤ (1+8*h-v.re)/_
      exact div_nonneg (by linarith) (normSq_nonneg _)
    exact k.trans (mul_le_mul_of_nonneg_left
      ((le_mul_of_one_le_left kn m).trans pot) (by positivity))
  have empty := (potential q (χ*ψ) 0 (8*h) h8 h8' ∅ (by simp)).1
  change _ ≤ LD (χ*ψ) + (principalFlag (χ*ψ)/(s-1)).re + E at empty
  simp [principalFlag,nprod] at empty
  have comb := four_character χ ψ hχ hψ (show 1<1+8*h by linarith)
  have tot : (logDeriv riemannZeta s).re + LD χ + LD ψ + LD (χ*ψ) ≤ 0 := comb
  have eqn : LFunction (1 : DirichletCharacter ℂ 1) = riemannZeta := LFunction_modOne_eq
  have r := right 1 (1 : DirichletCharacter ℂ 1) (8*h) 0 h8 h8'
  rw [eqn] at r
  have pole : -(logDeriv riemannZeta s).re ≤ 1/(8*h)+D :=
    ((neg_le_abs _).trans (abs_re_le_norm _)).trans r
  have inv : 32*h*(1/(8*h))=4 := by field_simp;ring
  have sum : LD χ+LD ψ+2*E ≤ 1/(8*h)+D+3*E := by linarith
  have both := add_le_add (single χ nχ z hz hiz zz) (single ψ nψ w hw hiw zw)
  have mul := mul_le_mul_of_nonneg_left sum (by positivity : 0≤32*h)
  have cost : D+3*E ≤ C*L := by
    dsimp [C,E];nlinarith [mul_nonneg hD (sub_nonneg.mpr hL)]
  have saving := mul_le_mul_of_nonneg_left cost (by positivity : 0≤32*h)
  linarith only [both,mul,inv,limit,saving]

/- The continuation argument follows the conjugation identity for
primitive real characters in the verified DyadicCellShortPrimeFloor.
Here the quadratic character may have any positive modulus. -/
theorem conjugate_value {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)
    (hχ : χ.IsQuadratic) (hn : χ ≠ 1) (s : ℂ) : LFunction χ (conj s) = conj (LFunction χ s) := by
  let f := LFunction χ
  let g := conj ∘ f ∘ conj
  have hf := differentiable_LFunction hn
  have hg : Differentiable ℂ g := fun z => by
    simpa only [g,Complex.conj_conj] using (hf (conj z)).conj_conj
  have hr (z : ℂ) (hz : 1<z.re) : f (conj z) = conj (f z) := by
    dsimp [f]
    rw [χ.LFunction_eq_LSeries (by simpa using hz),χ.LFunction_eq_LSeries hz]
    change (∑' n, LSeries.term _ (conj z) n) = conj (∑' n, LSeries.term _ z n)
    rw [Complex.conj_tsum]
    apply tsum_congr
    intro n
    by_cases e : n=0
    · subst n;simp
    rw [LSeries.term_of_ne_zero e,LSeries.term_of_ne_zero e]
    have arg : (n:ℂ).arg ≠ Real.pi := by
      rw [show (n:ℂ)=((n:ℝ):ℂ) from rfl,Complex.arg_ofReal_of_nonneg (Nat.cast_nonneg n)]
      exact Real.pi_pos.ne
    rw [Complex.cpow_conj _ _ arg,map_div₀]
    change χ (n:ZMod q) / _ = conj (χ (n:ZMod q)) / _
    rcases hχ (n:ZMod q) with a|a|a <;> simp [a]
  have same : g =ᶠ[𝓝 (2:ℂ)] f := by
    filter_upwards [(show IsOpen {u : ℂ | (1:ℝ)<u.re} from
      isOpen_lt continuous_const Complex.continuous_re).mem_nhds
      (show (1:ℝ)<(2:ℂ).re by norm_num)] with z hz
    simp only [g,Function.comp_apply,hr z hz,Complex.conj_conj]
  have all : g = f := (hg.differentiableOn.analyticOnNhd isOpen_univ).eq_of_eventuallyEq
    (hf.differentiableOn.analyticOnNhd isOpen_univ) same
  have eqn := congrFun all s
  change conj (f (conj s))=f s at eqn
  simpa [f] using congrArg conj eqn

theorem simple_real_at_level :
    ∃ c : ℝ, 0<c ∧ ∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q),
      χ.IsQuadratic → χ ≠ 1 → ∀ (h : ℝ), h≤c/logHeight q 0 →
      ∀ z w : ℂ, 1-h≤z.re → |z.im|≤h → genuine χ z →
        1-h≤w.re → |w.im|≤h → genuine χ w →
        z=w ∧ z.im=0 ∧ analyticOrderNatAt (LFunction χ) z=1 := by
  obtain ⟨c,hc,unique⟩ := isolated
  refine ⟨c,hc,?_⟩
  intro q _ χ qr hn h hsmall z w hz hiz zz hw hiw zw
  have hfit (v : ℂ) (lo : 1-h≤v.re) (ht : |v.im|≤h) (zero : genuine χ v) :
      1-c/logHeight q 0 ≤ v.re ∧ |v.im-0|≤c/logHeight q 0 ∧ genuine χ v :=
    ⟨by linarith,by simpa using ht.trans hsmall,zero⟩
  have eqv (u : ℂ) (lo : 1-h≤u.re) (ht : |u.im|≤h) (zero : genuine χ u) : z=u := by
    by_contra e
    have b := (unique q χ 0 {z,u} (by
      intro v hv
      simp only [Finset.mem_insert,Finset.mem_singleton] at hv
      rcases hv with rfl|rfl
      · exact hfit _ hz hiz zz
      · exact hfit _ lo ht zero)).2 hn
    simp only [Finset.sum_insert (by simpa using e : z ∉ ({u}:Finset ℂ)),Finset.sum_singleton] at b
    have pz : 0<analyticOrderNatAt (regularizedL χ) z := (order_positive χ zz).1
    have pu : 0<analyticOrderNatAt (regularizedL χ) u := (order_positive χ zero).1
    omega
  have conjz : genuine χ (conj z) := ⟨Or.inl hn,by rw [conjugate_value χ qr hn,zz.2,map_zero]⟩
  have real' := congrArg Complex.im (eqv (conj z) (by simpa using hz) (by simpa using hiz) conjz)
  have b := (unique q χ 0 {z} (by
    intro v hv; obtain rfl := Finset.mem_singleton.mp hv;exact hfit _ hz hiz zz)).2 hn
  simp only [Finset.sum_singleton] at b
  have pz : 0<analyticOrderNatAt (regularizedL χ) z := (order_positive χ zz).1
  have f : regularizedL χ = LFunction χ := by simp [regularizedL,hn]
  rw [f] at pz b
  simp only [Complex.conj_im] at real'
  exact ⟨eqv w hw hiw zw,by linarith,by omega⟩

private theorem quadratic_lift {r m : ℕ} [NeZero m] (hr : r ∣ m) (χ : DirichletCharacter ℂ r)
    (qr : χ.IsQuadratic) : (changeLevel hr χ).IsQuadratic := by
  rw [MulChar.isQuadratic_iff_sq_eq_one,← map_pow,qr.sq_eq_one,map_one]

/-- Compare the two primitive characters at their least common multiple.
Its logarithm costs at most a factor of two. -/
theorem landau_page :
    ∃ c : ℝ, 0<c ∧ ∀ (Q r s : ℕ) [NeZero r] [NeZero s],
      r≤Q → s≤Q → ∀ (χ : DirichletCharacter ℂ r) (ψ : DirichletCharacter ℂ s),
      χ.IsPrimitive → ψ.IsPrimitive → χ.IsQuadratic → ψ.IsQuadratic → χ ≠ 1 → ψ ≠ 1 →
      ∀ z w : ℂ, let h := c/Real.log (4*(Q:ℝ))
        1-h≤z.re → |z.im|≤h → genuine χ z → 1-h≤w.re → |w.im|≤h → genuine ψ w →
        r=s ∧ HEq χ ψ ∧ z=w ∧ z.im=0 ∧ analyticOrderNatAt (LFunction χ) z=1 := by
  obtain ⟨a,ha,chars⟩ := one_character_at_level
  obtain ⟨b,hb,zeros⟩ := simple_real_at_level
  let c := min a b/2
  have hc : 0<c := div_pos (lt_min ha hb) (by norm_num)
  refine ⟨c,hc,?_⟩
  intro Q r s _ _ hr hs χ ψ pr ps qr qs nχ nψ z w h hz hiz zz hw hiw zw
  let m := Nat.lcm r s
  haveI : NeZero m := ⟨(Nat.lcm_pos (NeZero.pos r) (NeZero.pos s)).ne'⟩
  let L := Real.log (4*(Q:ℝ))
  have Qpos : 0<Q := (NeZero.pos r).trans_le hr
  have Qone : 1≤(Q:ℝ) := by exact_mod_cast Qpos
  have Lpos : 0<L := Real.log_pos (by linarith)
  have height (n : ℕ) [NeZero n] (hn : n≤Q*Q) : logHeight n 0 ≤ 2*L := by
    have np : 0 < (n:ℝ) := by exact_mod_cast NeZero.pos n
    have H : (n:ℝ)≤(Q:ℝ)*(Q:ℝ) := by exact_mod_cast hn
    have H' : 2*(n:ℝ)*(2+|(0:ℝ)|)≤(4*(Q:ℝ))^2 := by simp only [abs_zero,add_zero];nlinarith [sq_nonneg (Q:ℝ)]
    exact (Real.log_le_log (by positivity) H').trans_eq (Real.log_pow _ _)
  have width (n : ℕ) [NeZero n] (hn : n≤Q*Q) (u : ℝ) (hu : min a b ≤ u) : h ≤ u/logHeight n 0 := by
    have A := height n hn
    have Lp : 0<logHeight n 0 := zero_lt_one.trans_le (logHeight_ge_one n 0)
    change c/L ≤ _
    rw [div_le_div_iff₀ Lpos Lp]
    calc
      _ ≤ c*(2*L) := mul_le_mul_of_nonneg_left A hc.le
      _ = min a b*L := by dsimp [c];ring
      _ ≤ _ := mul_le_mul_of_nonneg_right hu Lpos.le
  have hm : m ≤ Q*Q := (Nat.le_of_dvd (Nat.mul_pos (NeZero.pos r) (NeZero.pos s))
    (Nat.lcm_dvd (Nat.dvd_mul_right r s) (Nat.dvd_mul_left s r))).trans (Nat.mul_le_mul hr hs)
  let dr := Nat.dvd_lcm_left r s
  let ds := Nat.dvd_lcm_right r s
  have gn {u : ℕ} [NeZero u] (d : u∣m) (θ : DirichletCharacter ℂ u) (v : ℂ)
      (nt : θ ≠ 1) (zv : genuine θ v) : genuine (changeLevel d θ) v := by
    refine ⟨Or.inl (nt ∘ (changeLevel_eq_one_iff d).mp),?_⟩
    rw [LFunction_changeLevel d θ zv.1,zv.2,zero_mul]
  have eqn := chars m (changeLevel dr χ) (changeLevel ds ψ) (quadratic_lift dr χ qr)
    (quadratic_lift ds ψ qs) (nχ ∘ (changeLevel_eq_one_iff dr).mp) (nψ ∘ (changeLevel_eq_one_iff ds).mp)
    h z w (div_pos hc Lpos) (width m hm a (min_le_left _ _))
    hz hiz (gn dr χ z nχ zz) hw hiw (gn ds ψ w nψ zw)
  have levels : r=s := by
    have e := congrArg DirichletCharacter.conductor eqn
    rwa [conductor_changeLevel,conductor_changeLevel,pr,ps] at e
  subst s
  have equal : χ=ψ := changeLevel_injective dr eqn
  subst ψ
  have hr2 : r≤Q*Q := hr.trans (Nat.le_mul_of_pos_right Q Qpos)
  exact ⟨rfl,HEq.rfl,zeros r χ qr nχ h (width r hr2 b (min_le_right _ _)) z w hz hiz zz hw hiw zw⟩

end Conjectures.Goldbach.ExceptionalZeroProgressionsProof.ExceptionalQuadraticUniqueness

namespace Conjectures.Goldbach.ExceptionalZeroProgressionsProof.DirichletExceptionalZeroRegion

open Complex DirichletCharacter Metric Set
open GoldbachSmoothing
open ExceptionalZeroCatalogue NearOneZeroMultiplicity
open scoped Classical

private theorem positive_polynomial (z : ℂ) (hz : ‖z‖ ≤ 1) :
    0 ≤ 3+4*z.re+(z*z).re := by
  have sq := pow_le_pow_left₀ (norm_nonneg z) hz 2
  rw [Complex.sq_norm,Complex.normSq_apply] at sq
  rw [Complex.mul_re]
  nlinarith [sq_nonneg (1+z.re)]

private theorem three_terms {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)
    (x t : ℝ) (n : ℕ) :
    let f : ℕ → ℂ := fun k => (ArithmeticFunction.vonMangoldt k:ℂ)
    0 ≤ 3*(LSeries.term f (x:ℂ) n).re +
      4*(LSeries.term (twistedCoefficient χ) (⟨x,t⟩:ℂ) n).re +
      (LSeries.term (twistedCoefficient (χ*χ)) (⟨x,2*t⟩:ℂ) n).re := by
  intro f
  by_cases hn : n=0
  · subst n; simp
  have nc : (n:ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hn
  let l := Real.log (n:ℝ)
  let a := Real.exp (-(l*x))
  let phase := fun u : ℝ => Complex.exp (((-(l*u):ℝ):ℂ)*I)
  have factor (u : ℝ) : ((n:ℂ)^(⟨x,u⟩:ℂ))⁻¹ = (a:ℂ)*phase u := by
    rw [cpow_def_of_ne_zero nc,← Complex.exp_neg]
    dsimp only [a,phase]
    rw [Complex.ofReal_exp,← Complex.exp_add,← Complex.natCast_log]
    congr 1
    apply Complex.ext <;> simp [l,mul_re,mul_im]
    all_goals ring
  have ph2 : phase (2*t) = phase t*phase t := by
    dsimp only [phase];rw [← Complex.exp_add];congr 1;push_cast;ring
  have ph0 : phase 0=1 := by simp [phase]
  let d : ℝ := ArithmeticFunction.vonMangoldt n*a
  let u : ℂ := χ (n:ZMod q)*phase t
  have ud : ‖u‖ ≤ 1 := by
    dsimp only [u]
    rw [norm_mul,show ‖phase t‖=1 by simp [phase,Complex.norm_exp],mul_one]
    exact χ.norm_le_one _
  have e0 : LSeries.term f (x:ℂ) n = (d:ℂ) := by
    rw [LSeries.term_of_ne_zero hn,div_eq_mul_inv,show (x:ℂ)=(⟨x,0⟩:ℂ) from rfl,factor,ph0,mul_one]
    simp [d,f]
  have e1 : LSeries.term (twistedCoefficient χ) (⟨x,t⟩:ℂ) n = (d:ℂ)*u := by
    rw [LSeries.term_of_ne_zero hn,div_eq_mul_inv,factor]
    simp [twistedCoefficient,d,u];ring
  have e2 : LSeries.term (twistedCoefficient (χ*χ)) (⟨x,2*t⟩:ℂ) n = (d:ℂ)*(u*u) := by
    rw [LSeries.term_of_ne_zero hn,div_eq_mul_inv,factor,ph2]
    simp [twistedCoefficient,d,u,MulChar.mul_apply];ring
  rw [e0,e1,e2]
  have scale (v : ℂ) : ((d:ℂ)*v).re=d*v.re := by simp [Complex.mul_re]
  simp only [ofReal_re,scale]
  have dn : 0 ≤ d := mul_nonneg ArithmeticFunction.vonMangoldt_nonneg (Real.exp_pos _).le
  linarith only [mul_nonneg dn (positive_polynomial u ud)]

theorem three_four_one {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)
    {x : ℝ} (hx : 1 < x) (t : ℝ) :
    3*(logDeriv riemannZeta (x:ℂ)).re + 4*(logDeriv (LFunction χ) (⟨x,t⟩:ℂ)).re +
      (logDeriv (LFunction (χ*χ)) (⟨x,2*t⟩:ℂ)).re ≤ 0 := by
  let f : ℕ → ℂ := fun n => (ArithmeticFunction.vonMangoldt n:ℂ)
  have h0 : LSeriesSummable f (x:ℂ) := ArithmeticFunction.LSeriesSummable_vonMangoldt hx
  have h1 : LSeriesSummable (twistedCoefficient χ) (⟨x,t⟩:ℂ) := χ.LSeriesSummable_twist_vonMangoldt hx
  have h2 : LSeriesSummable (twistedCoefficient (χ*χ)) (⟨x,2*t⟩:ℂ) :=
    (χ*χ).LSeriesSummable_twist_vonMangoldt hx
  have hzeta : LSeries f (x:ℂ) = -logDeriv riemannZeta (x:ℂ) := by
    simpa [logDeriv,neg_div] using ArithmeticFunction.LSeries_vonMangoldt_eq_deriv_riemannZeta_div
      (s:=(x:ℂ)) (by simpa using hx)
  have total := ((((Complex.hasSum_re h0.hasSum).mul_left 3).add
    ((Complex.hasSum_re h1.hasSum).mul_left 4)).add (Complex.hasSum_re h2.hasSum)).tsum_eq
  have pos := (tsum_nonneg (fun n => three_terms χ x t n)).trans_eq total
  change 0 ≤ 3*(LSeries f (x:ℂ)).re + 4*(LSeries (twistedCoefficient χ) (⟨x,t⟩:ℂ)).re +
    (LSeries (twistedCoefficient (χ*χ)) (⟨x,2*t⟩:ℂ)).re at pos
  rw [hzeta,LSeries_twistedCoefficient_eq χ hx,LSeries_twistedCoefficient_eq (χ*χ) hx] at pos
  simp only [neg_re] at pos
  linarith

private theorem log_double (q : ℕ) [NeZero q] (t : ℝ) :
    logHeight q (2*t) ≤ 2*logHeight q t := by
  let H := 2*(q:ℝ)*(2+|t|)
  have Q1 : (1:ℝ) ≤ q := by exact_mod_cast NeZero.pos q
  have H2 : 2 ≤ H := by
    dsimp [H]
    nlinarith [mul_nonneg (Nat.cast_nonneg q) (abs_nonneg t)]
  change Real.log (2*(q:ℝ)*(2+|2*t|)) ≤ 2*Real.log H
  apply le_trans _ (show Real.log (H^2) = 2*Real.log H by simp).le
  apply Real.log_le_log (by positivity)
  rw [abs_mul,abs_of_nonneg (by norm_num : (0:ℝ) ≤ 2)]
  calc
    _ ≤ 2*H := by dsimp [H]; linarith only [Nat.cast_nonneg (α:=ℝ) q]
    _ ≤ H^2 := by nlinarith [mul_nonneg (sub_nonneg.mpr H2) (show 0 ≤ H by linarith)]

private theorem imaginary_pole {h t : ℝ} (hp : 0 < h) (large : 64*h ≤ |t|) :
    (1/((⟨1+16*h,t⟩:ℂ)-1)).re ≤ 1/(256*h) := by
  have square := (sq_le_sq₀ (show 0 ≤ 64*h by positivity) (abs_nonneg t)).mpr large
  rw [sq_abs] at square
  rw [Complex.div_re,Complex.normSq_apply]
  simp only [sub_re,sub_im,one_re,one_im,add_sub_cancel_left,sub_zero,one_mul,zero_mul,
    zero_div,add_zero]
  apply (div_le_div_iff₀ (add_pos_of_pos_of_nonneg (mul_pos (by positivity) (by positivity))
    (mul_self_nonneg _)) (by positivity)).mpr
  nlinarith only [square,sq_nonneg h]

/-- A near-one zero of any character has quadratic character and
has very small height. Both conclusions hold in the same strip. -/
theorem zero_characteristics :
    ∃ c : ℝ, 0 < c ∧ ∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q),
      ∀ (z : ℂ) (h : ℝ), 0 < h → h ≤ c/logHeight q z.im →
      1-h ≤ z.re → genuine χ z → χ.IsQuadratic ∧ |z.im| < 64*h := by
  obtain ⟨_,_,pot⟩ := disk_potential
  obtain ⟨D,hD,right⟩ := right_edge
  let A := 3*D+6*694400+1
  have A1 : 1 ≤ A := by dsimp [A];linarith
  have Ap : 0 < A := by linarith
  let c := 1/(128*A)
  refine ⟨c,by dsimp [c];positivity,?_⟩
  intro q _ χ z h hp small near zero
  let t := z.im
  let L := logHeight q t
  let s : ℂ := ⟨1+16*h,t⟩
  let s₂ : ℂ := ⟨1+16*h,2*t⟩
  have L1 : 1 ≤ L := logHeight_ge_one q t
  have Lp : 0 < L := by linarith
  have bound : h ≤ 1/(128*(A*L)) := by
    convert small using 1
    dsimp [c,L,t];rw [div_div];ring
  have budget : h*(128*(A*L)) ≤ 1 := (le_div_iff₀ (by positivity)).mp bound
  have smallH : h ≤ 1/16 := by
    apply bound.trans
    apply one_div_le_one_div_of_le (by norm_num)
    linarith [one_le_mul_of_one_le_of_one_le A1 L1]
  have ep : 0 < 16*h := by positivity
  have e1 : 16*h ≤ 1 := by linarith
  have zhi : z.re ≤ 1 := le_of_lt (lt_of_not_ge fun hz => regular_ne χ z hz ((regular_zero χ z).mpr zero))
  have mem : z ∈ closedBall (⟨2,t⟩:ℂ) (33/25) := by
    rw [mem_closedBall_iff_norm]
    have k := norm_le_abs_re_add_abs_im (z-(⟨2,t⟩:ℂ))
    change ‖_‖ ≤ |z.re-2|+|z.im-z.im| at k
    rw [sub_self,abs_zero,add_zero,abs_of_nonpos (by linarith : z.re-2 ≤ 0)] at k
    linarith
  have ab : 0 < 1+16*h-z.re := by linarith
  have k : 1 ≤ 17*h*kernel s z := by
    change 1 ≤ 17*h*((1+16*h-z.re)/((1+16*h-z.re)*(1+16*h-z.re)+(t-z.im)*(t-z.im)))
    rw [show t-z.im=0 from sub_self _,zero_mul,add_zero,← mul_div_assoc,
      le_div_iff₀ (mul_pos ab ab)]
    nlinarith only [mul_nonneg (show 0 ≤ 17*h-(1+16*h-z.re) by linarith) ab.le]
  have kn : 0 ≤ kernel s z := div_nonneg ab.le (normSq_nonneg _)
  have multiplicity : (1:ℝ) ≤ analyticOrderNatAt (regularizedL χ) z := by
    exact_mod_cast (order_positive χ zero).1
  have p1 := (pot q χ t (16*h) ep e1 {z} (by
    intro u hu;obtain rfl := Finset.mem_singleton.mp hu;exact ⟨mem,zero⟩)).1
  change _ ≤ (logDeriv (LFunction χ) s).re + (principalFlag χ/(s-1)).re + 694400*L at p1
  simp only [Finset.sum_singleton] at p1
  have single := k.trans (mul_le_mul_of_nonneg_left ((le_mul_of_one_le_left kn multiplicity).trans p1)
    (by positivity : 0 ≤ 17*h))
  by_contra absent
  have big (quad : χ.IsQuadratic) : 64*h ≤ |t| := le_of_not_gt fun hi => absent ⟨quad,hi⟩
  have pole1 : (principalFlag χ/(s-1)).re ≤ 1/(256*h) := by
    by_cases principal : χ=1
    · have quad : χ.IsQuadratic := MulChar.isQuadratic_iff_sq_eq_one.mpr (by simp [principal])
      simpa [principalFlag,principal,s] using imaginary_pole hp (big quad)
    · simp [principalFlag,principal]
      positivity
  have pole2 : (principalFlag (χ*χ)/(s₂-1)).re ≤ 1/(256*h) := by
    by_cases pair : χ*χ=1
    · have quad : χ.IsQuadratic := MulChar.isQuadratic_iff_sq_eq_one.mpr (by simpa [pow_two] using pair)
      have twice : 64*h ≤ |2*t| := by
        rw [abs_mul,abs_of_nonneg (by norm_num : (0:ℝ) ≤ 2)]
        linarith [big quad,abs_nonneg t]
      simpa [principalFlag,pair,s₂] using imaginary_pole hp twice
    · simp [principalFlag,pair]
      positivity
  have p2 := (pot q (χ*χ) (2*t) (16*h) ep e1 ∅ (by simp)).1
  change _ ≤ (logDeriv (LFunction (χ*χ)) s₂).re + (principalFlag (χ*χ)/(s₂-1)).re +
    694400*logHeight q (2*t) at p2
  simp only [Finset.sum_empty] at p2
  let x := 1+16*h
  have hx : 1 < x := by dsimp [x];linarith
  have tri : 3*(logDeriv riemannZeta (x:ℂ)).re+4*(logDeriv (LFunction χ) s).re+
    (logDeriv (LFunction (χ*χ)) s₂).re ≤ 0 := three_four_one χ hx t
  have R := right 1 (1 : DirichletCharacter ℂ 1) (16*h) 0 ep e1
  rw [LFunction_modOne_eq] at R
  have pole : -(logDeriv riemannZeta (x:ℂ)).re ≤ 1/(16*h)+D :=
    ((neg_le_abs _).trans (abs_re_le_norm _)).trans R
  have log2 : logHeight q (2*t) ≤ 2*L := log_double q t
  have cost : 3*D+6*694400*L ≤ A*L := by
    dsimp [A];nlinarith [mul_nonneg hD (sub_nonneg.mpr L1)]
  have total : 4*((logDeriv (LFunction χ) s).re+(principalFlag χ/(s-1)).re+694400*L) ≤
      3*(1/(16*h))+5*(1/(256*h))+A*L := by
    linarith only [pole,p2,pole1,pole2,tri,log2,cost]
  have fees := mul_le_mul_of_nonneg_left total (by positivity : 0 ≤ 17*h)
  have factor : (17*h)*(3*(1/(16*h))+5*(1/(256*h)))=901/256 := by field_simp;ring
  linarith only [single,budget,fees,factor]

private theorem logHeight_le {r Q : ℕ} [NeZero r] {u T : ℝ}
    (leQ : r ≤ Q) (ht : |u| ≤ T) : logHeight r u ≤ logHeight Q T := by
  have rp : (0:ℝ) < r := by exact_mod_cast NeZero.pos r
  have rq : (r:ℝ) ≤ Q := by exact_mod_cast leQ
  have hT := (abs_nonneg u).trans ht
  unfold logHeight
  rw [abs_of_nonneg hT]
  exact Real.log_le_log (by positivity) (by gcongr)

/-- Across every primitive conductor up to Q and at all heights up to T,
the classical logarithmic strip contains at most one genuine zero, and
its character, ordinate, and analytic multiplicity are determined. -/
theorem full_page :
    ∃ c : ℝ, 0 < c ∧ ∀ (Q r s : ℕ) [NeZero r] [NeZero s],
      r ≤ Q → s ≤ Q → ∀ (T : ℝ), 0 ≤ T →
      ∀ (χ : DirichletCharacter ℂ r) (ψ : DirichletCharacter ℂ s),
      χ.IsPrimitive → ψ.IsPrimitive → ∀ z w : ℂ, let h := c/logHeight Q T
        1-h ≤ z.re → |z.im| ≤ T → genuine χ z →
        1-h ≤ w.re → |w.im| ≤ T → genuine ψ w →
        χ.IsQuadratic ∧ χ ≠ 1 ∧ r=s ∧ HEq χ ψ ∧ z=w ∧ z.im=0 ∧
          analyticOrderNatAt (LFunction χ) z=1 := by
  obtain ⟨a,ha,profile⟩ := zero_characteristics
  obtain ⟨b,hb,page⟩ := ExceptionalQuadraticUniqueness.landau_page
  obtain ⟨δ,hδ,compact⟩ := bounded_strip 1 1
  let c := min a (min (b/64) (min δ (1/64)))
  have hc : 0 < c := lt_min ha (lt_min (by positivity) (lt_min hδ (by norm_num)))
  have ca : c ≤ a := min_le_left _ _
  have cb : c ≤ b/64 := (min_le_right _ _).trans (min_le_left _ _)
  have cd : c ≤ δ := (min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _))
  have c1 : c ≤ 1/64 := (min_le_right _ _).trans ((min_le_right _ _).trans (min_le_right _ _))
  refine ⟨c,hc,?_⟩
  intro Q r s _ _ hr hs T hT χ ψ pr ps z w h hz hiz zz hw hiw zw
  haveI : NeZero Q := ⟨((NeZero.pos r).trans_le hr).ne'⟩
  let L := logHeight Q T
  have L1 : 1 ≤ L := logHeight_ge_one Q T
  have Lp : 0 < L := zero_lt_one.trans_le L1
  have hp : 0 < h := div_pos hc Lp
  have hmax : h ≤ c := div_le_self hc.le L1
  have info (n : ℕ) [NeZero n] (hn : n ≤ Q) (θ : DirichletCharacter ℂ n) (prim : θ.IsPrimitive)
      (u : ℂ) (hu : 1-h ≤ u.re) (ht : |u.im| ≤ T) (zu : genuine θ u) :
      θ.IsQuadratic ∧ θ ≠ 1 ∧ |u.im| ≤ 64*h := by
    have pos : 0 < logHeight n u.im := zero_lt_one.trans_le (logHeight_ge_one n u.im)
    have localWidth : h ≤ a/logHeight n u.im := by
      change c/L ≤ _
      calc
        _ ≤ c/logHeight n u.im := div_le_div_of_nonneg_left hc.le pos (logHeight_le hn ht)
        _ ≤ _ := div_le_div_of_nonneg_right ca pos.le
    obtain ⟨quad,low⟩ := profile n θ u h hp localWidth hu zu
    refine ⟨quad,?_,low.le⟩
    intro principal
    have level : 1 = n := by simpa only [principal,IsPrimitive,conductor_one] using prim
    have smallT : |u.im| ≤ 1 := by linarith [hmax.trans c1]
    exact compact n level.symm.le θ u smallT (by linarith [hmax.trans cd]) zu
  obtain ⟨qr,nχ,zt⟩ := info r hr χ pr z hz hiz zz
  obtain ⟨qs,nψ,wt⟩ := info s hs ψ ps w hw hiw zw
  have ln : Real.log (4*(Q:ℝ)) = logHeight Q 0 := by
    simp only [logHeight,abs_zero,add_zero];congr 1;ring
  have lp : 0 < Real.log (4*(Q:ℝ)) := ln ▸ zero_lt_one.trans_le (logHeight_ge_one Q 0)
  have sup : Real.log (4*(Q:ℝ)) ≤ L := by
    rw [ln];exact logHeight_le (le_refl Q) (by simpa using hT)
  have width : 64*h ≤ b/Real.log (4*(Q:ℝ)) := by
    change 64*(c/L) ≤ _
    rw [← mul_div_assoc]
    calc
      _ ≤ b/L := div_le_div_of_nonneg_right (by linarith only [cb]) Lp.le
      _ ≤ _ := div_le_div_of_nonneg_left hb.le lp sup
  have hw' : h ≤ b/Real.log (4*(Q:ℝ)) := by linarith
  exact ⟨qr,nχ,page Q r s hr hs χ ψ pr ps qr qs nχ nψ z w
    (by linarith) (zt.trans width) zz (by linarith) (wt.trans width) zw⟩

end Conjectures.Goldbach.ExceptionalZeroProgressionsProof.DirichletExceptionalZeroRegion

namespace Conjectures.Goldbach.ExceptionalZeroProgressionsProof.ExceptionalZeroInducedLevels

open Complex DirichletCharacter Set Metric
open GoldbachSmoothing
open ExceptionalZeroCatalogue
open scoped Classical Topology

private noncomputable def factors {r : ℕ} (χ : DirichletCharacter ℂ r) (n : ℕ) (z : ℂ) : ℂ :=
  ∏ p ∈ n.primeFactors, (1-χ p*(p:ℂ)^(-z))

private theorem factors_ne {r : ℕ} (χ : DirichletCharacter ℂ r) (n : ℕ) {z : ℂ}
    (right : 0 < z.re) : factors χ n z ≠ 0 := by
  apply Finset.prod_ne_zero_iff.mpr
  intro p hp
  have prime := Nat.prime_of_mem_primeFactors hp
  have normp : ‖(p:ℂ)^(-z)‖ < 1 := by
    rw [norm_natCast_cpow_of_pos prime.pos,neg_re]
    exact Real.rpow_lt_one_of_one_lt_of_neg (by exact_mod_cast prime.one_lt) (neg_lt_zero.mpr right)
  have normlt : ‖χ p*(p:ℂ)^(-z)‖ < 1 := by
    rw [norm_mul]
    calc
      _ ≤ 1*‖(p:ℂ)^(-z)‖ := mul_le_mul_of_nonneg_right (χ.norm_le_one _) (norm_nonneg _)
      _ < _ := by simpa using normp
  intro zero
  simp only [← sub_eq_zero.mp zero,norm_one,lt_self_iff_false] at normlt

private theorem analytic_factors {r : ℕ} (χ : DirichletCharacter ℂ r) (n : ℕ) (z : ℂ) :
    AnalyticAt ℂ (factors χ n) z := by
  have diff : Differentiable ℂ (factors χ n) := by
    unfold factors
    apply Differentiable.fun_finsetProd
    intro p hp
    have : NeZero p := ⟨(Nat.prime_of_mem_primeFactors hp).ne_zero⟩
    fun_prop
  exact diff.analyticAt z

/-- The equality holds for analytic orders themselves, including order zero.
The pole of the principal character at one is excluded. -/
theorem lift_zero_order {r n : ℕ} [NeZero r] [NeZero n] (d : r ∣ n)
    (χ : DirichletCharacter ℂ r) {z : ℂ} (right : 0 < z.re) (off : z ≠ 1) :
    (genuine (changeLevel d χ) z ↔ genuine χ z) ∧
    analyticOrderAt (LFunction (changeLevel d χ)) z = analyticOrderAt (LFunction χ) z := by
  have fn := factors_ne χ n right
  have g : LFunction (changeLevel d χ) =ᶠ[𝓝 z] (LFunction χ * factors χ n) := by
    filter_upwards [isOpen_compl_singleton.mem_nhds (x:=z) off] with u hu
    exact LFunction_changeLevel d χ (Or.inr hu)
  have ag := analytic_factors χ n z
  have af : AnalyticAt ℂ (LFunction χ) z := by
    apply DifferentiableOn.analyticOnNhd (s:=({1}ᶜ:Set ℂ)) _ isOpen_compl_singleton z off
    exact fun u hu => (differentiableAt_LFunction χ u (Or.inl hu)).differentiableWithinAt
  constructor
  · change ((_ ∨ _) ∧ _ = 0) ↔ ((_ ∨ _) ∧ _ = 0)
    rw [show LFunction (changeLevel d χ) z = LFunction χ z*factors χ n z from g.self_of_nhds]
    simp [off,fn]
  · rw [analyticOrderAt_congr g,analyticOrderAt_mul af ag,ag.analyticOrderAt_eq_zero.mpr fn,add_zero]

def inStrip {n : ℕ} [NeZero n] (χ : DirichletCharacter ℂ n) (h T : ℝ) (z : ℂ) : Prop :=
  1-h ≤ z.re ∧ |z.im| ≤ T ∧ genuine χ z

private theorem lift_heq {r s n : ℕ} (dr : r ∣ n) (ds : s ∣ n)
    (χ : DirichletCharacter ℂ r) (ψ : DirichletCharacter ℂ s) (same : r=s) (eqv : HEq χ ψ) :
    changeLevel dr χ = changeLevel ds ψ := by
  subst s
  cases eq_of_heq eqv
  rfl

theorem all_characters :
    ∃ c : ℝ, 0<c ∧ c≤1/4 ∧ ∀ (Q r s : ℕ) [NeZero r] [NeZero s],
      r≤Q → s≤Q → ∀ (T : ℝ), 0≤T → ∀ (χ : DirichletCharacter ℂ r) (ψ : DirichletCharacter ℂ s)
      (z w : ℂ), let h := c/logHeight Q T
      inStrip χ h T z → inStrip ψ h T w →
      χ.IsQuadratic ∧ χ ≠ 1 ∧ χ.conductor=ψ.conductor ∧ HEq χ.primitiveCharacter ψ.primitiveCharacter ∧
      z=w ∧ z.im=0 ∧ analyticOrderNatAt (LFunction χ) z=1 := by
  obtain ⟨a,ha,page⟩ := DirichletExceptionalZeroRegion.full_page
  let c := min a (1/4)
  have hc : 0<c := lt_min ha (by norm_num)
  have c1 : c ≤ 1/4 := min_le_right _ _
  refine ⟨c,hc,c1,?_⟩
  intro Q r s _ _ hr hs T hT χ ψ z w h hχ hψ
  have : NeZero Q := ⟨((NeZero.pos r).trans_le hr).ne'⟩
  have L1 := logHeight_ge_one Q T
  have Lp : 0<logHeight Q T := zero_lt_one.trans_le L1
  have cap : h ≤ 1/4 := (div_le_self hc.le L1).trans c1
  have width : h ≤ a/logHeight Q T := div_le_div_of_nonneg_right (min_le_left _ _) Lp.le
  have : NeZero χ.conductor := ⟨χ.conductor_ne_zero⟩
  have : NeZero ψ.conductor := ⟨ψ.conductor_ne_zero⟩
  have lift (n : ℕ) [NeZero n] (θ : DirichletCharacter ℂ n) (v : ℂ) (hv : inStrip θ h T v)
      [NeZero θ.conductor] : genuine θ.primitiveCharacter v ∧
      analyticOrderAt (LFunction θ) v = analyticOrderAt (LFunction θ.primitiveCharacter) v := by
    have low := hv.1
    have hi : v.re < 1 := lt_of_not_ge fun e => regular_ne θ v e ((regular_zero θ v).mpr hv.2.2)
    have off : v ≠ 1 := fun e => (by simp [e] at hi)
    have L := lift_zero_order θ.conductor_dvd_level θ.primitiveCharacter (by linarith : 0<v.re) off
    rw [changeLevel_primitiveCharacter] at L
    exact ⟨L.1.mp hv.2.2,L.2⟩
  obtain ⟨uz,order⟩ := lift r χ z hχ
  obtain ⟨uw,_⟩ := lift s ψ w hψ
  have rd := (Nat.le_of_dvd (NeZero.pos r) χ.conductor_dvd_level).trans hr
  have sd := (Nat.le_of_dvd (NeZero.pos s) ψ.conductor_dvd_level).trans hs
  obtain ⟨quad,nontrivial,levels,characters,eqv,real',simple⟩ :=
    page Q χ.conductor ψ.conductor rd sd T hT χ.primitiveCharacter ψ.primitiveCharacter
      χ.primitiveCharacter_isPrimitive ψ.primitiveCharacter_isPrimitive z w
      (by linarith only [hχ.1,width]) hχ.2.1 uz (by linarith only [hψ.1,width]) hψ.2.1 uw
  have quad' : χ.IsQuadratic := by
    rw [← χ.changeLevel_primitiveCharacter,MulChar.isQuadratic_iff_sq_eq_one,← map_pow,quad.sq_eq_one,map_one]
  have non' : χ ≠ 1 := fun e => nontrivial ((changeLevel_eq_one_iff χ.conductor_dvd_level).mp
    (χ.changeLevel_primitiveCharacter.trans e))
  exact ⟨quad',non',levels,characters,eqv,real',(congrArg ENat.toNat order).trans simple⟩

def occurs (n : ℕ) (h T : ℝ) (z : ℂ) : Prop :=
  ∃ hn : NeZero n, ∃ χ : DirichletCharacter ℂ n, @inStrip n hn χ h T z

/-- At each multiple of its primitive conductor exactly one induced
character has the exceptional zero. This counts all levels carrying it. -/
theorem level_count :
    ∃ c : ℝ, 0<c ∧ ∀ (Q r : ℕ) [NeZero r], r≤Q → ∀ (T : ℝ), 0≤T →
    ∀ (χ : DirichletCharacter ℂ r), χ.IsPrimitive → ∀ (z : ℂ),
    let h := c/logHeight Q T
    inStrip χ h T z →
      (∀ (n : ℕ) [NeZero n], n≤Q →
        ((∃! ψ : DirichletCharacter ℂ n, inStrip ψ h T z) ↔ r ∣ n)) ∧
      ((Finset.Ioc 0 Q).filter (fun n => occurs n h T z)).card = Q/r := by
  obtain ⟨c,hc,c1,all⟩ := all_characters
  refine ⟨c,hc,?_⟩
  intro Q r _ hr T hT χ prim z h hz
  have : NeZero Q := ⟨((NeZero.pos r).trans_le hr).ne'⟩
  have cap : h ≤ 1/4 := (div_le_self hc.le (logHeight_ge_one Q T)).trans c1
  have right : 0<z.re := by linarith only [hz.1,cap]
  have hi : z.re<1 := lt_of_not_ge fun e => regular_ne χ z e ((regular_zero χ z).mpr hz.2.2)
  have off : z ≠ 1 := fun e => (by simp [e] at hi)
  have necessary (n : ℕ) [NeZero n] (hn : n ≤ Q) (ψ : DirichletCharacter ℂ n)
      (hw : inStrip ψ h T z) : r ∣ n := by
    have eqn := (all Q r n hr hn T hT χ ψ z z hz hw).2.2.1
    rw [show r=ψ.conductor from prim.symm.trans eqn]
    exact ψ.conductor_dvd_level
  have induced (n : ℕ) [NeZero n] (hn : n ≤ Q) (d : r ∣ n) :
      ∃! ψ : DirichletCharacter ℂ n, inStrip ψ h T z := by
    let φ := changeLevel d χ
    have hv : inStrip φ h T z := ⟨hz.1,hz.2.1,(lift_zero_order d χ right off).1.mpr hz.2.2⟩
    refine ⟨φ,hv,?_⟩
    intro ψ hw
    obtain ⟨_,_,leq,ceq,_⟩ := all Q n n hn hn T hT ψ φ z z hw hv
    simpa only [changeLevel_primitiveCharacter] using
      lift_heq ψ.conductor_dvd_level φ.conductor_dvd_level ψ.primitiveCharacter φ.primitiveCharacter leq ceq
  constructor
  · intro n _ hn
    exact ⟨fun ⟨ψ,hw,_⟩ => necessary n hn ψ hw,induced n hn⟩
  · have seteq : (Finset.Ioc 0 Q).filter (fun n => occurs n h T z) =
        (Finset.Ioc 0 Q).filter (fun n => r ∣ n) := by
      apply Finset.filter_congr
      intro n hn
      obtain ⟨hp,leQ⟩ := Finset.mem_Ioc.mp hn
      have nz : NeZero n := ⟨hp.ne'⟩
      constructor
      · rintro ⟨_,ψ,hw⟩
        exact necessary n leQ ψ hw
      · intro d
        obtain ⟨θ,hw,_⟩ := induced n leQ d
        exact ⟨nz,θ,hw⟩
    rw [seteq,Nat.Ioc_filter_dvd_card_eq_div]

end Conjectures.Goldbach.ExceptionalZeroProgressionsProof.ExceptionalZeroInducedLevels

namespace Conjectures.Goldbach.ExceptionalZeroProgressionsProof.ExceptionalZeroContour

open Complex DirichletCharacter Set Metric
open GoldbachSmoothing GoldbachTwistedMellin
open ExceptionalZeroCatalogue ExceptionalZeroInducedLevels
open scoped Classical Topology

def edge (σ T : ℝ) (u : ℂ) : Prop :=
  σ ≤ u.re ∧ u.re ≤ 2 ∧ |u.im| ≤ T ∧ (u.re=σ ∨ |u.im|=T)

private theorem candidate (b h : ℝ) (hp : 0<h) :
    ∃ σ : ℝ, 1-h/2 ≤ σ ∧ σ ≤ 1-h/4 ∧ h/8 ≤ |σ-b| := by
  by_cases low : b ≤ 1-3*h/8
  · exact ⟨1-h/4,by linarith,le_refl _,(by linarith : h/8 ≤ 1-h/4-b).trans (le_abs_self _)⟩
  · exact ⟨1-h/2,le_refl _,by linarith,(by linarith : h/8 ≤ -(1-h/2-b)).trans (neg_le_abs _)⟩

/-- Keep the same logarithmic width, ordinate, and simple residue throughout
the whole family. The bound applies on the left and both horizontal edges. -/
theorem contour :
    ∃ c C : ℝ, 0<c ∧ c≤1/4 ∧ 0<C ∧ ∀ (Q : ℕ) [NeZero Q] (T : ℝ), 1≤T →
      let L := logHeight Q (T+1)
      let h := c/L
      ∃ σ b : ℝ, 1-h/2≤σ ∧ σ≤1-h/4 ∧
        (∀ (q : ℕ) [NeZero q], q≤Q → ∀ (χ : DirichletCharacter ℂ q) (w : ℂ),
          inStrip χ h (T+1) w → w.re=b ∧ w.im=0 ∧ χ ≠ 1 ∧ analyticOrderNatAt (LFunction χ) w=1) ∧
        (∀ (q : ℕ) [NeZero q], q≤Q → ∀ (χ : DirichletCharacter ℂ q) (u : ℂ),
          edge σ T u →
          (∀ w : ℂ, genuine χ w → h/8 ≤ ‖u-w‖) ∧
          ‖contourLog χ u‖ ≤ C*L^2) := by
  obtain ⟨c,hc,c1,family⟩ := all_characters
  obtain ⟨D,hD,logBound⟩ := norm_logDeriv_regularizedL_le
  let C := D*(1+8/c)+8/c
  refine ⟨c,C,hc,c1,by dsimp [C]; positivity,?_⟩
  intro Q _ T hT L h
  have L1 : 1 ≤ L := logHeight_ge_one Q (T+1)
  have Lp : 0 < L := zero_lt_one.trans_le L1
  have hp : 0 < h := div_pos hc Lp
  have cap : h ≤ 1/4 := (div_le_self hc.le L1).trans c1
  have hr : logHeight Q (T+1) = L := rfl
  have positive : 0 ≤ T+1 := by linarith
  have label : ∃ b : ℝ, ∀ (q : ℕ) [NeZero q], q≤Q →
      ∀ (χ : DirichletCharacter ℂ q) (w : ℂ), inStrip χ h (T+1) w →
        w.re=b ∧ w.im=0 ∧ χ ≠ 1 ∧ analyticOrderNatAt (LFunction χ) w=1 := by
    by_cases hasZero : ∃ (r : ℕ) (nz : NeZero r), r≤Q ∧
        ∃ (ψ : DirichletCharacter ℂ r) (z : ℂ), @inStrip r nz ψ h (T+1) z
    · obtain ⟨r,nz,leQ,ψ,z,hz⟩ := hasZero
      refine ⟨z.re,?_⟩
      intro q _ qQ χ w hw
      obtain ⟨_,non',_,_,equal,real',simple⟩ := family Q q r qQ leQ (T+1) positive χ ψ w z hw hz
      exact ⟨congrArg Complex.re equal,real',non',simple⟩
    · exact ⟨0,fun q i qQ χ w hw => (hasZero ⟨q,i,qQ,χ,w,hw⟩).elim⟩
  obtain ⟨b,label⟩ := label
  obtain ⟨σ,left,right,gap⟩ := candidate b h hp
  refine ⟨σ,b,left,right,label,?_⟩
  intro q _ leQ χ u hu
  obtain ⟨lo,hi,ht,side⟩ := hu
  let d := h/8
  have dp : 0 < d := by dsimp [d];positivity
  have sep (w : ℂ) (zero : genuine χ w) : d ≤ ‖u-w‖ := by
    by_contra! small
    have re := (abs_re_le_norm (u-w)).trans_lt small
    have im := (abs_im_le_norm (u-w)).trans_lt small
    simp only [sub_re,sub_im] at re im
    have wre : 1-h ≤ w.re := by dsimp [d] at re;linarith [(abs_lt.mp re).2]
    have wim : |w.im| ≤ T+1 := by
      have hwi := abs_sub_abs_le_abs_sub w.im u.im
      rw [abs_sub_comm w.im u.im] at hwi
      dsimp [d] at im
      linarith
    obtain ⟨wb,real',_⟩ := label q leQ χ w ⟨wre,wim,zero⟩
    rcases side with es|et
    · rw [es,wb] at re
      exact (not_lt_of_ge gap) re
    · rw [real',sub_zero,et] at im
      dsimp [d] at im
      linarith
  refine ⟨sep,?_⟩
  have Qpos : (0:ℝ) < q := by exact_mod_cast NeZero.pos q
  have qr : (q:ℝ) ≤ Q := by exact_mod_cast leQ
  have LH : logHeight q u.im ≤ L := by
    change Real.log (2*(q:ℝ)*(2+|u.im|)) ≤ Real.log (2*(Q:ℝ)*(2+|T+1|))
    rw [abs_of_nonneg positive]
    apply Real.log_le_log (by positivity)
    gcongr
    linarith
  have reg := logBound q χ u.im u.re d (by linarith) hi dp
    (fun w _ zero => sep w ((regular_zero χ w).mp zero))
  change ‖logDeriv (regularizedL χ) u‖ ≤ D*logHeight q u.im*(1+d⁻¹) at reg
  have poleDist : d ≤ ‖u-1‖ := by
    rcases side with es|et
    · have A := (neg_le_abs (u-1).re).trans (abs_re_le_norm _)
      simp only [sub_re,one_re,es] at A
      dsimp [d];linarith
    · have A := abs_im_le_norm (u-1)
      simp only [sub_im,one_im,sub_zero,et] at A
      dsimp [d];linarith
  have flag : ‖principalFlag χ‖ ≤ 1 := by by_cases e : χ=1 <;> simp [principalFlag,e]
  have pole : ‖principalFlag χ/(u-1)‖ ≤ 1/d := by
    rw [norm_div]
    exact div_le_div₀ zero_le_one flag dp poleDist
  have inv : 1/d=(8/c)*L := by change 1/(c/L/8)=_;field_simp
  have top := norm_add_le (-logDeriv (regularizedL χ) u) (principalFlag χ/(u-1))
  rw [norm_neg] at top
  change ‖-logDeriv (regularizedL χ) u + principalFlag χ/(u-1)‖ ≤ _
  have up : D*logHeight q u.im*(1+d⁻¹) ≤ D*L*(1+d⁻¹) := by gcongr
  rw [← one_div,inv] at up
  rw [← one_div,inv] at reg
  rw [inv] at pole
  have ls : (8/c)*L ≤ (8/c)*L^2 := by
    gcongr; nlinarith [mul_nonneg Lp.le (sub_nonneg.mpr L1)]
  have cost : D*L*(1+(8/c)*L) ≤ D*(1+8/c)*L^2 := by
    calc
      _ ≤ D*L*((1+8/c)*L) := mul_le_mul_of_nonneg_left (by linarith) (by positivity)
      _ = _ := by ring
  dsimp only [C]
  linarith only [top,reg,up,pole,ls,cost]

end Conjectures.Goldbach.ExceptionalZeroProgressionsProof.ExceptionalZeroContour

namespace Conjectures.Goldbach.ExceptionalZeroProgressionsProof.ExceptionalZeroTwistedWindow

open Complex DirichletCharacter Set Metric
open GoldbachSmoothing GoldbachTwistedMellin
open ExceptionalZeroCatalogue ExceptionalZeroInducedLevels ExceptionalZeroContour
open scoped Classical Topology

def active {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) (σ b : ℝ) : Prop :=
  σ < b ∧ b < 1 ∧ genuine χ (b:ℂ)

theorem common_box :
    ∃ c C : ℝ, 0<c ∧ c≤1/4 ∧ 0<C ∧ ∀ (Q : ℕ) [NeZero Q] (T : ℝ), 1≤T →
      let L := logHeight Q (T+1)
      let h := c/L
      ∃ σ b : ℝ, 1-h/2≤σ ∧ σ≤1-h/4 ∧
      ∀ (q : ℕ) [NeZero q], q≤Q → ∀ χ : DirichletCharacter ℂ q,
        (∀ u : ℂ, edge σ T u → ‖contourLog χ u‖ ≤ C*L^2) ∧
        (∀ w ∈ boxZeros χ σ 2 (-T) T, σ < w.re ∧ w.re < 2 ∧ -T < w.im ∧ w.im < T) ∧
        (∀ K : ℂ → ℂ, ∑ w ∈ boxZeros χ σ 2 (-T) T, (analyticOrderNatAt (regularizedL χ) w : ℂ)*K w =
          if active χ σ b then K (b:ℂ) else 0) := by
  obtain ⟨c,C,hc,c1,hC,contour⟩ := ExceptionalZeroContour.contour
  refine ⟨c,C,hc,c1,hC,?_⟩
  intro Q _ T hT L h
  obtain ⟨σ,b,left,right,label,avoid⟩ := contour Q T hT
  have hp : 0<h := div_pos hc (zero_lt_one.trans_le (logHeight_ge_one Q (T+1)))
  refine ⟨σ,b,left,right,?_⟩
  intro q _ leQ χ
  let S := boxZeros χ σ 2 (-T) T
  have info (w : ℂ) (hw : w ∈ S) : w=(b:ℂ) ∧ σ<w.re ∧ w.re<1 ∧ w.im=0 ∧
      genuine χ w ∧ analyticOrderNatAt (regularizedL χ) w=1 := by
    obtain ⟨inside,zero⟩ := (mem_boxZeros χ σ 2 (-T) T w).mp hw
    obtain ⟨re,im⟩ := mem_reProdIm.mp inside
    have low := re.1
    have up := re.2
    have imag := abs_le.mpr im
    have gw := (regular_zero χ w).mp zero
    have strip : inStrip χ h (T+1) w := ⟨by linarith only [low,left,hp],by linarith,gw⟩
    obtain ⟨wb,real',non',simple⟩ := label q leQ χ w strip
    have eqn : w=(b:ℂ) := Complex.ext wb real'
    have strict : σ < w.re := by
      by_contra! le
      have e := le_antisymm le low
      have d := (avoid q leQ χ w ⟨low,up,imag,Or.inl e⟩).1 w gw
      change h/8 ≤ ‖w-w‖ at d
      simp only [sub_self,norm_zero] at d
      linarith
    have below : w.re < 1 := lt_of_not_ge (fun e => regular_ne χ w e zero)
    exact ⟨eqn,strict,below,real',gw,by simpa only [regularizedL,ite_eq_right non'] using simple⟩
  refine ⟨fun u hu => (avoid q leQ χ u hu).2,?_,?_⟩
  · intro w hw
    obtain ⟨_,hs,hu,real',_,_⟩ := info w hw
    exact ⟨hs,by linarith,by linarith,by linarith⟩
  · intro K
    by_cases selected : active χ σ b
    · have member : (b:ℂ) ∈ S := by
        apply (mem_boxZeros χ σ 2 (-T) T _).mpr
        exact ⟨mem_reProdIm.mpr ⟨⟨selected.1.le,by change b≤2;linarith only [selected.2.1]⟩,
          by change -T≤0 ∧ 0≤T; constructor <;> linarith⟩,(regular_zero χ _).mpr selected.2.2⟩
      have one : S = {(b:ℂ)} := Finset.ext (fun w => by
        rw [Finset.mem_singleton];exact ⟨fun hw => (info w hw).1,fun eqn => eqn ▸ member⟩)
      have simple := (info _ member).2.2.2.2.2
      change ∑ w ∈ S, _ = _
      rw [one,Finset.sum_singleton,simple,ite_eq_left selected]
      simp
    · have empty : S = ∅ := Finset.eq_empty_iff_forall_notMem.mpr (by
        intro w hw
        obtain ⟨eqn,lo,hi,_,gw,_⟩ := info w hw
        subst w
        exact selected ⟨lo,hi,gw⟩)
      change ∑ w ∈ S, _ = _
      rw [empty,Finset.sum_empty,ite_eq_right selected]

end Conjectures.Goldbach.ExceptionalZeroProgressionsProof.ExceptionalZeroTwistedWindow

namespace Conjectures.Goldbach.ExceptionalZeroProgressionsProof.ExceptionalZeroRieszEstimate

open Complex DirichletCharacter MeasureTheory Set Filter
open GoldbachSmoothing GoldbachTwistedMellin
open ExceptionalZeroCatalogue ExceptionalZeroInducedLevels ExceptionalZeroContour ExceptionalZeroTwistedWindow
open Conjectures.Goldbach.EstermannAlmostAllPolylog_aux.OAI.LargePrimeGaps (rieszSum rieszSum_mellinInv)
open scoped Classical Topology Interval

noncomputable def weight (x : ℝ) (s : ℂ) := (x:ℂ)^s/(s*(s+1))

noncomputable def integrand {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) (x : ℝ) (s : ℂ) :=
  contourLog χ s*weight x s

private theorem weight_analytic {x : ℝ} (hx : 0<x) {s : ℂ} (hs : 0<s.re) :
    AnalyticAt ℂ (weight x) s := by
  have : NeZero (x:ℂ) := ⟨ofReal_ne_zero.mpr hx.ne'⟩
  have n0 : s ≠ 0 := fun e => (by simp [e] at hs)
  have n1 : s+1 ≠ 0 := by
    intro e
    have := congrArg Complex.re e
    simp at this
    linarith
  exact ((differentiable_const_cpow_of_neZero (x:ℂ)).analyticAt _).div
    (by fun_prop) (mul_ne_zero n0 n1)

theorem weight_bound {x : ℝ} (hx : 0<x) {s : ℂ} (hs : 1/2 ≤ s.re) :
    ‖weight x s‖ ≤ 8*x^s.re/(1+s.im^2) := by
  have s0 : 1/2 ≤ ‖s‖ := hs.trans (re_le_norm _)
  have s1 : 1/2 ≤ ‖s+1‖ := by
    have re := re_le_norm (s+1);simp only [add_re,one_re] at re;linarith
  have p0 : (1/2:ℝ)*(1/2) ≤ ‖s‖*‖s+1‖ := mul_le_mul s0 s1 (by norm_num) (norm_nonneg _)
  have p1 : s.im^2 ≤ ‖s‖*‖s+1‖ := by
    have i1 : |s.im| ≤ ‖s+1‖ := by simpa using abs_im_le_norm (s+1)
    simpa only [←sq,sq_abs] using mul_le_mul (abs_im_le_norm s) i1 (abs_nonneg _) (norm_nonneg _)
  have pos : 0<‖s‖*‖s+1‖ := by linarith
  rw [weight,norm_div,norm_mul,norm_cpow_eq_rpow_re_of_pos hx]
  apply (div_le_div_iff₀ pos (by positivity)).mpr
  have den : 1+s.im^2 ≤ 8*(‖s‖*‖s+1‖) := by linarith only [p0,p1]
  nlinarith only [mul_nonneg (Real.rpow_nonneg hx.le s.re) (sub_nonneg.mpr den)]

private theorem contour_right_eq {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) {s : ℂ} (hs : 1<s.re) :
    contourLog χ s = LSeries (twistedCoefficient χ) s := by
  have off : s ≠ 1 := fun e => (by simp [e] at hs)
  have ne := LFunction_ne_zero_of_one_le_re χ (Or.inr off) hs.le
  rw [contourLog,logDeriv_regularizedL_eq χ off ne,LSeries_twistedCoefficient_eq χ hs]
  ring

private theorem right_inverse {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) {x k : ℝ} (hx : 0<x)
    (hk : 1<k) :
    rieszSum (twistedCoefficient χ) x = (1/(2*Real.pi)) • ∫ t : ℝ, integrand χ x (line k t) := by
  rw [← rieszSum_mellinInv hk.le hx (twistedCoefficient χ) (χ.LSeriesSummable_twist_vonMangoldt hk)]
  unfold mellinInv
  apply congrArg (fun v : ℂ => (1/(2*Real.pi):ℝ) • v)
  apply integral_congr_ae
  filter_upwards with t
  have hz : 1<(line k t).re := by simpa using hk
  dsimp only [integrand,weight]
  rw [contour_right_eq χ hz]
  change (((1/x:ℝ):ℂ)^(-line k t))*(LSeries (twistedCoefficient χ) (line k t)/_) = _
  rw [one_div,Complex.ofReal_inv,inv_cpow_ofReal_nonneg hx.le,cpow_neg,inv_inv]
  unfold line
  ring

private theorem right_integrable {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) {x k : ℝ} (hx : 0<x)
    (hk : 1<k) : Integrable (fun t : ℝ => integrand χ x (line k t)) := by
  have eqn (t : ℝ) : integrand χ x (line k t) = LSeries (twistedCoefficient χ) (line k t)*weight x (line k t) := by
    rw [integrand,contour_right_eq χ (by simpa using hk)]
  simp_rw [eqn]
  apply integrable_series_transform _ _ _ (χ.LSeriesSummable_twist_vonMangoldt hk).norm
  have hc : Continuous (fun t : ℝ => weight x (line k t)) := continuous_iff_continuousAt.mpr
    (fun t => (weight_analytic hx (s:=line k t) (by simp;linarith)).continuousAt.comp
      (by unfold line;fun_prop))
  apply (integrable_inv_one_add_sq.const_mul (8*x^k)).mono' hc.aestronglyMeasurable
  filter_upwards with t
  simpa only [re_line,im_line,div_eq_mul_inv] using weight_bound hx (s:=line k t) (by simp;linarith)

private theorem edge_point {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)
    {x σ T A : ℝ} (hx : 0<x) (hs : 1/2≤σ) (hA : 0≤A)
    (control : ∀ u : ℂ, edge σ T u → ‖contourLog χ u‖ ≤ A)
    {r t : ℝ} (hu : edge σ T (line r t)) :
    ‖integrand χ x (line r t)‖ ≤ 8*A*x^r/(1+t^2) := by
  have low : 1/2≤(line r t).re := hs.trans hu.1
  have wt := weight_bound hx low
  simp only [re_line,im_line] at wt
  rw [integrand,norm_mul]
  exact (mul_le_mul (control _ hu) wt (norm_nonneg _) hA).trans_eq (by ring)

private theorem vertical_bound {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)
    {x σ T A : ℝ} (hx : 0<x) (hs : 1/2≤σ) (hs2 : σ≤2) (hT : 0<T) (hA : 0≤A)
    (control : ∀ u : ℂ, edge σ T u → ‖contourLog χ u‖ ≤ A) :
    ‖∫ t in (-T)..T, integrand χ x (line σ t)‖ ≤ 8*A*x^σ*Real.pi := by
  let M := 8*A*x^σ
  have bound (t : ℝ) (ht : t ∈ Ioc (-T) T) : ‖integrand χ x (line σ t)‖ ≤ M*(1+t^2)⁻¹ := by
    have onEdge : edge σ T (line σ t) := ⟨by simp,by simpa using hs2,
      by simpa using abs_le.mpr ⟨ht.1.le,ht.2⟩,Or.inl (re_line ..)⟩
    simpa [M,div_eq_mul_inv] using edge_point χ hx hs hA control onEdge
  have integral := intervalIntegral.norm_integral_le_of_norm_le (by linarith : -T≤T)
    (Filter.Eventually.of_forall bound) (integrable_inv_one_add_sq.intervalIntegrable.const_mul M)
  rw [intervalIntegral.integral_const_mul,integral_inv_one_add_sq] at integral
  exact integral.trans (mul_le_mul_of_nonneg_left (by
    linarith only [Real.arctan_lt_pi_div_two T,Real.neg_pi_div_two_lt_arctan (-T)])
    (by dsimp [M];positivity))

private theorem horizontal_bound {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)
    {x σ k T t A : ℝ} (hx : 1≤x) (hs : 1/2≤σ) (hsk : σ≤k) (hk : k≤2)
    (hT : 0<T) (ht : |t|=T) (hA : 0≤A) (control : ∀ u : ℂ, edge σ T u → ‖contourLog χ u‖ ≤ A) :
    ‖∫ u in σ..k, integrand χ x (line u t)‖ ≤ 16*A*x^k/T^2 := by
  have point (u : ℝ) (hu : u ∈ Ι σ k) : ‖integrand χ x (line u t)‖ ≤ 8*A*x^k/T^2 := by
    rw [uIoc_of_le hsk] at hu
    have side : edge σ T (line u t) := ⟨by simpa using hu.1.le,by simpa using hu.2.trans hk,
      by simpa using ht.le,Or.inr (by simpa using ht)⟩
    apply (edge_point χ (zero_lt_one.trans_le hx) hs hA control side).trans
    have sq : t^2=T^2 := by rw [←sq_abs,ht]
    rw [sq]
    exact div_le_div₀ (by positivity) (mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow_of_exponent_le hx hu.2) (by positivity)) (by positivity) (by linarith)
  have int := intervalIntegral.norm_integral_le_of_norm_le_const point
  have len : |k-σ| ≤ 2 := by rw [abs_of_nonneg (sub_nonneg.mpr hsk)];linarith
  exact int.trans ((mul_le_mul_of_nonneg_left len (by positivity : 0≤8*A*x^k/T^2)).trans_eq (by ring))

private theorem tail_bound {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)
    {x η T D : ℝ} (hx : 0<x) (hp : 0<η) (hT : 0<T) (hD : 0≤D)
    (control : ∀ t : ℝ, ‖logDeriv (LFunction χ) (line (1+η) t)‖ ≤ 1/η+D) :
    let k := 1+η
    ‖(∫ t : ℝ, integrand χ x (line k t)) - ∫ t in (-T)..T, integrand χ x (line k t)‖ ≤
      16*(1/η+D)*x^k/T := by
  intro k
  have hk : 1<k := by dsimp [k];linarith
  let M := 8*(1/η+D)*x^k
  have bound (t : ℝ) (ht : T < |t|) : ‖integrand χ x (line k t)‖ ≤ M/t^2 := by
    have sk : 1<(line k t).re := by simpa using hk
    have lg : ‖contourLog χ (line k t)‖ ≤ 1/η+D := by
      rw [contour_right_eq χ sk,LSeries_twistedCoefficient_eq χ sk,norm_neg]
      exact control t
    have wt := weight_bound hx (s:=line k t) (by simp;linarith)
    simp only [re_line,im_line] at wt
    have tp : 0<t^2 := sq_pos_of_ne_zero ((abs_pos.mp (hT.trans ht)))
    rw [integrand,norm_mul]
    calc
      _ ≤ (1/η+D)*(8*x^k/(1+t^2)) := mul_le_mul lg wt (norm_nonneg _) (by positivity)
      _ = M/(1+t^2) := by dsimp [M];ring
      _ ≤ _ := div_le_div_of_nonneg_left (by dsimp [M];positivity) tp (by linarith)
  exact (tails_bound (right_integrable χ hx hk) hT (by dsimp [M];positivity) bound).trans_eq
    (by dsimp [M];ring)

noncomputable def model {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) (x σ b : ℝ) : ℂ :=
  principalFlag χ*weight x 1 - (if active χ σ b then weight x (b:ℂ) else 0)

/-- Shifting the moving right edge still encloses precisely the same zeros,
since no genuine zero lies in the closed half-plane to the right of one. -/
private theorem shift {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) {x σ k T b : ℝ}
    (hx : 0<x) (hs : 1/2≤σ) (hs1 : σ<1) (hk : 1<k) (hk2 : k≤2) (ht : 0<T)
    (inside : ∀ w ∈ boxZeros χ σ 2 (-T) T, σ<w.re ∧ w.re<2 ∧ -T<w.im ∧ w.im<T)
    (residue : ∀ K : ℂ → ℂ, ∑ w ∈ boxZeros χ σ 2 (-T) T,(analyticOrderNatAt (regularizedL χ) w:ℂ)*K w =
      if active χ σ b then K (b:ℂ) else 0) :
    let F := integrand χ x
    (∫ t in (-T)..T, F (line k t)) =
      (∫ t in (-T)..T, F (line σ t)) + 2*(Real.pi:ℂ)*model χ x σ b +
      I*((∫ u in σ..k, F (line u (-T))) - ∫ u in σ..k, F (line u T)) := by
  let S := boxZeros χ σ 2 (-T) T
  let U := Icc σ k ×ℂ Icc (-T) T
  have zero (w : ℂ) (hw : w ∈ U) : regularizedL χ w = 0 ↔ w ∈ S := by
    obtain ⟨r,i⟩ := mem_reProdIm.mp hw
    rw [show S=boxZeros χ σ 2 (-T) T from rfl,mem_boxZeros]
    exact ⟨fun zw => ⟨mem_reProdIm.mpr ⟨⟨r.1,r.2.trans hk2⟩,i⟩,zw⟩,And.right⟩
  have interior (w : ℂ) (hw : w ∈ S) : σ<w.re ∧ w.re<k ∧ -T<w.im ∧ w.im<T := by
    obtain ⟨lo,_,im⟩ := inside w hw
    have zw := ((mem_boxZeros χ σ 2 (-T) T w).mp hw).2
    have above : w.re < 1 := lt_of_not_ge fun e => regular_ne χ w e zw
    exact ⟨lo,above.trans hk,im⟩
  have kw (w : ℂ) (hw : w ∈ U) : AnalyticAt ℂ (weight x) w :=
    weight_analytic hx (lt_of_lt_of_le (by linarith : 0<σ) (mem_reProdIm.mp hw).1.1)
  have rect := rectBoundaryIntegral_neg_logDeriv_add_pole_mul (regularizedL χ) (weight x) S (principalFlag χ)
    hs1 hk (neg_lt_zero.mpr ht) ht ((analytic_regularizedL χ).mono (subset_univ _)) kw zero interior
    (fun w _ => regularizedL_analyticOrder_ne_top χ w) (regularizedL_ne_zero_at_one χ)
  dsimp only [S] at rect
  rw [residue (weight x)] at rect
  exact right_vertical_integral_of_rect rect

theorem finite_estimate :
    ∃ c A D : ℝ, 0<c ∧ c≤1/4 ∧ 0<A ∧ 0≤D ∧ ∀ (Q : ℕ) [NeZero Q] (T : ℝ), 1≤T →
      let L := logHeight Q (T+1)
      let h := c/L
      ∃ σ b : ℝ, 1-h/2≤σ ∧ σ≤1-h/4 ∧
      ∀ (q : ℕ) [NeZero q], q≤Q → ∀ (χ : DirichletCharacter ℂ q) (x η : ℝ),
        1≤x → 0<η → η≤1 →
        ‖rieszSum (twistedCoefficient χ) x - model χ x σ b‖ ≤
        8*(A*L^2)*x^σ*Real.pi + 32*(A*L^2)*x^(1+η)/T^2 + 16*(1/η+D)*x^(1+η)/T := by
  obtain ⟨c,A,hc,c1,hA,box⟩ := common_box
  obtain ⟨D,hD,right⟩ := NearOneZeroMultiplicity.right_edge
  refine ⟨c,A,D,hc,c1,hA,hD,?_⟩
  intro Q _ T hT L h
  obtain ⟨σ,b,left,upper,family⟩ := box Q T hT
  have L1 : 1≤L := logHeight_ge_one Q (T+1)
  have hp : 0<h := div_pos hc (zero_lt_one.trans_le L1)
  have cap : h≤1/4 := (div_le_self hc.le L1).trans c1
  have hs : 1/2≤σ := by change 1-h/2≤σ at left;linarith
  have hs1 : σ<1 := by change σ≤1-h/4 at upper;linarith
  have tp : 0<T := zero_lt_one.trans_le hT
  refine ⟨σ,b,left,upper,?_⟩
  intro q _ leQ χ x η hx ep e1
  obtain ⟨edgeControl,inside,residue⟩ := family q leQ χ
  let B := A*L^2
  let k := 1+η
  let cπ := 1/(2*Real.pi)
  let R := model χ x σ b
  let F := integrand χ x
  let full := ∫ t : ℝ, F (line k t)
  let trunc := ∫ t in (-T)..T, F (line k t)
  let v := ∫ t in (-T)..T, F (line σ t)
  let bottom := ∫ u in σ..k, F (line u (-T))
  let top := ∫ u in σ..k, F (line u T)
  have xp := zero_lt_one.trans_le hx
  have kp : 1<k := by dsimp [k];linarith
  have k2 : k≤2 := by dsimp [k];linarith
  have bp : 0≤B := by dsimp [B];positivity
  have inverse : rieszSum (twistedCoefficient χ) x = cπ • full := right_inverse χ xp kp
  have rect : trunc = v + 2*(Real.pi:ℂ)*R + I*(bottom-top) :=
    shift χ xp hs hs1 kp k2 tp inside residue
  have normV : ‖v‖ ≤ 8*B*x^σ*Real.pi :=
    vertical_bound χ xp hs (by linarith) tp bp edgeControl
  have normH (t : ℝ) (ht : |t|=T) := horizontal_bound χ hx hs (hs1.trans kp).le k2 tp ht bp edgeControl
  have nB : ‖bottom‖ ≤ 16*B*x^k/T^2 := normH (-T) (by simp [abs_of_pos tp])
  have nT : ‖top‖ ≤ 16*B*x^k/T^2 := normH T (abs_of_pos tp)
  have onLine (t : ℝ) : line (1+η) t = (⟨1+η,t⟩:ℂ) := Complex.ext (re_line ..) (im_line ..)
  have nF : ‖full-trunc‖ ≤ 16*(1/η+D)*x^k/T :=
    tail_bound χ xp ep tp hD (fun t => by rw [onLine];exact right q χ η t ep e1)
  have cancel : cπ • (2*(Real.pi:ℂ)*R) = R := by
    rw [Complex.real_smul];dsimp [cπ];push_cast;field_simp [Real.pi_ne_zero]
  have ident : rieszSum (twistedCoefficient χ) x - R = cπ • ((full-trunc)+v+I*(bottom-top)) := by
    have eqv := congrArg (fun z : ℂ => cπ • z) rect
    simp only [smul_add,cancel] at eqv
    rw [inverse]
    simp only [smul_add,smul_sub,eqv]
    abel
  have ps : ‖cπ‖≤1 := by
    rw [Real.norm_eq_abs,abs_of_pos (by dsimp [cπ];positivity)]
    dsimp [cπ]
    apply (div_le_one (by positivity : 0<2*Real.pi)).mpr
    linarith [Real.pi_gt_three]
  have nI : ‖I*(bottom-top)‖ ≤ ‖bottom‖+‖top‖ := by
    rw [norm_mul,norm_I,one_mul]
    exact norm_sub_le ..
  change ‖rieszSum (twistedCoefficient χ) x - R‖ ≤ _
  rw [ident,norm_smul]
  apply (mul_le_of_le_one_left (norm_nonneg _) ps).trans
  have triangle := (norm_add_le ((full-trunc)+v) (I*(bottom-top))).trans
    (add_le_add (norm_add_le (full-trunc) v) nI)
  change _ ≤ 8*B*x^σ*Real.pi + 32*B*x^k/T^2 + 16*(1/η+D)*x^k/T
  exact (triangle.trans (add_le_add (add_le_add nF normV) (add_le_add nB nT))).trans_eq (by ring)

end Conjectures.Goldbach.ExceptionalZeroProgressionsProof.ExceptionalZeroRieszEstimate

namespace Conjectures.Goldbach.ExceptionalZeroProgressionsProof.ExceptionalZeroRieszDecay

open Real DirichletCharacter
open GoldbachSmoothing ExceptionalZeroRieszEstimate
open Conjectures.Goldbach.EstermannAlmostAllPolylog_aux.OAI.LargePrimeGaps (rieszSum)
open scoped Classical

private theorem height_le {u : ℝ} (hu : 8≤u) (Q : ℕ) [NeZero Q] (hQ : (Q:ℝ)≤exp u) :
    logHeight Q (exp u+1) ≤ 3*u := by
  have tp := exp_pos u
  have t1 : 1≤exp u := one_le_exp (by linarith)
  have qp : 0<(Q:ℝ) := by exact_mod_cast NeZero.pos Q
  have first : 2*(Q:ℝ)*(2+|exp u+1|) ≤ 8*(exp u*exp u) := by
    rw [abs_of_pos (by positivity)]
    calc
      _ ≤ 2*exp u*(2+(exp u+1)) := by gcongr
      _ ≤ 2*exp u*(4*exp u) := by gcongr; linarith
      _ = _ := by ring
  apply (Real.log_le_log (by positivity) first).trans
  rw [Real.log_mul (by norm_num) (mul_ne_zero tp.ne' tp.ne'),Real.log_mul tp.ne' tp.ne',Real.log_exp]
  linarith only [hu,Real.log_le_sub_one_of_pos (by norm_num : (0:ℝ)<8)]

private theorem saved_power {x u a σ : ℝ} (hx : 1≤x) (hu : 0<u) (ha : 0≤a)
    (low : u^2≤log x) (hs : σ≤1-2*a/u) : x^σ ≤ x*exp (-(2*a*u)) := by
  have xp := zero_lt_one.trans_le hx
  rw [rpow_def_of_pos xp,←Real.exp_log xp,Real.log_exp,←exp_add,exp_le_exp]
  have mul1 := mul_le_mul_of_nonneg_left hs (log_nonneg hx)
  have mul2 := mul_le_mul_of_nonneg_right low (by positivity : 0≤2*a/u)
  have cancel : u^2*(2*a/u)=2*a*u := by field_simp
  rw [cancel] at mul2
  linarith only [mul1,mul2]

private theorem right_power {x u : ℝ} (hx : 1≤x) (hu : 0<u) (hi : log x≤2*u^2) :
    x^(1+1/u^2) ≤ x*exp 2 := by
  have xp := zero_lt_one.trans_le hx
  rw [rpow_def_of_pos xp,←Real.exp_log xp,Real.log_exp,←exp_add,exp_le_exp]
  have := (div_le_iff₀ (sq_pos_of_pos hu)).mpr hi
  linarith only [show log x*(1+1/u^2) = log x + log x/u^2 by ring,this]

theorem square_exp_bound {a u : ℝ} (ha : 0<a) (hu : 0≤u) :
    u^2*exp (-(2*a*u)) ≤ (2/a^2)*exp (-(a*u)) := by
  have ser := Real.pow_div_factorial_le_exp (a*u) (mul_nonneg ha.le hu) 2
  norm_num at ser
  have bound : u^2 ≤ (2/a^2)*exp (a*u) := by
    have := (le_div_iff₀ (sq_pos_of_pos ha)).mpr (show u^2*a^2 ≤ 2*exp (a*u) by nlinarith only [ser])
    calc
      _ ≤ 2*exp (a*u)/a^2 := this
      _ = _ := by ring
  apply (mul_le_mul_of_nonneg_right bound (exp_pos _).le).trans_eq
  rw [mul_assoc,←exp_add]
  congr 2; ring

theorem uniform_estimate :
    ∃ a C : ℝ, 0<a ∧ a≤1/4 ∧ 0<C ∧ ∀ (u : ℝ), 8≤u →
      ∀ (Q : ℕ) [NeZero Q], (Q:ℝ)≤exp u → ∃ σ b : ℝ, 1/2≤σ ∧ σ≤1-2*a/u ∧
      ∀ (q : ℕ) [NeZero q], q≤Q → ∀ (χ : DirichletCharacter ℂ q) (x : ℝ),
        1≤x → u^2≤log x → log x≤2*u^2 →
        ‖rieszSum (twistedCoefficient χ) x - model χ x σ b‖ ≤ C*x*exp (-(a*u)) := by
  obtain ⟨c,A,D,hc,c1,hA,hD,finite⟩ := finite_estimate
  let a := c/24
  let C₀ := 72*A*Real.pi + 288*A*exp 2 + 16*(1+D)*exp 2
  have ap : 0<a := by dsimp [a];positivity
  have a1 : a≤1/4 := by dsimp [a];linarith
  have C₀p : 0<C₀ := by dsimp [C₀];positivity
  refine ⟨a,C₀*(2/a^2),ap,a1,by positivity,?_⟩
  intro u hu Q _ hQ
  have up : 0<u := by linarith
  have unit : 1≤u^2 := by nlinarith only [hu,sq_nonneg (u-8)]
  let T := exp u
  let L := logHeight Q (T+1)
  have t1 : 1≤T := one_le_exp up.le
  have tp : 0<T := exp_pos _
  have L1 : 1≤L := logHeight_ge_one Q _
  have lp : 0<L := zero_lt_one.trans_le L1
  have Lu : L≤3*u := height_le hu Q hQ
  obtain ⟨σ,b,left,upper,raw⟩ := finite Q T t1
  change 1-(c/L)/2≤σ at left
  change σ≤1-(c/L)/4 at upper
  have σ0 : 1/2≤σ := by linarith only [left,div_le_self hc.le L1,c1]
  have gain : 2*a/u≤(c/L)/4 := by
    have m := div_le_div_of_nonneg_left hc.le lp Lu
    dsimp [a]
    linarith only [show c/(3*u)/4=2*(c/24)/u by ring,m]
  have σ1 : σ≤1-2*a/u := by linarith
  refine ⟨σ,b,σ0,σ1,?_⟩
  intro q _ leQ χ x hx lo hi
  let U := u^2
  let H := exp (-(2*a*u))
  have gap : T⁻¹≤H := by
    change (exp u)⁻¹≤exp _
    rw [←exp_neg,exp_le_exp]
    nlinarith only [mul_le_mul_of_nonneg_right a1 up.le,up]
  have d2 : (T^2)⁻¹≤H := (inv_anti₀ tp (by nlinarith only [t1,sq_nonneg (T-1)] : T≤T^2)).trans gap
  have l2 : L^2≤9*U := by
    calc
      _ ≤ (3*u)^2 := pow_le_pow_left₀ lp.le Lu 2
      _ = _ := by dsimp [U];ring
  have y0 : 0≤x := zero_le_one.trans hx
  have bnd0 : x^σ≤x*H := saved_power hx up ap.le lo σ1
  have bnd1 : x^(1+1/U)≤x*exp 2 := right_power hx up hi
  have den : 1/(1/U)+D≤(1+D)*U := by
    simp only [one_div,inv_inv]
    nlinarith only [mul_le_mul_of_nonneg_left unit hD]
  have hU : 0<U := sq_pos_of_pos up
  have eta : 1/U≤1 := (div_le_one hU).mpr unit
  have raw' := raw q leQ χ x (1/U) hx (by positivity) eta
  have s1 : 8*(A*L^2)*x^σ*Real.pi ≤ 8*(A*(9*U))*(x*H)*Real.pi := by gcongr
  have s2 : 32*(A*L^2)*x^(1+1/U)/T^2 ≤ 32*(A*(9*U))*(x*exp 2)*H := by
    rw [div_eq_mul_inv];gcongr
  have s3 : 16*(1/(1/U)+D)*x^(1+1/U)/T ≤ 16*((1+D)*U)*(x*exp 2)*H := by
    rw [div_eq_mul_inv];gcongr
  apply raw'.trans
  calc
    _ ≤ (8*(A*(9*U))*(x*H)*Real.pi + 32*(A*(9*U))*(x*exp 2)*H + 16*((1+D)*U)*(x*exp 2)*H) :=
      by exact add_le_add (add_le_add s1 s2) s3
    _ = (C₀*x)*(U*H) := by dsimp [C₀];ring
    _ ≤ (C₀*x)*((2/a^2)*exp (-(a*u))) :=
      mul_le_mul_of_nonneg_left (square_exp_bound ap up.le) (mul_nonneg C₀p.le y0)
    _ = _ := by ring

end Conjectures.Goldbach.ExceptionalZeroProgressionsProof.ExceptionalZeroRieszDecay

namespace Conjectures.Goldbach.ExceptionalZeroProgressionsProof.ExceptionalZeroPrimePrefix

open Set Real Complex DirichletCharacter
open GoldbachSmoothing ExceptionalZeroTwistedWindow ExceptionalZeroRieszEstimate
open Conjectures.Goldbach.EstermannAlmostAllPolylog_aux.OAI.LargePrimeGaps
  (weightedPrefix weightedPrefix_eq_mul_rieszSum weightedPrefix_difference weightedPrefix_tail_bound
   primeCoefficients_norm_le characterMain_norm_le)
open scoped Classical

private noncomputable def primitive (b x : ℝ) : ℝ := x^(b+1)/(b*(b+1))
private noncomputable def density (b x : ℝ) : ℝ := x^b/b

private theorem primitive_derivative {x b : ℝ} (hx : 0<x) (hb : 0<b) :
    HasDerivAt (primitive b) (density b x) x := by
  have der := (Real.hasDerivAt_rpow_const (p:=b+1) (Or.inl hx.ne')).div_const (b*(b+1))
  have eqn : density b x = (b+1)*x^(b+1-1)/(b*(b+1)) := by
    rw [density,add_sub_cancel_right]
    field_simp
  rw [eqn]
  exact der

private theorem density_derivative {x b : ℝ} (hx : 0<x) (hb : 0<b) :
    HasDerivAt (density b) (x^(b-1)) x := by
  have der := (Real.hasDerivAt_rpow_const (p:=b) (Or.inl hx.ne')).div_const b
  have eqn : x^(b-1)=b*x^(b-1)/b := by field_simp
  rw [eqn]
  exact der

private theorem primitive_increment {x b h : ℝ} (hx : 1≤x) (hh : 0<h) (hb : 0<b) (hb1 : b≤1) :
    |primitive b (x+h) - primitive b x - h*density b x| ≤ h^2 := by
  have xp := zero_lt_one.trans_le hx
  have dF (t : ℝ) (ht : t ∈ Icc x (x+h)) := primitive_derivative (xp.trans_le ht.1) hb
  obtain ⟨z,hz,slope⟩ := exists_hasDerivAt_eq_slope (primitive b) (density b) (by linarith : x<x+h)
    (fun t ht => (dF t ht).continuousAt.continuousWithinAt)
    (fun t ht => dF t (Ioo_subset_Icc_self ht))
  rw [add_sub_cancel_left] at slope
  have lip := norm_image_sub_le_of_norm_deriv_le_segment' (f:=density b)
    (fun (t : ℝ) (ht : t ∈ Icc x (x+h)) =>
      (density_derivative (xp.trans_le ht.1) hb).hasDerivWithinAt)
    (fun (t : ℝ) (ht : t ∈ Ico x (x+h)) => (show ‖t^(b-1)‖≤(1:ℝ) by
      rw [Real.norm_eq_abs,abs_of_nonneg (Real.rpow_nonneg (xp.trans_le ht.1).le _)]
      exact Real.rpow_le_one_of_one_le_of_nonpos (hx.trans ht.1) (by linarith))) z (Ioo_subset_Icc_self hz)
  have ident : primitive b (x+h)-primitive b x-h*density b x = h*(density b z-density b x) := by
    have s := (eq_div_iff hh.ne').mp slope
    linarith only [s]
  rw [ident,abs_mul,abs_of_pos hh]
  calc
    _ ≤ h*(z-x) := mul_le_mul_of_nonneg_left (by simpa [Real.norm_eq_abs] using lip) hh.le
    _ ≤ h^2 := by nlinarith only [mul_le_mul_of_nonneg_left hz.2.le hh.le]

noncomputable def integrated {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) (x σ b : ℝ) : ℂ :=
  principalFlag χ*(x:ℂ)^2/2 - (if active χ σ b then (primitive b x:ℂ) else 0)

noncomputable def sharp {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) (x σ b : ℝ) : ℂ :=
  principalFlag χ*(x:ℂ) - (if active χ σ b then (density b x:ℂ) else 0)

private theorem integrated_eq {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) {x σ b : ℝ}
    (hx : 0<x) : integrated χ x σ b = (x:ℂ)*model χ x σ b := by
  have one : weight x 1=(x:ℂ)/2 := by unfold weight;norm_num
  unfold integrated model
  rw [one]
  by_cases use : active χ σ b
  · rw [ite_eq_left use,ite_eq_left use]
    have power : (primitive b x:ℂ) = (x:ℂ)*weight x (b:ℂ) := by
      unfold primitive weight
      rw [Real.rpow_add hx,Real.rpow_one]
      push_cast
      rw [Complex.ofReal_cpow hx.le]
      ring
    rw [power];ring
  · rw [ite_eq_right use,ite_eq_right use];ring

private theorem integrated_increment {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)
    {x σ b h : ℝ} (hx : 1≤x) (hs : 1/2≤σ) (hh : 0<h) :
    ‖integrated χ (x+h) σ b - integrated χ x σ b - (h:ℂ)*sharp χ x σ b‖ ≤ 2*h^2 := by
  have nδ : ‖principalFlag χ‖≤1 := characterMain_norm_le χ
  let δ := principalFlag χ
  have principal : ‖δ*(h:ℂ)^2/2‖≤h^2 := by
    rw [norm_div,norm_mul,norm_pow,Complex.norm_real,Real.norm_eq_abs,abs_of_pos hh]
    norm_num
    nlinarith only [mul_le_mul_of_nonneg_right nδ (sq_nonneg h),sq_nonneg h]
  unfold integrated sharp
  by_cases use : active χ σ b
  · simp only [ite_eq_left use]
    have er := primitive_increment hx hh (by linarith only [hs,use.1] : 0<b) use.2.1.le
    let r := primitive b (x+h)-primitive b x-h*density b x
    have iden : principalFlag χ*((x+h:ℝ):ℂ)^2/2 - (primitive b (x+h):ℂ) -
        (principalFlag χ*(x:ℂ)^2/2-(primitive b x:ℂ))-(h:ℂ)*(principalFlag χ*x-(density b x:ℂ)) =
        δ*(h:ℂ)^2/2 - (r:ℂ) := by dsimp [δ,r];push_cast;ring
    rw [iden]
    have small : ‖(r:ℂ)‖≤h^2 := by simpa only [Complex.norm_real,Real.norm_eq_abs] using er
    linarith only [norm_sub_le (δ*(h:ℂ)^2/2) (r:ℂ),principal,small]
  · simp only [ite_eq_right use,sub_zero]
    have iden : principalFlag χ*((x+h:ℝ):ℂ)^2/2 -principalFlag χ*(x:ℂ)^2/2 -(h:ℂ)*(principalFlag χ*x) =
        δ*(h:ℂ)^2/2 := by dsimp [δ];push_cast;ring
    rw [iden]
    linarith only [principal,sq_nonneg h]

/-- Moving the endpoint by h costs the sum of two integrated errors, the
short interval's elementary Mangoldt bound, and the model's curvature. -/
theorem unsmooth {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) {x σ b h : ℝ}
    (hx : 1≤x) (hs : 1/2≤σ) (hh : 0<h) :
    let a := twistedCoefficient χ
    let E := fun y => ‖weightedPrefix a y - integrated χ y σ b‖
    ‖(∑ n ∈ Finset.Ioc 0 ⌊x⌋₊, a n) - sharp χ x σ b‖ ≤
      (E (x+h)+E x)/h + (h+1)*Real.log (x+h)+2*h := by
  intro a E
  let p := ∑ n ∈ Finset.Ioc 0 ⌊x⌋₊, a n
  let F := fun t => weightedPrefix a t - integrated χ t σ b
  let tail := ∑ n ∈ Finset.Ioc ⌊x⌋₊ ⌊x+h⌋₊, ((x+h-(n:ℝ):ℝ):ℂ)*a n
  let curv := integrated χ (x+h) σ b - integrated χ x σ b - (h:ℂ)*sharp χ x σ b
  have xp := zero_lt_one.trans_le hx
  have lp := Real.log_nonneg (show 1≤x+h by linarith)
  have coef (n : ℕ) (hn : n∈Finset.Ioc ⌊x⌋₊ ⌊x+h⌋₊) : ‖a n‖≤Real.log (x+h) := by
    have hn0 : 0<n := lt_of_le_of_lt (Nat.zero_le _) (Finset.mem_Ioc.mp hn).1
    have hn1 := (Nat.le_floor_iff (show 0≤x+h by linarith)).mp (Finset.mem_Ioc.mp hn).2
    exact (primeCoefficients_norm_le χ n).trans (Real.log_le_log (by exact_mod_cast hn0) hn1)
  have tail_le : ‖tail‖ ≤ (h+1)*(h*Real.log (x+h)) := weightedPrefix_tail_bound xp.le hh.le lp a coef
  have inc : weightedPrefix a (x+h)-weightedPrefix a x=(h:ℂ)*p+tail :=
    weightedPrefix_difference hh.le a
  have full : (h:ℂ)*(p-sharp χ x σ b) = ((F (x+h)-F x)-tail)+curv := by
    dsimp [F,curv]
    linear_combination -inc
  have tri := (norm_add_le (F (x+h)-F x-tail) curv).trans
    (add_le_add ((norm_sub_le (F (x+h)-F x) tail).trans
      (add_le_add (norm_sub_le (F (x+h)) (F x)) (le_refl ‖tail‖))) le_rfl)
  rw [←full,norm_mul,Complex.norm_real,Real.norm_eq_abs,abs_of_pos hh] at tri
  change ‖p-sharp χ x σ b‖ ≤ _
  calc
    _ ≤ ((E (x+h)+E x)+((h+1)*Real.log (x+h)+2*h)*h)/h := by
      apply (le_div_iff₀ hh).mpr
      have cv : ‖curv‖≤2*h^2 := integrated_increment χ hx hs hh
      change h*‖p-sharp χ x σ b‖ ≤ E (x+h)+E x+‖tail‖+‖curv‖ at tri
      nlinarith only [tri,tail_le,cv]
    _ = _ := by field_simp;ring

/-- Up to exp(sqrt(log x)) in modulus the ordinary, unsmoothed initial
has an exponentially decaying relative error after its single possible
exceptional term is retained. The correction and the contour are common
to every level in the family at this length. -/
theorem prime_prefix :
    ∃ k C : ℝ, 0<k ∧ 0<C ∧ ∀ (x : ℝ), Real.exp 64≤x →
      let u := Real.sqrt (Real.log x)
      ∀ (Q : ℕ) [NeZero Q], (Q:ℝ)≤Real.exp u → ∃ σ b : ℝ, 1/2≤σ ∧ σ≤1-8*k/u ∧
      ∀ (q : ℕ) [NeZero q], q≤Q → ∀ χ : DirichletCharacter ℂ q,
        ‖(∑ n ∈ Finset.Ioc 0 ⌊x⌋₊, twistedCoefficient χ n) - sharp χ x σ b‖ ≤
        C*x*Real.exp (-(k*u)) := by
  obtain ⟨a,A,ap,ac,Ap,estimate⟩ := ExceptionalZeroRieszDecay.uniform_estimate
  let k := a/4
  have kp : 0<k := by dsimp [k];positivity
  let C := 5*A+8/k^2+2
  refine ⟨k,C,kp,by dsimp [C];positivity,?_⟩
  intro x hx u Q _ hQ
  have x1 : 1≤x := (Real.one_le_exp (by norm_num : (0:ℝ)≤64)).trans hx
  have xp := zero_lt_one.trans_le x1
  have lx : 64≤Real.log x := by simpa using Real.log_le_log (Real.exp_pos _) hx
  have usq : u^2=Real.log x := Real.sq_sqrt (by linarith)
  have up : 0<u := Real.sqrt_pos.mpr (by linarith)
  have u8 : 8≤u := by nlinarith only [usq,lx,up]
  obtain ⟨σ,b,lo,hi,fam⟩ := estimate u u8 Q hQ
  have ku : 8*k=2*a := by dsimp [k];ring
  refine ⟨σ,b,lo,by simpa only [ku] using hi,?_⟩
  intro q _ leQ χ
  let H := Real.exp (-(2*k*u))
  let h := x*H
  have Hp : 0<H := Real.exp_pos _
  have H1 : H≤1 := Real.exp_le_one_iff.mpr (by nlinarith only [mul_nonneg kp.le up.le])
  have hp : 0<h := mul_pos xp Hp
  have h1 : 1≤h := by
    change 1≤x*Real.exp _
    rw [←Real.exp_log xp,←Real.exp_add,Real.one_le_exp_iff]
    have := mul_le_mul_of_nonneg_right ac up.le
    dsimp [k]
    nlinarith only [usq,this,u8,sq_nonneg (u-8)]
  have hle : h≤x := mul_le_of_le_one_right xp.le H1
  have v1 : 1≤x+h := by linarith
  have vlo : u^2≤Real.log (x+h) := usq.le.trans (Real.log_le_log xp (by linarith))
  have vhi : Real.log (x+h)≤2*u^2 := by
    apply (Real.log_le_log (by positivity) (show x+h≤2*x by linarith)).trans
    rw [Real.log_mul (by norm_num) xp.ne']
    linarith only [Real.log_le_sub_one_of_pos (by norm_num : (0:ℝ)<2),usq,lx]
  have decay : Real.exp (-(a*u))=H^2 := by
    change _ = (Real.exp _)^2
    rw [sq,←Real.exp_add]
    congr 1;dsimp [k];ring
  let E := fun y => ‖weightedPrefix (twistedCoefficient χ) y - integrated χ y σ b‖
  have err (y : ℝ) (hy : 1≤y) (yl : u^2≤Real.log y) (yu : Real.log y≤2*u^2) : E y≤A*y^2*H^2 := by
    have yp := zero_lt_one.trans_le hy
    dsimp [E]
    rw [weightedPrefix_eq_mul_rieszSum _ yp,integrated_eq χ yp,←mul_sub,norm_mul,
      Complex.norm_real,Real.norm_eq_abs,abs_of_pos yp]
    have r := fam q leQ χ y hy yl yu
    rw [decay] at r
    exact (mul_le_mul_of_nonneg_left r yp.le).trans_eq (by ring)
  have el := err x x1 usq.le (by rw [←usq];nlinarith only [sq_nonneg u])
  have er := err (x+h) v1 vlo vhi
  have both : (E (x+h)+E x)/h ≤ 5*A*x*H := by
    apply (div_le_iff₀ hp).mpr
    have bound : (x+h)^2≤(2*x)^2 := pow_le_pow_left₀ (by linarith) (by linarith) 2
    have outer : A*(x+h)^2*H^2≤A*(2*x)^2*H^2 := by gcongr
    change _ ≤ 5*A*x*H*(x*H)
    nlinarith only [el,er,outer]
  have short : (h+1)*Real.log (x+h) ≤ (2*h)*(2*u^2) := by
    apply mul_le_mul (by linarith) vhi (Real.log_nonneg v1) (by positivity)
  have raw := unsmooth (b:=b) χ x1 lo hp
  change _ ≤ (E (x+h)+E x)/h+(h+1)*Real.log (x+h)+2*h at raw
  have loss : u^2*H ≤ (2/k^2)*Real.exp (-(k*u)) :=
    ExceptionalZeroRieszDecay.square_exp_bound kp up.le
  have weak : H≤Real.exp (-(k*u)) := Real.exp_le_exp.mpr (by nlinarith only [mul_nonneg kp.le up.le])
  have K0 : 0≤5*A+2 := by positivity
  calc
    _ ≤ 5*A*x*H+(2*h)*(2*u^2)+2*h := raw.trans (add_le_add (add_le_add both short) le_rfl)
    _ = x*((5*A+2)*H+4*(u^2*H)) := by dsimp [h];ring
    _ ≤ x*((5*A+2)*Real.exp (-(k*u))+4*((2/k^2)*Real.exp (-(k*u)))) := by gcongr
    _ = _ := by dsimp [C];ring

end Conjectures.Goldbach.ExceptionalZeroProgressionsProof.ExceptionalZeroPrimePrefix

namespace Conjectures.Goldbach.ExceptionalZeroProgressionsProof.ExceptionalZeroPrimeFamily

open Real Complex DirichletCharacter
open GoldbachSmoothing ExceptionalZeroCatalogue ExceptionalZeroInducedLevels
open ExceptionalZeroTwistedWindow ExceptionalZeroPrimePrefix
open scoped Classical

noncomputable def carriers (q : ℕ) [NeZero q] (s b : ℝ) : Finset (DirichletCharacter ℂ q) :=
  Finset.univ.filter (fun χ => active χ s b)

@[simp] theorem mem_carriers {q : ℕ} [NeZero q] {χ : DirichletCharacter ℂ q} {s b : ℝ} :
    χ ∈ carriers q s b ↔ active χ s b := by simp [carriers]

private theorem induced_ext {q : ℕ} (χ ψ : DirichletCharacter ℂ q)
    (hc : χ.conductor=ψ.conductor) (hχ : HEq χ.primitiveCharacter ψ.primitiveCharacter) : χ=ψ := by
  have lift {r t : ℕ} (d : r∣q) (e : t∣q) (φ : DirichletCharacter ℂ r) (θ : DirichletCharacter ℂ t)
      (same : r=t) (eqn : HEq φ θ) : changeLevel d φ=changeLevel e θ := by
    subst t
    cases eq_of_heq eqn
    rfl
  simpa only [changeLevel_primitiveCharacter] using
    lift χ.conductor_dvd_level ψ.conductor_dvd_level χ.primitiveCharacter ψ.primitiveCharacter hc hχ

/-- The shift of the cutoff from σ up to s loses at most a real-power
term of size 2 x exp(-ku). -/
private theorem cutoff_error {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)
    {x u k σ b : ℝ} (hx : 1≤x) (up : 0<u) (kp : 0<k) (lu : Real.log x=u^2)
    (hs : 1/2≤σ) (hsc : σ≤1-k/u) :
    ‖sharp χ x σ b - sharp χ x (1-k/u) b‖ ≤ 2*x*Real.exp (-(k*u)) := by
  let s := 1-k/u
  have xp := zero_lt_one.trans_le hx
  by_cases old : active χ σ b
  · by_cases new : active χ s b
    · simp only [sharp,show 1-k/u=s from rfl,ite_eq_left old,ite_eq_left new,sub_self,norm_zero]
      positivity
    · have lo : 1/2<b := hs.trans_lt old.1
      have bs : b≤ s := le_of_not_gt (fun h => new ⟨h,old.2⟩)
      have pow : x^b≤x*Real.exp (-(k*u)) := by
        rw [Real.rpow_def_of_pos xp,←Real.exp_log xp,Real.log_exp,←Real.exp_add,Real.exp_le_exp,lu]
        have prod := mul_le_mul_of_nonneg_left bs (sq_nonneg u)
        have iden : u^2*s=u^2-k*u := by dsimp [s];field_simp
        linarith only [prod,iden]
      have dens : |x^b/b| ≤ 2*(x*Real.exp (-(k*u))) := by
        rw [abs_of_nonneg (by positivity)]
        apply (div_le_iff₀ (by linarith : 0<b)).mpr
        nlinarith only [pow,mul_le_mul_of_nonneg_right lo.le (by positivity : 0≤x*Real.exp (-(k*u)))]
      simp only [sharp,show 1-k/u=s from rfl,ite_eq_left old,ite_eq_right new,sub_zero,sub_sub_cancel_left,
        norm_neg,Complex.norm_real,Real.norm_eq_abs]
      exact dens.trans_eq (by ring)
  · have new : ¬active χ s b := fun h => old ⟨hsc.trans_lt h.1,h.2⟩
    simp only [sharp,show 1-k/u=s from rfl,ite_eq_right old,ite_eq_right new,sub_self,norm_zero]
    positivity

private theorem select_conductor {Q : ℕ} [NeZero Q] {s b : ℝ} (hs : 1/2≤ s)
    (family : ∀ (q r : ℕ) [NeZero q] [NeZero r], q≤Q → r≤Q →
      ∀ (χ : DirichletCharacter ℂ q) (ψ : DirichletCharacter ℂ r), active χ s b → active ψ s b →
      χ.IsQuadratic ∧ χ ≠ 1 ∧ χ.conductor=ψ.conductor ∧ HEq χ.primitiveCharacter ψ.primitiveCharacter ∧
      analyticOrderNatAt (LFunction χ) (b:ℂ)=1) :
    ∃ d : ℕ, d≤Q ∧ ∀ (q : ℕ) [NeZero q], q≤Q →
      (carriers q s b).card=(if d∣q then 1 else 0) ∧
      ∀ χ ∈ carriers q s b, χ.IsQuadratic ∧ χ ≠ 1 ∧ χ.conductor=d ∧ analyticOrderNatAt (LFunction χ) (b:ℂ)=1 := by
  classical
  by_cases ex : ∃ r : ℕ, ∃ nz : NeZero r, r≤Q ∧ ∃ ψ : DirichletCharacter ℂ r, @active r nz ψ s b
  · obtain ⟨r,nz,rQ,ψ,hψ⟩ := ex
    let d := ψ.conductor
    haveI : NeZero d := ⟨ψ.conductor_ne_zero⟩
    have pos : 0<(b:ℂ).re := by change 0<b;linarith only [hs,hψ.1]
    have off : (b:ℂ)≠1 := fun eqn => (by have e := congrArg Complex.re eqn;simp at e;linarith only [e,hψ.2.1])
    have back := (lift_zero_order ψ.conductor_dvd_level ψ.primitiveCharacter pos off).1
    rw [changeLevel_primitiveCharacter] at back
    have root := back.mp hψ.2.2
    refine ⟨d,(Nat.le_of_dvd (NeZero.pos r) ψ.conductor_dvd_level).trans rQ,?_⟩
    intro q _ qQ
    have char (χ : DirichletCharacter ℂ q) (hχ : active χ s b) :=
      family q r qQ rQ χ ψ hχ hψ
    refine ⟨?_,fun χ hχ => ?_⟩
    · by_cases dv : d∣q
      · rw [ite_eq_left dv,Finset.card_eq_one_iff_existsUnique]
        let φ := changeLevel dv ψ.primitiveCharacter
        have hφ : active φ s b := ⟨hψ.1,hψ.2.1,(lift_zero_order dv ψ.primitiveCharacter pos off).1.mpr root⟩
        refine ⟨φ,mem_carriers.mpr hφ,?_⟩
        intro χ hχ
        obtain ⟨_,_,levels,chars,_⟩ := family q q qQ qQ χ φ (mem_carriers.mp hχ) hφ
        exact induced_ext χ φ levels chars
      · rw [ite_eq_right dv,Finset.card_eq_zero,Finset.eq_empty_iff_forall_notMem]
        intro χ hχ
        have level : χ.conductor=d := (char χ (mem_carriers.mp hχ)).2.2.1
        exact dv (level ▸ χ.conductor_dvd_level)
    · obtain ⟨quad,non',level,_,order⟩ := char χ (mem_carriers.mp hχ)
      exact ⟨quad,non',level,order⟩
  · refine ⟨0,Nat.zero_le Q,?_⟩
    intro q nz qQ
    have empty : carriers q s b=∅ := Finset.eq_empty_iff_forall_notMem.mpr (fun χ hχ =>
      ex ⟨q,nz,qQ,χ,mem_carriers.mp hχ⟩)
    simp [empty,NeZero.ne q]

theorem uniform_family :
    ∃ k C : ℝ, 0<k ∧ 0<C ∧ ∀ x : ℝ, Real.exp 64≤x →
    let u := Real.sqrt (Real.log x)
    let s := 1-k/u
    ∀ (Q : ℕ) [NeZero Q], (Q:ℝ)≤Real.exp u → ∃ (b : ℝ) (d : ℕ), d≤Q ∧
    ∀ (q : ℕ) [NeZero q], q≤Q →
      (carriers q s b).card=(if d∣q then 1 else 0) ∧
      (∀ χ ∈ carriers q s b, χ.IsQuadratic ∧ χ ≠ 1 ∧ χ.conductor=d ∧ analyticOrderNatAt (LFunction χ) (b:ℂ)=1) ∧
      ∀ χ : DirichletCharacter ℂ q,
        ‖(∑ n ∈ Finset.Ioc 0 ⌊x⌋₊, twistedCoefficient χ n)-sharp χ x s b‖≤C*x*Real.exp (-(k*u)) := by
  obtain ⟨a,A,ap,Ap,estimate⟩ := prime_prefix
  obtain ⟨c,cp,cap,page⟩ := ExceptionalZeroInducedLevels.all_characters
  let k := min a (c/2)
  have kp : 0<k := lt_min ap (by positivity)
  have ka : k≤a := min_le_left ..
  have kc : k≤c/2 := min_le_right ..
  refine ⟨k,A+2,kp,by positivity,?_⟩
  intro x hx u s Q _ hQ
  have x1 := (Real.one_le_exp (by norm_num : (0:ℝ)≤64)).trans hx
  have xp := zero_lt_one.trans_le x1
  have lx : 64≤Real.log x := by simpa using Real.log_le_log (Real.exp_pos _) hx
  have lu : Real.log x=u^2 := (Real.sq_sqrt (by linarith)).symm
  have up : 0<u := Real.sqrt_pos.mpr (by linarith)
  have u8 : 8≤u := by nlinarith only [lu,lx,up]
  have L1 := logHeight_ge_one Q 0
  have lp : 0<logHeight Q 0 := zero_lt_one.trans_le L1
  have qp : 0<(Q:ℝ) := by exact_mod_cast NeZero.pos Q
  have lbound : logHeight Q 0≤2*u := by
    rw [logHeight,abs_zero,add_zero,show 2*(Q:ℝ)*2=4*Q by ring,Real.log_mul (by norm_num) qp.ne']
    have qlog := Real.log_le_log qp hQ
    rw [Real.log_exp] at qlog
    linarith only [qlog,u8,Real.log_le_sub_one_of_pos (by norm_num : (0:ℝ)<4)]
  have cut : k/u≤c/logHeight Q 0 := by
    have bound := div_le_div_of_nonneg_left cp.le lp lbound
    apply (div_le_div_of_nonneg_right kc up.le).trans
    calc
      _ = c/(2*u) := by ring
      _ ≤ _ := bound
  obtain ⟨σ,b,σ0,σ1,f⟩ := estimate x hx Q hQ
  have sc : σ≤ s := by
    change σ≤1-8*a/u at σ1
    dsimp [s]
    linarith only [σ1,div_le_div_of_nonneg_right (by linarith only [ka,ap] : k≤8*a) up.le]
  have region (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q) (hχ : active χ s b) :
      inStrip χ (c/logHeight Q 0) 0 (b:ℂ) := by
    refine ⟨?_,by simp,hχ.2.2⟩
    change 1-c/logHeight Q 0≤b
    have gt := hχ.1
    change 1-k/u<b at gt
    linarith
  obtain ⟨d,dQ,conductor⟩ := select_conductor (Q:=Q) (s:=s) (b:=b) (σ0.trans sc) (by
    intro q r _ _ qQ rQ χ ψ hχ hψ
    obtain ⟨qq,nn,level,char,_,_,order⟩ := page Q q r qQ rQ 0 le_rfl χ ψ (b:ℂ) (b:ℂ) (region _ _ hχ) (region _ _ hψ)
    exact ⟨qq,nn,level,char,order⟩)
  refine ⟨b,d,dQ,?_⟩
  intro q _ qQ
  obtain ⟨count,types⟩ := conductor q qQ
  refine ⟨count,types,?_⟩
  intro χ
  let P := ∑ n ∈ Finset.Ioc 0 ⌊x⌋₊, twistedCoefficient χ n
  have old := f q qQ χ
  have cuterr := cutoff_error (x:=x) (u:=u) (k:=k) (b:=b) χ x1 up kp lu σ0 sc
  have less : Real.exp (-(a*u)) ≤ Real.exp (-(k*u)) :=
    Real.exp_le_exp.mpr (neg_le_neg (mul_le_mul_of_nonneg_right ka up.le))
  calc
    _ = ‖(P-sharp χ x σ b)+(sharp χ x σ b-sharp χ x s b)‖ := by congr 1;abel
    _ ≤ ‖P-sharp χ x σ b‖+‖sharp χ x σ b-sharp χ x s b‖ := norm_add_le ..
    _ ≤ A*x*Real.exp (-(k*u))+2*x*Real.exp (-(k*u)) :=
      by exact add_le_add (old.trans (mul_le_mul_of_nonneg_left less (mul_nonneg Ap.le xp.le))) cuterr
    _ = _ := by ring

end Conjectures.Goldbach.ExceptionalZeroProgressionsProof.ExceptionalZeroPrimeFamily

namespace Conjectures.Goldbach.ExceptionalZeroProgressionsProof.ExceptionalZeroProgressions

open Set Real Complex DirichletCharacter
open GoldbachSmoothing ExceptionalZeroTwistedWindow ExceptionalZeroPrimeFamily
open ExceptionalZeroPrimePrefix
open Conjectures.Goldbach.EstermannAlmostAllPolylog_aux.OAI.LargePrimeGaps
  (primeCharacterPrefix primeCharacterError residuePrefix character_error_orthogonality)
open scoped Classical

noncomputable def amplitude (q : ℕ) [NeZero q] (a : ℕ) (s b : ℝ) : ℂ :=
  ∑ χ ∈ carriers q s b, χ (a:ZMod q)⁻¹

private theorem character_card (q : ℕ) [NeZero q] :
    Fintype.card (DirichletCharacter ℂ q)=q.totient := by
  simpa only [Nat.card_eq_fintype_card] using DirichletCharacter.card_eq_totient_of_hasEnoughRootsOfUnity ℂ q

private theorem sign {q a d : ℕ} [NeZero q] {s b : ℝ} (cop : a.Coprime q)
    (count : (carriers q s b).card=(if d∣q then 1 else 0))
    (quad : ∀ χ ∈ carriers q s b, χ.IsQuadratic) :
    (if d∣q then amplitude q a s b=1 ∨ amplitude q a s b= -1 else amplitude q a s b=0) := by
  by_cases dv : d∣q
  · rw [ite_eq_left dv] at count ⊢
    obtain ⟨χ,only⟩ := Finset.card_eq_one.mp count
    have mem : χ∈carriers q s b := by simp [only]
    have unit : IsUnit (a:ZMod q)⁻¹ := by
      obtain ⟨z,hz⟩ := (ZMod.isUnit_iff_coprime a q).mpr cop
      rw [←hz,ZMod.inv_coe_unit]
      exact (z⁻¹).isUnit
    have nonzero := (unit.map χ.toMonoidHom).ne_zero
    rw [amplitude,only,Finset.sum_singleton]
    exact (quad χ mem _).resolve_left nonzero
  · rw [ite_eq_right dv] at count ⊢
    simp [amplitude,Finset.card_eq_zero.mp count]

private theorem average {q : ℕ} [NeZero q] {a : ℕ} (ha : a<q) (cop : a.Coprime q)
    (x s b M : ℝ)
    (all : ∀ χ : DirichletCharacter ℂ q,
      ‖primeCharacterPrefix x χ - sharp χ x s b‖ ≤ M) :
    ‖(residuePrefix ArithmeticFunction.vonMangoldt ⌊x⌋₊ q a:ℂ) -
      ((x:ℂ) - amplitude q a s b*((x^b/b:ℝ):ℂ))/(q.totient:ℂ)‖ ≤ M := by
  classical
  let P : ℂ := (residuePrefix ArithmeticFunction.vonMangoldt ⌊x⌋₊ q a:ℝ)
  let t : ℂ := q.totient
  let g : ℂ := (x^b/b:ℝ)
  let w := fun (χ : DirichletCharacter ℂ q) => χ (a:ZMod q)⁻¹
  let E := fun χ : DirichletCharacter ℂ q => primeCharacterPrefix x χ - sharp χ x s b
  have tn : t≠0 := by dsimp [t];exact_mod_cast (Nat.totient_pos.mpr (NeZero.pos q)).ne'
  have normsum : ‖∑ χ, w χ*E χ‖ ≤ (q.totient:ℝ)*M := by
    apply (norm_sum_le ..).trans
    calc
      _ ≤ ∑ _χ : DirichletCharacter ℂ q, M := by
        apply Finset.sum_le_sum
        intro χ _
        rw [norm_mul]
        exact (mul_le_of_le_one_left (norm_nonneg _) (χ.norm_le_one _)).trans (all χ)
      _ = _ := by simp [character_card]
  have base := character_error_orthogonality x (NeZero.pos q) ha cop
  change (∑ χ, w χ*primeCharacterError x χ)=_ at base
  have identity (χ : DirichletCharacter ℂ q) :
      E χ = primeCharacterError x χ + (if active χ s b then g else 0) := by
    unfold E sharp primeCharacterError principalFlag
    by_cases h : χ=1
    · simp only [ite_eq_left h,one_mul]
      abel
    · simp only [ite_eq_right h,zero_mul,sub_zero]
      abel
  have correction : (∑ χ, w χ*(if active χ s b then g else 0))=amplitude q a s b*g := by
    rw [amplitude,Finset.sum_mul,carriers,Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro χ _
    by_cases hit : active χ s b <;> simp [hit,w]
  have iden : (∑ χ, w χ*E χ)=t*(P-((x:ℂ)-amplitude q a s b*g)/t) := by
    simp_rw [identity,mul_add]
    rw [Finset.sum_add_distrib,base,correction]
    change t*((residuePrefix ArithmeticFunction.vonMangoldt ⌊x⌋₊ q a-x/q.totient:ℝ):ℂ)+_ = _
    push_cast
    dsimp only [P,t,g] at *
    field_simp
    ring
  rw [iden,norm_mul] at normsum
  have tp : (0:ℝ)<q.totient := by exact_mod_cast Nat.totient_pos.mpr (NeZero.pos q)
  change ‖(q.totient:ℂ)‖*_≤_ at normsum
  rw [Complex.norm_natCast] at normsum
  exact (le_of_mul_le_mul_left normsum tp)

theorem progressions :
    ∃ k C : ℝ, 0<k ∧ 0<C ∧ ∀ x : ℝ, Real.exp 64≤x →
    let u := Real.sqrt (Real.log x)
    let s := 1-k/u
    ∀ (Q : ℕ) [NeZero Q], (Q:ℝ)≤Real.exp u → ∃ (b : ℝ) (d : ℕ), d≤Q ∧
    ∀ (q : ℕ) [NeZero q], q≤Q →
      (carriers q s b).card=(if d∣q then 1 else 0) ∧
      (∀ χ ∈ carriers q s b, χ.IsQuadratic ∧ χ ≠ 1 ∧ χ.conductor=d ∧ analyticOrderNatAt (LFunction χ) (b:ℂ)=1) ∧
      ∀ (a : ℕ), a<q → a.Coprime q →
      let ε := (amplitude q a s b).re
      let R := |residuePrefix ArithmeticFunction.vonMangoldt ⌊x⌋₊ q a-(x-ε*(x^b/b))/q.totient|
      (if d∣q then ε=1 ∨ ε= -1 else ε=0) ∧ R≤C*x*Real.exp (-(k*u)) ∧
      ((q:ℝ)≤Real.exp (k*u/2) → R≤C*(x/q.totient)*Real.exp (-(k*u/2))) := by
  obtain ⟨k,C,kp,Cp,raw⟩ := uniform_family
  refine ⟨k,C,kp,Cp,?_⟩
  intro x hx u s Q _ hQ
  obtain ⟨b,d,dQ,family⟩ := raw x hx Q hQ
  refine ⟨b,d,dQ,?_⟩
  intro q _ qQ
  obtain ⟨count,types,error⟩ := family q qQ
  refine ⟨count,types,?_⟩
  intro a ha cop ε R
  have signs := sign cop (s:=s) (b:=b) count (fun χ hχ => (types χ hχ).1)
  have realpart : (if d∣q then ε=1 ∨ ε= -1 else ε=0) ∧ ((ε:ℂ)=amplitude q a s b) := by
    dsimp only [ε]
    by_cases dv : d∣q
    · rw [ite_eq_left dv] at signs ⊢
      rcases signs with plus | minus
      · simp [plus]
      · simp [minus]
    · rw [ite_eq_right dv] at signs ⊢
      simp [signs]
  have xp := (Real.exp_pos _).trans_le hx
  let M := C*x*Real.exp (-(k*u))
  have bound := average ha cop x s b M (fun χ => error χ)
  rw [←realpart.2] at bound
  have exactR : R≤M := by
    change |residuePrefix ArithmeticFunction.vonMangoldt ⌊x⌋₊ q a-(x-ε*(x^b/b))/q.totient|≤M
    rw [←Real.norm_eq_abs,←Complex.norm_real]
    push_cast
    simpa only [Complex.ofReal_div] using bound
  refine ⟨realpart.1,exactR,?_⟩
  intro qrange
  apply exactR.trans
  have tp : (0:ℝ)<q.totient := by exact_mod_cast Nat.totient_pos.mpr (NeZero.pos q)
  have tot : (q.totient:ℝ)≤Real.exp (k*u/2) :=
    (show (q.totient:ℝ)≤q by exact_mod_cast Nat.totient_le q).trans qrange
  have exp : (q.totient:ℝ)*Real.exp (-(k*u))≤Real.exp (-(k*u/2)) := by
    apply (mul_le_mul_of_nonneg_right tot (Real.exp_pos _).le).trans_eq
    rw [←Real.exp_add];congr 1;ring
  calc
    M = (C*(x/q.totient))*((q.totient:ℝ)*Real.exp (-(k*u))) := by dsimp [M];field_simp
    _ ≤ _ := mul_le_mul_of_nonneg_left exp (by positivity)

end Conjectures.Goldbach.ExceptionalZeroProgressionsProof.ExceptionalZeroProgressions

set_option maxHeartbeats 1800000 in
theorem Conjectures.Goldbach.ExceptionalZeroProgressions :
by
  classical
  let hit := fun {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) (s b : ℝ) =>
    s<b ∧ b<1 ∧ (χ ≠ 1 ∨ (b:ℂ) ≠ 1) ∧ DirichletCharacter.LFunction χ (b:ℂ)=0
  exact ∃ k C : ℝ, 0<k ∧ 0<C ∧ ∀ x : ℝ, Real.exp 64≤x →
    let u := Real.sqrt (Real.log x)
    let s := 1-k/u
    ∀ (Q : ℕ) [NeZero Q], (Q:ℝ)≤Real.exp u → ∃ (b : ℝ) (d : ℕ), d≤Q ∧
    ∀ (q : ℕ) [NeZero q], q≤Q →
      let S := @Finset.filter (DirichletCharacter ℂ q) (fun χ => hit χ s b)
        (fun _ => Classical.propDecidable _) Finset.univ
      S.card=(if d∣q then 1 else 0) ∧
      (∀ χ ∈ S, χ.IsQuadratic ∧ χ ≠ 1 ∧ χ.conductor=d ∧
        analyticOrderNatAt (DirichletCharacter.LFunction χ) (b:ℂ)=1) ∧
      ∀ a : ℕ, a<q → a.Coprime q →
        let ε := (∑ χ ∈ S, χ (a:ZMod q)⁻¹).re
        let ψ := ∑ n ∈ (Finset.Ioc 0 ⌊x⌋₊).filter (fun n => n % q=a), ArithmeticFunction.vonMangoldt n
        let R := |ψ-(x-ε*(x^b/b))/q.totient|
        (if d∣q then ε=1 ∨ ε= -1 else ε=0) ∧ R≤C*x*Real.exp (-(k*u)) ∧
        ((q:ℝ)≤Real.exp (k*u/2) → R≤C*(x/q.totient)*Real.exp (-(k*u/2))) :=
by
  with_unfolding_all exact Conjectures.Goldbach.ExceptionalZeroProgressionsProof.ExceptionalZeroProgressions.progressions
