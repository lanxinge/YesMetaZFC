import YesMetaZFC.SetTheory.Descriptive.LeastLegalMove
import YesMetaZFC.SetTheory.Descriptive.InputIteration

/-! # 最小编号驱动的三步响应表

先落下枚举中的最小合法请求，再读取 I 的回答，最后按原时序读取 I 的实数
走法或对手输入。所有历史都返回同一有限历史空间中的实际后继。
-/
namespace YesMetaZFC.SetTheory.Descriptive
open Definitional.Project InnerModel Internal
universe u
variable {M : Structure.{u}} (hZF : M.Models ZF)
local notation "I" => kp_pair_l (ZF.modelsKP hZF)

def Cg_scan_step_d (ω X F J σ g K h x t : M.Domain) : Prop := ∃ i a h₁ w h₂ n y,
  Rd_entry_d h i K ∧ Rd_entry_d i a g ∧ M.mem h₁ F ∧ Fseq_end_d I ω h₁ h a ∧
  Rd_entry_d h₁ w σ ∧ M.mem h₂ F ∧ Fseq_end_d I ω h₂ h₁ w ∧ Fn0_d n X h₂ ∧
  ((M.mem n J ∧ Rd_entry_d h₂ y σ) ∨ (¬ M.mem n J ∧ y = x)) ∧ M.mem t F ∧ Fseq_end_d I ω t h₂ y

def cg_scan_step_m {d} (ω X F J σ g K h x t : Term d) : Formula 1 d := set[d] ⟪∃ i a h₁ w h₂ n y,
  ⌜rd_entry0_m⌝ₚ(⌜h⌝ₛ, i, ⌜K⌝ₛ) ∧ ⌜rd_entry0_m⌝ₚ(i, a, ⌜g⌝ₛ) ∧ h₁ ∈ ⌜F⌝ₛ ∧
  ⌜fseq_end_m (𝒞 := kpair_convention_l)⌝ₚ(⌜ω⌝ₛ, h₁, ⌜h⌝ₛ, a) ∧
  ⌜rd_entry0_m⌝ₚ(h₁, w, ⌜σ⌝ₛ) ∧ h₂ ∈ ⌜F⌝ₛ ∧ ⌜fseq_end_m (𝒞 := kpair_convention_l)⌝ₚ(⌜ω⌝ₛ, h₂, h₁, w) ∧
  ⌜fn0_m⌝ₚ(n, ⌜X⌝ₛ, h₂) ∧ ((n ∈ ⌜J⌝ₛ ∧ ⌜rd_entry0_m⌝ₚ(h₂, y, ⌜σ⌝ₛ)) ∨ (¬ n ∈ ⌜J⌝ₛ ∧ y = ⌜x⌝ₛ)) ∧
  ⌜t⌝ₛ ∈ ⌜F⌝ₛ ∧ ⌜fseq_end_m (𝒞 := kpair_convention_l)⌝ₚ(⌜ω⌝ₛ, ⌜t⌝ₛ, h₂, y)⟫
derive_free_closed cg_scan_step_m

theorem cg_scan_step_sat_l {d} (ρ : Env M d) (ω X F J σ g K h x t : Term d) :
    Formula.satisfies ρ (cg_scan_step_m ω X F J σ g K h x t) ↔ Cg_scan_step_d hZF
      (ω.eval ρ) (X.eval ρ) (F.eval ρ) (J.eval ρ) (σ.eval ρ) (g.eval ρ) (K.eval ρ) (h.eval ρ) (x.eval ρ) (t.eval ρ) := by
  simp only [cg_scan_step_m, Cg_scan_step_d, Formula.satisfies_exists_iff, Formula.satisfies_conj_iff,
    rd_entry0_sat_l hZF.1, Formula.satisfies_mem_iff, fseq_end_sat_l I hZF.1, fn0_sat_l hZF.1,
    Formula.satisfies_disj_iff, Formula.satisfies_neg_iff, Formula.satisfies_extensionalEq_iff_eq hZF.1,
    Definitional.Term.eval_weaken]; rfl

theorem Cg_scan_step_d.unique_l {ω X F J σ g K h x t u : M.Domain}
    (fk : M.IsSetFunction I K) (fg : M.IsSetFunction I g) (fs : M.IsSetFunction I σ)
    (left : Cg_scan_step_d hZF ω X F J σ g K h x t) (right : Cg_scan_step_d hZF ω X F J σ g K h x u) : t = u := by
  obtain ⟨i, a, h₁, w, h₂, n, y, ki, ga, _, e₁, sw, _, e₂, fn, own, _, et⟩ := left
  obtain ⟨i', a', h₁', w', h₂', n', y', ki', ga', _, e₁', sw', _, e₂', fn', own', _, eu⟩ := right
  have eq := fk.2 h i' i ki' ki; subst i'
  have eq := fg.2 i a' a ga' ga; subst a'
  have eq := fseq_end_rebuild_l I hZF.1 e₁' e₁; subst h₁'
  have eq := fs.2 h₁ w' w sw' sw; subst w'
  have eq := fseq_end_rebuild_l I hZF.1 e₂' e₂; subst h₂'
  have eq := fn'.domain_eq_l hZF.1 fn; subst n'
  have eq : y = y' := by
    rcases own with ⟨hi, hy⟩ | ⟨hi, hy⟩ <;> rcases own' with ⟨hi', hy'⟩ | ⟨hi', hy'⟩
    · exact fs.2 h₂ y y' hy hy'
    · exact (hi' hi).elim
    · exact (hi hi').elim
    · exact hy.trans hy'.symm
  exact fseq_end_rebuild_l I hZF.1 et (eq.symm ▸ eu)

theorem cg_scan_step_exists_l {ω X F J σ g K h x : M.Domain} (hw : M.IsOmega ω)
    (space : Fseq_space_d I ω X F) (fk : Fn0_d F ω K) (fg : Fn0_d ω X g) (fs : Fn0_d F X σ)
    (hh : M.mem h F) (hx : M.mem x X) : ∃ t, Cg_scan_step_d hZF ω X F J σ g K h x t := by
  classical
  obtain ⟨i, hi, ki⟩ := fk.2.1 h hh
  obtain ⟨a, ha, ga⟩ := fg.2.1 i hi
  obtain ⟨n₀, hn₀, fh⟩ := (space h).mp hh
  obtain ⟨n₁, h₁, hn₁, fh₁, e₁⟩ := ZF.fseq_end_exists_l I hZF hw hn₀ fh ha
  have hh₁ := (space h₁).mpr ⟨n₁, hn₁, fh₁⟩
  obtain ⟨w, hwX, sw⟩ := fs.2.1 h₁ hh₁
  obtain ⟨n₂, h₂, hn₂, fh₂, e₂⟩ := ZF.fseq_end_exists_l I hZF hw hn₁ fh₁ hwX
  have hh₂ := (space h₂).mpr ⟨n₂, hn₂, fh₂⟩
  have output : ∃ y, M.mem y X ∧ ((M.mem n₂ J ∧ Rd_entry_d h₂ y σ) ∨ (¬ M.mem n₂ J ∧ y = x)) := by
    by_cases hi : M.mem n₂ J
    · obtain ⟨y, hy, sy⟩ := fs.2.1 h₂ hh₂
      exact ⟨y, hy, Or.inl ⟨hi, sy⟩⟩
    · exact ⟨x, hx, Or.inr ⟨hi, rfl⟩⟩
  obtain ⟨y, hy, own⟩ := output
  obtain ⟨m, t, hm, ft, et⟩ := ZF.fseq_end_exists_l I hZF hw hn₂ fh₂ hy
  exact ⟨t, i, a, h₁, w, h₂, n₂, y, ki, ga, hh₁, e₁, sw, hh₂, e₂,
    fn0_of_function_l (ZF.modelsKP hZF) fh₂, own, (space t).mpr ⟨m, hm, ft⟩, et⟩

structure Cg_scanner_d (ω A X F L J σ g K D T : M.Domain) : Prop where
  space : Fseq_space_d I ω X F
  enumeration : Fn0_d ω X g
  strategy : Fn0_d F X σ
  input : M.MemberSubset A X
  indices : Fn0_d F ω K
  product : M.IsCartesianProduct I D F A
  response : Fn0_d D F T
  least : ∀ h i, Rd_entry_d h i K →
    (∃ j a, M.mem j ω ∧ Rd_entry_d j a g ∧ Cg_admit_d hZF ω L h a) → Cg_scan_d hZF ω L g h i
  step : ∀ h x p t, (I).Codes p h x → Rd_entry_d p t T → Cg_scan_step_d hZF ω X F J σ g K h x t

/-- 一次构造最小编号表与实际三步响应函数，后续对局递归不再选择。 -/
theorem cg_scan_table_l {ω e A X F L J σ g : M.Domain} (hw : M.IsOmega ω) (he : ∀ x, ¬ M.mem x e)
    (space : Fseq_space_d I ω X F) (fg : Fn0_d ω X g) (fs : Fn0_d F X σ) (sub : M.MemberSubset A X) :
    ∃ K D T, Cg_scanner_d hZF ω A X F L J σ g K D T := by
  obtain ⟨K, fk, least⟩ := cg_selector_l hZF (F := F) (L := L) (g := g) hw he
  obtain ⟨D, prod⟩ := ZF.exists_cartesianProduct hZF I F A
  let ρ : Env M 7 := ⟨fun i => [ω, X, F, J, σ, g, K].get i, fun _ => ω⟩
  let φ : BinarySchema 7 := { body := set[9] ⟪∃ h x, ⌜kpair0_m⌝ₚ(⌜(.bound 1 : Term 9)⌝ₛ, h, x) ∧
    ⌜cg_scan_step_m⌝ₚ(⌜(.bound 2 : Term 9)⌝ₛ, ⌜(.bound 3 : Term 9)⌝ₛ, ⌜(.bound 4 : Term 9)⌝ₛ,
      ⌜(.bound 5 : Term 9)⌝ₛ, ⌜(.bound 6 : Term 9)⌝ₛ, ⌜(.bound 7 : Term 9)⌝ₛ, ⌜(.bound 8 : Term 9)⌝ₛ,
      h, x, ⌜(.newest : Term 9)⌝ₛ)⟫ }
  have sat p t : φ.denote ρ p t ↔ ∃ h x, (I).Codes p h x ∧ Cg_scan_step_d hZF ω X F J σ g K h x t := by
    simp only [φ, BinarySchema.denote, Formula.satisfies_exists_iff, Formula.satisfies_conj_iff,
      kpair0_sat_l hZF.1, cg_scan_step_sat_l hZF, Definitional.Term.eval_weaken]; rfl
  obtain ⟨T, fn, graph⟩ := ZF.exists_setFunctionFromTo_of_denote hZF I φ ρ (source := D) (target := F) (by
    intro p hp
    obtain ⟨h, hh, x, hx, pair⟩ := (prod p).mp hp
    obtain ⟨t, step⟩ := cg_scan_step_exists_l hZF hw space fk fg fs hh (sub x hx)
    exact ⟨t, (sat p t).mpr ⟨h, x, pair, step⟩⟩) (by
    intro p _ t u ht hu
    obtain ⟨h, x, pair, step⟩ := (sat p t).mp ht
    obtain ⟨h', x', pair', step'⟩ := (sat p u).mp hu
    obtain ⟨rfl, rfl⟩ := (I).injective pair pair'
    exact step.unique_l hZF (fn0_function_l (ZF.modelsKP hZF) fk).1
      (fn0_function_l (ZF.modelsKP hZF) fg).1 (fn0_function_l (ZF.modelsKP hZF) fs).1 step') (by
    intro p t _ ht
    obtain ⟨_, _, _, step⟩ := (sat p t).mp ht
    obtain ⟨i, a, h₁, w, h₂, n, y, _, _, _, _, _, _, _, _, _, mem, _⟩ := step
    exact mem)
  refine ⟨K, D, T, space, fg, fs, sub, fk, prod, fn0_of_function_l (ZF.modelsKP hZF) fn, least, fun h x p t pair pt => ?_⟩
  obtain ⟨h', x', pair', step⟩ := (sat p t).mp ((graph p t).mp pt).2
  obtain ⟨rfl, rfl⟩ := (I).injective pair pair'
  exact step

end YesMetaZFC.SetTheory.Descriptive
