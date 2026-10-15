import YesMetaZFC.SetTheory.Descriptive.ScanResponse
import YesMetaZFC.SetTheory.Descriptive.Path
import YesMetaZFC.SetTheory.RelationChain

/-! # 最小请求递归产生原有限历史策略

有限输入只在对手的奇数轮被读取。由确定响应表递归到当前轮，再读取第三步；
不属于原字母表的虚拟历史取固定默认字母，合法历史中的实际输出不受此约定影响。
-/
namespace YesMetaZFC.SetTheory.Descriptive
open Definitional.Project InnerModel Internal
universe u
variable {M : Structure.{u}} (hZF : M.Models ZF)
local notation "I" => kp_pair_l (ZF.modelsKP hZF)

def Cg_scan_answer_d (ω A F T e a s y : M.Domain) : Prop := ∃ n H h p t z v,
  M.IsDomainOf I n s ∧ Gi_d hZF false ω F T e a s H ∧ Rd_entry_d n h H ∧
  (I).Codes p h a ∧ Rd_entry_d p t T ∧ Fseq_end_d I ω t z v ∧
  ((M.mem v A ∧ y = v) ∨ (¬ M.mem v A ∧ y = a))

def cg_scan_answer_m {d} (ω A F T e a s y : Term d) : Formula 1 d := set[d] ⟪∃ n H h p t z v,
  ⌜Formula.isDomain kpair_convention_l⌝ₚ(n, ⌜s⌝ₛ) ∧
  ⌜(gi_m false)⌝ₚ(⌜ω⌝ₛ, ⌜F⌝ₛ, ⌜T⌝ₛ, ⌜e⌝ₛ, ⌜a⌝ₛ, ⌜s⌝ₛ, H) ∧
  ⌜rd_entry0_m⌝ₚ(n, h, H) ∧ ⌜kpair0_m⌝ₚ(p, h, ⌜a⌝ₛ) ∧ ⌜rd_entry0_m⌝ₚ(p, t, ⌜T⌝ₛ) ∧
  ⌜fseq_end_m (𝒞 := kpair_convention_l)⌝ₚ(⌜ω⌝ₛ, t, z, v) ∧
  ((v ∈ ⌜A⌝ₛ ∧ ⌜y⌝ₛ = v) ∨ (¬ v ∈ ⌜A⌝ₛ ∧ ⌜y⌝ₛ = ⌜a⌝ₛ))⟫
derive_free_closed cg_scan_answer_m

theorem cg_scan_answer_sat_l {d} (ρ : Env M d) (ω A F T e a s y : Term d) :
    Formula.satisfies ρ (cg_scan_answer_m ω A F T e a s y) ↔ Cg_scan_answer_d hZF
      (ω.eval ρ) (A.eval ρ) (F.eval ρ) (T.eval ρ) (e.eval ρ) (a.eval ρ) (s.eval ρ) (y.eval ρ) := by
  simp only [cg_scan_answer_m, Cg_scan_answer_d, Formula.satisfies_exists_iff, Formula.satisfies_conj_iff,
    Formula.satisfies_isDomain_iff I, gi_sat_l hZF false, rd_entry0_sat_l hZF.1, kpair0_sat_l hZF.1,
    fseq_end_sat_l I hZF.1, Formula.satisfies_disj_iff, Formula.satisfies_mem_iff, Formula.satisfies_neg_iff,
    Formula.satisfies_extensionalEq_iff_eq hZF.1, Definitional.Term.eval_weaken]; rfl

theorem Cg_scanner_d.answer_l {ω A X F L J σ g K D T e a s n : M.Domain}
    (c : Cg_scanner_d hZF ω A X F L J σ g K D T) (hw : M.IsOmega ω) (he : ∀ x, ¬ M.mem x e)
    (ha : M.mem a A) (hn : M.mem n ω) (fs : M.IsSetFunctionFromTo I s n A) :
    ∃ y, Cg_scan_answer_d hZF ω A F T e a s y := by
  classical
  have heF := (c.space e).mpr ⟨e, num_mem_l hZF.1 hw (show Num_d 0 e from he), ds_empty_fun_l I he⟩
  obtain ⟨H, run⟩ := gi_exists_l hZF (b := false) hw c.product c.response heF ha fs.1 (fun _ _ h => fs.output_mem_of_pairMember h)
  obtain ⟨h, hh, nh⟩ := run.1.2.1 n hn
  obtain ⟨p, pair⟩ := (I).total h a
  obtain ⟨t, _, pt⟩ := c.response.2.1 p ((c.product p).mpr ⟨h, hh, a, ha, pair⟩)
  obtain ⟨i, b, h₁, w, h₂, m, v, _, _, _, _, _, _, _, _, _, _, endt⟩ := c.step h a p t pair pt
  by_cases hv : M.mem v A
  · exact ⟨v, n, H, h, p, t, h₂, v, fs.2.1, run, nh, pair, pt, endt, Or.inl ⟨hv, rfl⟩⟩
  · exact ⟨a, n, H, h, p, t, h₂, v, fs.2.1, run, nh, pair, pt, endt, Or.inr ⟨hv, rfl⟩⟩

theorem cg_scan_answer_unique_l {ω A F T e a s x y : M.Domain} (hw : M.IsOmega ω)
    (ft : M.IsSetFunction I T) (fs : M.IsSetFunction I s)
    (hx : Cg_scan_answer_d hZF ω A F T e a s x) (hy : Cg_scan_answer_d hZF ω A F T e a s y) : x = y := by
  obtain ⟨n, H, h, p, t, z, v, dom, run, nh, pair, pt, endt, output⟩ := hx
  obtain ⟨n', H', h', p', t', z', v', dom', run', nh', pair', pt', endt', output'⟩ := hy
  have eq := dom'.eq hZF.1 dom; subst n'
  have eq := run.agree_l hZF hw ft fs run' (run.1.bound_l nh).1 (fun _ _ _ => Iff.rfl) h h' nh nh'
  subst h'
  have eq := (I).unique pair' pair; subst p'
  have eq := ft.2 p t' t pt' pt; subst t'
  have eq := (fseq_end_unique_l I hZF.1 endt' endt).2; subst v'
  rcases output with ⟨hv, eq⟩ | ⟨hv, eq⟩ <;> rcases output' with ⟨hv', eq'⟩ | ⟨hv', eq'⟩
  · exact eq.trans eq'.symm
  · exact (hv' hv).elim
  · exact (hv hv').elim
  · exact eq.trans eq'.symm

theorem Cg_scanner_d.strategy_l {ω A X F L J σ g K D T e a S : M.Domain}
    (c : Cg_scanner_d hZF ω A X F L J σ g K D T) (hw : M.IsOmega ω) (he : ∀ x, ¬ M.mem x e)
    (ha : M.mem a A) (space : Fseq_space_d I ω A S) : ∃ τ, Fn0_d S A τ ∧
      ∀ s y, Rd_entry_d s y τ ↔ M.mem s S ∧ Cg_scan_answer_d hZF ω A F T e a s y := by
  let ρ : Env M 6 := ⟨fun i => [ω, A, F, T, e, a].get i, fun _ => ω⟩
  let φ : BinarySchema 6 := { body := cg_scan_answer_m (.bound 2) (.bound 3) (.bound 4) (.bound 5) (.bound 6) (.bound 7) (.bound 1) .newest }
  have sat s y : φ.denote ρ s y ↔ Cg_scan_answer_d hZF ω A F T e a s y := cg_scan_answer_sat_l hZF ..
  obtain ⟨τ, fn, graph⟩ := ZF.exists_setFunctionFromTo_of_denote hZF I φ ρ (source := S) (target := A) (by
    intro s hs
    obtain ⟨n, hn, fs⟩ := (space s).mp hs
    obtain ⟨y, hy⟩ := c.answer_l hZF hw he ha hn fs
    exact ⟨y, (sat s y).mpr hy⟩) (by
    intro s hs x y hx hy
    obtain ⟨_, _, fs⟩ := (space s).mp hs
    exact cg_scan_answer_unique_l hZF hw (fn0_function_l (ZF.modelsKP hZF) c.response).1 fs.1
      ((sat s x).mp hx) ((sat s y).mp hy)) (by
    intro s y _ hy
    obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, output⟩ := (sat s y).mp hy
    exact output.elim (fun h => h.2.symm ▸ h.1) (fun h => h.2.symm ▸ ha))
  exact ⟨τ, fn0_of_function_l (ZF.modelsKP hZF) fn, fun s y => (graph s y).trans (and_congr_right fun _ => sat s y)⟩

/-- 完整对局与其有限前缀生成同一当前状态，策略值就是原三步响应的末项。 -/
theorem cg_scan_answer_prefix_l {ω A F T e a s f H n h p t z v y : M.Domain}
    (hw : M.IsOmega ω) (ft : M.IsSetFunction I T) (ff : M.IsSetFunction I f) (fd : M.IsDomainOf I ω f)
    (run : Gi_d hZF false ω F T e a f H) (cut : M.IsRestrictionOf I s f n)
    (nh : Rd_entry_d n h H) (pair : (I).Codes p h a) (pt : Rd_entry_d p t T)
    (endt : Fseq_end_d I ω t z v) (hv : M.mem v A) (answer : Cg_scan_answer_d hZF ω A F T e a s y) : y = v := by
  obtain ⟨n', H', h', p', t', z', v', dom', run', nh', pair', pt', endt', output⟩ := answer
  have eq := dom'.eq hZF.1 (cut.isDomainOf fd (hw.transitive hZF n (run.1.bound_l nh).1))
  subst n'
  have eq := run.prefix_l hZF hw ft ff run' (run.1.bound_l nh).1 cut h h' nh nh'; subst h'
  have eq := (I).unique pair' pair; subst p'
  have eq := ft.2 p t' t pt' pt; subst t'
  have eq := (fseq_end_unique_l I hZF.1 endt' endt).2; subst v'
  exact output.elim And.right (fun h => (h.1 hv).elim)

/-- 三步响应只追加历史，故任何较早轮的全部事件都保留到以后。 -/
theorem Cg_scanner_d.history_mono_l {b : Bool} {ω A X F L O σ g K D T r a f H : M.Domain}
    (c : Cg_scanner_d hZF ω A X F L O σ g K D T) (hw : M.IsOmega ω)
    (run : Gi_d hZF b ω F T r a f H) :
    ∀ n m h t, (M.mem n m ∨ n = m) → Rd_entry_d n h H → Rd_entry_d m t H → M.MemberSubset h t := by
  let φ : BinarySchema 0 := { body := .subset (.bound 1) .newest }
  have fn := fn0_function_l (ZF.modelsKP hZF) run.1
  have chain := ZF.rel_chain_l I hZF φ ⟨Fin.elim0, fun _ => H⟩ hw fn
    (fun _ _ _ _ _ _ xy yz z hz => yz z (xy z hz)) (by
      intro n m h t succ nh mt
      obtain ⟨x, q, _, pair, qt⟩ := run.2.2 n m h t succ nh mt
      obtain ⟨_, _, _, _, _, _, _, _, _, _, e₁, _, _, e₂, _, _, _, e₃⟩ := c.step h x q t pair qt
      exact fun z hz => e₃.subset_l I z (e₂.subset_l I z (e₁.subset_l I z hz)))
  intro n m h t nm nh mt
  exact nm.elim (fun lt => chain n m h t lt nh mt) (fun eq => (fn.1.2 m h t (eq ▸ nh) mt) ▸ fun _ hz => hz)

end YesMetaZFC.SetTheory.Descriptive
