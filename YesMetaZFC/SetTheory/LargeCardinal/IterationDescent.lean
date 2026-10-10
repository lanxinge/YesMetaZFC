import YesMetaZFC.SetTheory.LargeCardinal.IterationCutHistory
import YesMetaZFC.SetTheory.HereditaryCover
import YesMetaZFC.SetTheory.Collapse.RelationSequence

/-! # 内部 ω 递归与下降反证

先分离全部合法有限历史，再对实际可延伸关系使用背景 ZFC 的依赖选择。
取每段历史的末模型得到内部 ω 隶属下降图，由原基础公理排除。
-/
namespace YesMetaZFC.SetTheory.LargeCardinal
open Definitional.Project InnerModel Internal
universe u
variable {M : Structure.{u}} (hZF : M.Models ZF)

private def Pn_state_d (ω D L C s : M.Domain) : Prop := ∃ n H m,
  KPair_d M s n H ∧ M.mem n ω ∧ M.SuccessorOf m n ∧ Pn_history_d hZF ω D L C m H

private def pn_state_m {d} (ω D L C s : Term d) : Formula 1 d := set[d] ⟪
  ∃ n H m, ⌜kpair_m⌝ₚ(⌜s⌝ₛ, n, H) ∧ n ∈ ⌜ω⌝ₛ ∧ ⌜KP.succ0_m⌝ₚ(m, n) ∧ ⌜pn_history_m⌝ₚ(⌜ω⌝ₛ, ⌜D⌝ₛ, ⌜L⌝ₛ, ⌜C⌝ₛ, m, H)⟫
derive_free_closed pn_state_m

private theorem pn_state_sat_l {d} (η : Env M d) (ω D L C s : Term d) :
    Formula.satisfies η (pn_state_m ω D L C s) ↔ Pn_state_d hZF (ω.eval η) (D.eval η) (L.eval η) (C.eval η) (s.eval η) := by
  simp only [pn_state_m, Pn_state_d, Formula.satisfies_exists_iff, Formula.satisfies_conj_iff,
    kpair_sat_l M hZF.1, Formula.satisfies_mem_iff, KP.succ0_sat_l hZF.1, pn_history_sat_l hZF,
    Definitional.Term.eval_weaken]; rfl

private def Pn_last_d (s P : M.Domain) : Prop := ∃ n H r a X π ι,
  KPair_d M s n H ∧ Rd_entry_d n r H ∧ Pn_cell_d r a X P π ι

private def pn_last_m {d} (s P : Term d) : Formula 1 d := set[d] ⟪
  ∃ n H r a X π ι, ⌜kpair_m⌝ₚ(⌜s⌝ₛ, n, H) ∧ ⌜rd_entry0_m⌝ₚ(n, r, H) ∧ ⌜pn_cell_m⌝ₚ(r, a, X, ⌜P⌝ₛ, π, ι)⟫
derive_free_closed pn_last_m

private theorem pn_last_sat_l (hE : Extensional M) {d} (η : Env M d) (s P : Term d) :
    Formula.satisfies η (pn_last_m s P) ↔ Pn_last_d (s.eval η) (P.eval η) := by
  simp only [pn_last_m, Pn_last_d, Formula.satisfies_exists_iff, Formula.satisfies_conj_iff,
    kpair_sat_l M hE, rd_entry0_sat_l hE, pn_cell_sat_l hE, Definitional.Term.eval_weaken]; rfl

variable (hZFC : M.Models ZFC)

/-- nice 树的正则秩段列不能沿每条后继边严格下降。 -/
theorem it_nice_no_drop_l {ω c T Q G E L A D z a X P π ι : M.Domain}
    (nice : It_nice_d (ZFC.models_zf_l hZFC) ω c ω T Q G E L)
    (cuts : It_cut_d (ZFC.models_zf_l hZFC) ω ω Q E A D)
    (hz : ∀ x, ¬ M.mem x z) (hq : Rd_entry_d z a D) (initial : Pn_row_d (ZFC.models_zf_l hZFC) ω a X P π ι) :
    ¬ (∀ i j k f α β, M.SuccessorOf j i → It_pred_d T k j → It_map_d G k j f →
      Rd_entry_d k α A → Rd_entry_d j β A → ∃ γ, Rd_entry_d α γ f ∧ M.mem β γ) := by
  intro drop
  let hZF := ZFC.models_zf_l hZFC
  let I := kp_pair_l (ZF.modelsKP hZF)
  have hω := nice.tree.omega
  have succ_mem {n m} (hn : M.mem n ω) (hm : M.SuccessorOf m n) : M.mem m ω := by
    obtain ⟨m', hm', h'⟩ := hω.1.2 n hn
    exact (hZF.1.eq_of_same_members m' m (fun x => (hm' x).trans (hm x).symm)) ▸ h'
  -- 固定包络容纳原码列和初始模型；后续模型沿隶属下降，始终留在此包络。
  obtain ⟨B, pair⟩ := KP.exists_pair (ZF.modelsKP hZF) D P
  obtain ⟨χ, C, reg, above, hc, hBC⟩ := ZFC.h_cover_l I hZFC hω B
  have ct := ZF.h_transitive_l I hZF hc
  have algebra := sc_h_algebra_l hZFC hω reg above hc
  have hDC := ct B hBC D ((pair D).mpr (Or.inl rfl))
  have hPC := ct B hBC P ((pair P).mpr (Or.inr rfl))
  have codes i b (hb : Rd_entry_d i b D) := (rd_entry_transitive_l ct hDC hb).2
  obtain ⟨r, hrC, cell⟩ := initial.cell_l hZF ct algebra (codes z a hq) hPC
  have hzω := (cuts.code_domain z).mpr ⟨a, hq⟩
  obtain ⟨o, ho, hoω⟩ := hω.1.2 z hzω
  obtain ⟨H₀, history₀, _⟩ := pn_history_start_l hZF hz ho hq cell initial hrC
  obtain ⟨s₀, pair₀⟩ := I.total z H₀
  have first : Pn_state_d hZF ω D L C s₀ := ⟨z, H₀, o, pair₀, hzω, ho, history₀⟩
  obtain ⟨S, seq⟩ := ZF.fseq_space_exists_l I hZF hω C
  obtain ⟨U, product⟩ := ZF.exists_cartesianProduct hZF I ω S
  let η : Env M 4 := ⟨Fin.cases C (Fin.cases L (Fin.cases D (fun _ => ω))), fun _ => ω⟩
  let φ : UnarySchema 4 := { body := pn_state_m (.bound 4) (.bound 3) (.bound 2) (.bound 1) .newest }
  have read s : φ.denote η s ↔ Pn_state_d hZF ω D L C s := pn_state_sat_l hZF ..
  obtain ⟨B, bs⟩ := ZF.separation_exists_d hZF φ η U
  have state s : M.mem s B ↔ Pn_state_d hZF ω D L C s := by
    rw [bs s]
    change (M.mem s U ∧ φ.denote η s) ↔ _
    rw [read s]
    refine ⟨And.right, fun h => ⟨?_, h⟩⟩
    obtain ⟨n, H, m, pair, hn, hm, hist⟩ := h
    exact (product s).mpr ⟨n, hn, H, (seq H).mpr ⟨m, succ_mem hn hm, fn0_function_l (ZF.modelsKP hZF) hist.function⟩, pair⟩
  let θ : Env M 0 := ⟨Fin.elim0, fun _ => ω⟩
  let ψ : BinarySchema 0 := { body := set[2] ⟪∃ n H m J,
    ⌜kpair_m⌝ₚ(⌜(Term.bound 1 : Term 2)⌝ₛ, n, H) ∧ ⌜kpair_m⌝ₚ(⌜(Term.newest : Term 2)⌝ₛ, m, J) ∧ ⌜KP.succ0_m⌝ₚ(m, n) ∧
    (∀ i r, ⌜rd_entry0_m⌝ₚ(i, r, H) → ⌜rd_entry0_m⌝ₚ(i, r, J))⟫ }
  have step x y : ψ.denote θ x y ↔ ∃ n H m J, KPair_d M x n H ∧ KPair_d M y m J ∧
      M.SuccessorOf m n ∧ ∀ i r, Rd_entry_d i r H → Rd_entry_d i r J := by
    simp only [ψ, BinarySchema.denote, Formula.satisfies_exists_iff, Formula.satisfies_conj_iff,
      kpair_sat_l M hZF.1, KP.succ0_sat_l hZF.1, Formula.satisfies_forall_iff,
      Formula.satisfies_imp_iff, rd_entry0_sat_l hZF.1, Definitional.Term.eval_weaken]; rfl
  obtain ⟨R, _, rs⟩ := ZF.exists_setRelationOn_of_denote hZF I ψ θ B
  obtain ⟨g, gf, _, gs⟩ := ZFC.dependent_choice_l I hZFC hω ((state s₀).mpr first) (R := R) (by
    intro s hs
    obtain ⟨n, H, m, pair, hn, hm, hist⟩ := (state s).mp hs
    obtain ⟨l, J, hl, hist', extend⟩ := pn_history_extend_l hZFC nice cuts drop hist hn hm ct algebra codes
    obtain ⟨t, pt⟩ := I.total m J
    have ht := (state t).mpr ⟨m, J, l, pt, succ_mem hn hm, hl, hist'⟩
    exact ⟨t, ht, (rs s t).mpr ⟨hs, ht, (step s t).mpr ⟨n, H, m, J, pair, pt, hm, extend⟩⟩⟩)
  -- 末模型投影由真实历史的函数性唯一决定，整张投影图由替代构造。
  have last_exists s (hs : M.mem s B) : ∃ P, Pn_last_d s P := by
    obtain ⟨n, H, m, pair, _, hm, hist⟩ := (state s).mp hs
    obtain ⟨r, _, hr⟩ := hist.function.2.1 n hm.predecessor_mem
    obtain ⟨a, X, P, π, ι, cell, _⟩ := hist.rows n r hr
    exact ⟨P, n, H, r, a, X, π, ι, pair, hr, cell⟩
  have last_unique s P Q (hs : M.mem s B) (hp : Pn_last_d s P) (hq : Pn_last_d s Q) : P = Q := by
    obtain ⟨n, H, m, pair, _, _, hist⟩ := (state s).mp hs
    obtain ⟨n', H', r, a, X, π, ι, pair', hr, cell⟩ := hp
    obtain ⟨e, e'⟩ := kpair_injective_l M pair' pair
    subst n' H'
    obtain ⟨n', H', t, b, Y, σ, ξ, pair', ht, cell'⟩ := hq
    obtain ⟨e, e'⟩ := kpair_injective_l M pair' pair
    subst n' H'
    have eq := (fn0_function_l (ZF.modelsKP hZF) hist.function).1.2 n r t hr ht
    subst t
    exact (cell.unique_l cell').2.2.1
  have last_mem s P (hs : M.mem s B) (hp : Pn_last_d s P) : M.mem P C := by
    obtain ⟨n, H, m, pair, _, _, hist⟩ := (state s).mp hs
    obtain ⟨n', H', r, a, X, π, ι, pair', hr, q, path, _⟩ := hp
    obtain ⟨e, e'⟩ := kpair_injective_l M pair' pair
    subst n' H'
    obtain ⟨v, pv, pr⟩ := path
    exact (pv.mem_l M ct (pr.mem_l M ct (hist.function.bound_l hr).2).2).1
  let last : BinarySchema 0 := { body := pn_last_m (.bound 1) .newest }
  have last_read s P : last.denote θ s P ↔ Pn_last_d s P := pn_last_sat_l hZF.1 ..
  obtain ⟨t, tf, ts⟩ := ZF.exists_setFunctionFromTo_of_denote hZF I last θ (source := B) (target := C)
    (fun s hs => (last_exists s hs).imp fun P hp => (last_read s P).mpr hp)
    (fun s hs P Q hp hq => last_unique s P Q hs ((last_read s P).mp hp) ((last_read s Q).mp hq))
    (fun s P hs hp => last_mem s P hs ((last_read s P).mp hp))
  obtain ⟨f, ff, fs⟩ := ZF.exists_compositionFunction hZF I gf tf
  obtain ⟨V, wf, vs⟩ := wf_membership_l hZF C
  apply wf_no_desc_l hZF hω wf (fn0_of_function_l (ZF.modelsKP hZF) ff)
  intro i j P Q hij hi hj
  obtain ⟨_, s, his, hsP⟩ := (fs i P).mp hi
  obtain ⟨_, t, hjt, htQ⟩ := (fs j Q).mp hj
  obtain ⟨hs, ht, edge⟩ := (rs s t).mp (gs i j s t hij his hjt)
  obtain ⟨n, H, m, J, pair, pair', succ, extend⟩ := (step s t).mp edge
  obtain ⟨n', H', r, a, X, π, ι, p, hr, cr⟩ := (last_read s P).mp ((ts s P).mp hsP).2
  obtain ⟨e, e'⟩ := kpair_injective_l M p pair
  subst n' H'
  obtain ⟨m', J', q, b, Y, σ, ξ, p, hq, cq⟩ := (last_read t Q).mp ((ts t Q).mp htQ).2
  obtain ⟨e, e'⟩ := kpair_injective_l M p pair'
  subst m' J'
  obtain ⟨m', J', l, p, _, _, hist⟩ := (state t).mp ht
  obtain ⟨e, e'⟩ := kpair_injective_l M p pair'
  subst m' J'
  obtain ⟨_, _, _, member, _⟩ := hist.past n m r q a X P π ι b Y Q σ ξ (extend n r hr) hq succ.predecessor_mem cr cq
  exact (vs Q P).mpr ⟨ff.output_mem_of_pairMember hj, ff.output_mem_of_pairMember hi, member⟩

end YesMetaZFC.SetTheory.LargeCardinal
