import YesMetaZFC.SetTheory.LargeCardinal.IterationCutNormalize
import YesMetaZFC.SetTheory.HereditaryCover

/-! # 含恒等步的双重基础反证

分离全部合法有限历史，先取末模型的隶属极小值，再在同一模型的历史中
取原高度极小值。活动步使模型下降，恒等步使原高度下降，两者均矛盾。
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

/-- 含恒等步的 nice 树，其实际正则秩段列不能沿每条后继边严格下降。 -/
theorem it_pnice_no_drop_l {ω c T Q G E L A D z a X P π ι : M.Domain}
    (nice : It_pnice_d (ZFC.models_zf_l hZFC) ω c ω T Q G E L)
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
  obtain ⟨A', D', cuts', _, roots, pads, strict⟩ := it_cut_normalize_l hZFC nice cuts hz drop
  have hq' := (roots a).mpr hq
  -- 固定包络容纳原码列和初始模型；后续模型沿隶属下降，始终留在此包络。
  obtain ⟨B, pair⟩ := KP.exists_pair (ZF.modelsKP hZF) D' P
  obtain ⟨χ, C, reg, above, hc, hBC⟩ := ZFC.h_cover_l I hZFC hω B
  have ct := ZF.h_transitive_l I hZF hc
  have algebra := sc_h_algebra_l hZFC hω reg above hc
  have hDC := ct B hBC D' ((pair D').mpr (Or.inl rfl))
  have hPC := ct B hBC P ((pair P).mpr (Or.inr rfl))
  have codes i b (hb : Rd_entry_d i b D') := (rd_entry_transitive_l ct hDC hb).2
  obtain ⟨r, hrC, cell⟩ := initial.cell_l hZF ct algebra (codes z a hq') hPC
  have hzω := (cuts'.code_domain z).mpr ⟨a, hq'⟩
  obtain ⟨o, ho, hoω⟩ := hω.1.2 z hzω
  obtain ⟨H₀, history₀, _⟩ := pn_history_start_l hZF hz ho hq' cell initial hrC
  obtain ⟨s₀, pair₀⟩ := I.total z H₀
  have first : Pn_state_d hZF ω D' L C s₀ := ⟨z, H₀, o, pair₀, hzω, ho, history₀⟩
  obtain ⟨S, seq⟩ := ZF.fseq_space_exists_l I hZF hω C
  obtain ⟨U, product⟩ := ZF.exists_cartesianProduct hZF I ω S
  let η : Env M 4 := ⟨Fin.cases C (Fin.cases L (Fin.cases D' (fun _ => ω))), fun _ => ω⟩
  let φ : UnarySchema 4 := { body := pn_state_m (.bound 4) (.bound 3) (.bound 2) (.bound 1) .newest }
  have read s : φ.denote η s ↔ Pn_state_d hZF ω D' L C s := pn_state_sat_l hZF ..
  obtain ⟨B, bs⟩ := ZF.separation_exists_d hZF φ η U
  have state s : M.mem s B ↔ Pn_state_d hZF ω D' L C s := by
    rw [bs s]
    change (M.mem s U ∧ φ.denote η s) ↔ _
    rw [read s]
    refine ⟨And.right, fun h => ⟨?_, h⟩⟩
    obtain ⟨n, H, m, pair, hn, hm, hist⟩ := h
    exact (product s).mpr ⟨n, hn, H, (seq H).mpr ⟨m, succ_mem hn hm, fn0_function_l (ZF.modelsKP hZF) hist.function⟩, pair⟩
  have last_exists s (hs : M.mem s B) : ∃ P, Pn_last_d s P := by
    obtain ⟨n, H, m, pair, _, hm, hist⟩ := (state s).mp hs
    obtain ⟨r, _, hr⟩ := hist.function.2.1 n hm.predecessor_mem
    obtain ⟨a, X, P, π, ι, cell, _⟩ := hist.rows n r hr
    exact ⟨P, n, H, r, a, X, π, ι, pair, hr, cell⟩
  have last_mem s P (hs : M.mem s B) (hp : Pn_last_d s P) : M.mem P C := by
    obtain ⟨n, H, m, pair, _, _, hist⟩ := (state s).mp hs
    obtain ⟨n', H', r, a, X, π, ι, pair', hr, q, path, _⟩ := hp
    obtain ⟨e, e'⟩ := kpair_injective_l M pair' pair
    subst n' H'
    obtain ⟨v, pv, pr⟩ := path
    exact (pv.mem_l M ct (pr.mem_l M ct (hist.function.bound_l hr).2).2).1
  -- 第一层基础：所有合法历史的末模型组成一个真实集合。
  let ψ : UnarySchema 1 := { body := .existsMem (.bound 1) (pn_last_m .newest (.bound 1)) }
  let θ : Env M 1 := ⟨fun _ => B, fun _ => B⟩
  have readP P : ψ.denote θ P ↔ ∃ s, M.mem s B ∧ Pn_last_d s P := by
    simp only [ψ, UnarySchema.denote, Formula.satisfies_existsMem_iff, pn_last_sat_l hZF.1]; rfl
  obtain ⟨V, vs⟩ := ZF.separation_exists_d hZF ψ θ C
  have ps P : M.mem P V ↔ ∃ s, M.mem s B ∧ Pn_last_d s P := by
    refine (vs P).trans ?_
    change (M.mem P C ∧ ψ.denote θ P) ↔ _
    rw [readP]
    exact ⟨And.right, fun h => ⟨by obtain ⟨s, hs, last⟩ := h; exact last_mem s P hs last, h⟩⟩
  obtain ⟨P₀, last₀⟩ := last_exists s₀ ((state s₀).mpr first)
  obtain ⟨P, hP, minP⟩ := KP.mem_minimal_exists_d (ZF.modelsKP hZF)
    ⟨P₀, (ps P₀).mpr ⟨s₀, (state s₀).mpr first, last₀⟩⟩
  -- 第二层基础：固定末模型后，原高度仍是已有高度列的一个子集。
  let χ : UnarySchema 3 := { body := set[4] ⟪∃ s ∈ ⌜(Term.bound 2 : Term 4)⌝ₛ,
    ⌜pn_last_m⌝ₚ(s, ⌜(Term.bound 1 : Term 4)⌝ₛ) ∧
    (∃ n H, ⌜kpair_m⌝ₚ(s, n, H) ∧ ⌜rd_entry0_m⌝ₚ(n, ⌜(Term.newest : Term 4)⌝ₛ, ⌜(Term.bound 3 : Term 4)⌝ₛ))⟫ }
  let ξ : Env M 3 := ⟨Fin.cases P (Fin.cases B (fun _ => A)), fun _ => A⟩
  have readA α : χ.denote ξ α ↔ ∃ s, M.mem s B ∧ Pn_last_d s P ∧
      ∃ n H, KPair_d M s n H ∧ Rd_entry_d n α A := by
    simp only [χ, UnarySchema.denote, Formula.satisfies_existsMem_iff, Formula.satisfies_conj_iff,
      Formula.satisfies_exists_iff, pn_last_sat_l hZF.1, kpair_sat_l M hZF.1, rd_entry0_sat_l hZF.1,
      Definitional.Term.eval_weaken]; rfl
  obtain ⟨W, ws⟩ := ZF.exists_range_of_setFunction hZF I cuts.heights cuts.height_domain
  obtain ⟨U, us⟩ := ZF.separation_exists_d hZF χ ξ W
  have values α : M.mem α U ↔ ∃ s, M.mem s B ∧ Pn_last_d s P ∧
      ∃ n H, KPair_d M s n H ∧ Rd_entry_d n α A := by
    refine (us α).trans ?_
    change (M.mem α W ∧ χ.denote ξ α) ↔ _
    rw [readA]
    exact ⟨And.right, fun h => ⟨by obtain ⟨_, _, _, n, _, _, hα⟩ := h; exact (ws α).mpr ⟨n, hα⟩, h⟩⟩
  have nonempty : ∃ α, M.mem α U := by
    obtain ⟨s, hs, last⟩ := (ps P).mp hP
    obtain ⟨n, H, _, pair, hn, _⟩ := (state s).mp hs
    obtain ⟨α, hα⟩ := (cuts.height_domain n).mp hn
    exact ⟨α, (values α).mpr ⟨s, hs, last, n, H, pair, hα⟩⟩
  obtain ⟨α, hα, minα⟩ := KP.mem_minimal_exists_d (ZF.modelsKP hZF) nonempty
  obtain ⟨s, hs, last, n, H, pair, height⟩ := (values α).mp hα
  obtain ⟨n₀, H₁, m, pair', hn, hm, hist⟩ := (state s).mp hs
  obtain ⟨eqn, eqH⟩ := kpair_injective_l M pair' pair
  subst n₀ H₁
  obtain ⟨n₀, H₁, r, a, X, π, ι, pair', hr, cell⟩ := last
  obtain ⟨eqn, eqH⟩ := kpair_injective_l M pair' pair
  subst n₀ H₁
  obtain ⟨l, J, hl, hist', keep⟩ := pn_history_extend_l hZFC nice cuts' pads strict hist hn hm ct algebra codes
  obtain ⟨t, pairt⟩ := I.total m J
  have ht := (state t).mpr ⟨m, J, l, pairt, succ_mem hn hm, hl, hist'⟩
  obtain ⟨q, _, hq⟩ := hist'.function.2.1 m hl.predecessor_mem
  obtain ⟨b, Y, N, σ, η, cq, _, _⟩ := hist'.rows m q hq
  have lastt : Pn_last_d t N := ⟨m, J, q, b, Y, σ, η, pairt, hq, cq⟩
  obtain ⟨_, below, active⟩ := hist'.past n m r q a X P π ι b Y N σ η (keep n r hr) hq hm.predecessor_mem cell cq
  have eq := below.resolve_right (minP N ((ps N).mpr ⟨t, ht, lastt⟩))
  subst N
  have inactive ρ (hρ : Rd_entry_d n ρ L) : False := KP.mem_irrefl_d (ZF.modelsKP hZF) P (active ⟨ρ, hρ⟩)
  obtain ⟨k, b, d, e, f, p, pred, _, _, _, hf, hp, data⟩ := nice.tree.steps n m (succ_mem hn hm) hm
  have pad : k = n ∧ ∀ x y, Rd_entry_d x y f → x = y := by
    rcases data with ⟨_, eq, _, ident⟩ | ⟨κ, ρ, F, _, _, _, _, pay, _⟩
    · exact ⟨eq, ident⟩
    · exact (inactive ρ ((nice.levels n ρ).mpr ⟨p, κ, F, hp, pay⟩)).elim
  obtain ⟨eq, ident⟩ := pad
  subst k
  obtain ⟨β, hβ⟩ := (cuts.height_domain m).mp (succ_mem hn hm)
  obtain ⟨γ, image, less⟩ := drop n m n f α β hm pred hf height hβ
  have eq := ident α γ image
  subst γ
  exact minα β ((values β).mpr ⟨t, ht, lastt, m, J, pairt, hβ⟩) less

end YesMetaZFC.SetTheory.LargeCardinal
