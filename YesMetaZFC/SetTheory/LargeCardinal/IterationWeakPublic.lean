import YesMetaZFC.SetTheory.LargeCardinal.IterationWeakReplay

/-! # 仅以公开走法历史为输入的集合策略

唯一重放恢复内部状态，再由同一请求读取树枝。策略的定义域包含所有指定长度的
走法历史；返回映射与内部状态均不作为对手必须提供的输入。
-/
namespace YesMetaZFC.SetTheory.LargeCardinal
open Definitional.Project InnerModel Internal
universe u
variable {M : Structure.{u}} (hZF : M.Models ZF)

def Wi_position_d (Ω Z F : M.Domain) : Prop := ∃ α ξ, M.mem α Ω ∧ M.SuccessorOf α ξ ∧ Fn0_d α Z F
def wi_position_m {d} (Ω Z F : Term d) : Formula 1 d := set[d] ⟪
  ∃ α ξ, α ∈ ⌜Ω⌝ₛ ∧ ⌜KP.succ0_m⌝ₚ(α, ξ) ∧ ⌜fn0_m⌝ₚ(α, ⌜Z⌝ₛ, ⌜F⌝ₛ)⟫
derive_free_closed wi_position_m
theorem wi_position_sat_l (hE : Extensional M) {d} (η : Env M d) (Ω Z F : Term d) :
    Formula.satisfies η (wi_position_m Ω Z F) ↔ Wi_position_d (Ω.eval η) (Z.eval η) (F.eval η) := by
  simp only [wi_position_m, Wi_position_d, Formula.satisfies_exists_iff, Formula.satisfies_conj_iff,
    Formula.satisfies_mem_iff, KP.succ0_sat_l hE, fn0_sat_l hE, Definitional.Term.eval_weaken]; rfl

def Wi_public_d (o Ψ Z F B : M.Domain) : Prop := ∃ α ξ H t r u s,
  M.SuccessorOf α ξ ∧ Fn0_d α Z F ∧ Wi_run_d hZF o Ψ F α Z H ∧ Rd_entry_d ξ t F ∧
    Rd_triple_d r α H t ∧ Rd_entry_d r u Ψ ∧ KPair_d M u B s
def wi_public_m {d} (o Ψ Z F B : Term d) : Formula 1 d := set[d] ⟪
  ∃ α ξ H t r u s, ⌜KP.succ0_m⌝ₚ(α, ξ) ∧ ⌜fn0_m⌝ₚ(α, ⌜Z⌝ₛ, ⌜F⌝ₛ) ∧
    ⌜wi_run_m⌝ₚ(⌜o⌝ₛ, ⌜Ψ⌝ₛ, ⌜F⌝ₛ, α, ⌜Z⌝ₛ, H) ∧ ⌜rd_entry0_m⌝ₚ(ξ, t, ⌜F⌝ₛ) ∧
    ⌜rd_triple0_m⌝ₚ(r, α, H, t) ∧ ⌜rd_entry0_m⌝ₚ(r, u, ⌜Ψ⌝ₛ) ∧ ⌜kpair0_m⌝ₚ(u, ⌜B⌝ₛ, s)⟫
derive_free_closed wi_public_m
theorem wi_public_sat_l {d} (η : Env M d) (o Ψ Z F B : Term d) :
    Formula.satisfies η (wi_public_m o Ψ Z F B) ↔
      Wi_public_d hZF (o.eval η) (Ψ.eval η) (Z.eval η) (F.eval η) (B.eval η) := by
  simp only [wi_public_m, Wi_public_d, Formula.satisfies_exists_iff, Formula.satisfies_conj_iff,
    KP.succ0_sat_l hZF.1, fn0_sat_l hZF.1, wi_run_sat_l hZF, rd_entry0_sat_l hZF.1,
    rd_triple0_sat_l hZF.1, kpair0_sat_l hZF.1, Definitional.Term.eval_weaken]; rfl

def Wi_strategy_d (o Ψ Ω Z D Γ : M.Domain) : Prop :=
  (∀ F, M.mem F D ↔ Wi_position_d Ω Z F) ∧ Fn0_d D Z Γ ∧
    ∀ F B, Rd_entry_d F B Γ ↔ M.mem F D ∧ Wi_public_d hZF o Ψ Z F B

theorem Wi_public_d.unique_l {o Ψ Z F B C : M.Domain}
    (hΨ : M.IsSetFunction (kp_pair_l (ZF.modelsKP hZF)) Ψ)
    (h : Wi_public_d hZF o Ψ Z F B) (k : Wi_public_d hZF o Ψ Z F C) : B = C := by
  obtain ⟨α, ξ, H, t, r, u, s, hα, ff, run, ht, pack, edge, pair⟩ := h
  obtain ⟨β, η, K, t', r', u', s', hβ, ff', run', ht', pack', edge', pair'⟩ := k
  have eq := ff'.domain_eq_l hZF.1 ff
  subst β
  have eq := Structure.SuccessorOf.predecessor_eq hZF.1 (run.1.1.mem hα.predecessor_mem) hα hβ
  subst η
  have eq := run'.unique_l hZF (fn0_function_l (ZF.modelsKP hZF) ff).1 hΨ run
  subst K
  have eq := (fn0_function_l (ZF.modelsKP hZF) ff).1.2 ξ t' t ht' ht
  subst t'
  obtain ⟨p, pp, pr⟩ := pack
  obtain ⟨q, pq, qr⟩ := pack'
  have eq := kpair_unique_l M hZF.1 pq pp
  subst q
  have eq := kpair_unique_l M hZF.1 qr pr
  subst r'
  exact (kpair_injective_l M pair (hΨ.2 r u' u edge' edge ▸ pair')).1

theorem wi_strategy_exists_l (hZFC : M.Models ZFC) {ω χ Z Ω a A S o s₀ Ψ : M.Domain}
    (hω : M.IsOmega ω) (hχ : M.IsRegularCardinal (kp_pair_l (ZF.modelsKP (ZFC.models_zf_l hZFC))) χ)
    (hωχ : M.mem ω χ) (hZ : H_d (kp_pair_l (ZF.modelsKP (ZFC.models_zf_l hZFC))) χ Z)
    (hΩ : M.IsOrdinal Ω) (hΩZ : M.mem Ω Z) (hoZ : M.mem o Z)
    (select : Wi_selector_d (ZFC.models_zf_l hZFC) ω a A S o s₀ Z Ψ) :
    ∃ D Γ, Wi_strategy_d (ZFC.models_zf_l hZFC) o Ψ Ω Z D Γ := by
  let hZF := ZFC.models_zf_l hZFC
  let I := kp_pair_l (ZF.modelsKP hZF)
  have zt := ZF.h_transitive_l I hZF hZ
  let φ : UnarySchema 2 := { body := wi_position_m (.bound 2) (.bound 1) .newest }
  let ρ : Env M 2 := (⟨fun _ => Ω, fun _ => Ω⟩ : Env M 1).push Z
  obtain ⟨D, ds⟩ := ZF.separation_exists_d hZF φ ρ Z
  have domain F : M.mem F D ↔ Wi_position_d Ω Z F := by
    have sat : φ.denote ρ F ↔ Wi_position_d Ω Z F := wi_position_sat_l hZF.1 ..
    refine (ds F).trans ⟨fun hh => sat.mp hh.2, fun hh => ⟨?_, sat.mpr hh⟩⟩
    obtain ⟨α, _, hα, _, ff⟩ := hh
    exact ZFC.h_function_l hZFC hω hχ hωχ hZ (zt Ω hΩZ α hα) (fn0_function_l (ZF.modelsKP hZF) ff)
  have total F (hf : M.mem F D) : ∃ B, Wi_public_d hZF o Ψ Z F B := by
    obtain ⟨α, ξ, hα, succ, ff⟩ := (domain F).mp hf
    have hαZ := zt Ω hΩZ α hα
    obtain ⟨H, run, _⟩ := wi_run_exists_l hZFC hω hχ hωχ hZ (hΩ.mem hα) hαZ hoZ select ff
    have hh := ZFC.h_function_l hZFC hω hχ hωχ hZ hαZ run.1.2
    obtain ⟨t, ht, move⟩ := ff.2.1 ξ succ.predecessor_mem
    obtain ⟨p, pp⟩ := I.total H t
    obtain ⟨r, pr⟩ := I.total α p
    have hr := ZFC.h_kpair_l hZFC hω hχ hωχ hZ pr hαZ (ZFC.h_kpair_l hZFC hω hχ hωχ hZ pp hh ht)
    obtain ⟨u, _, edge⟩ := select.function.2.1 r hr
    obtain ⟨B, s, pair⟩ := select.values r u edge
    exact ⟨B, α, ξ, H, t, r, u, s, succ, ff, run, move, ⟨p, pp, pr⟩, edge, pair⟩
  let ψ : BinarySchema 3 := { body := wi_public_m (.bound 4) (.bound 3) (.bound 2) (.bound 1) .newest }
  let η : Env M 3 := ((⟨fun _ => o, fun _ => o⟩ : Env M 1).push Ψ).push Z
  have sat F B : ψ.denote η F B ↔ Wi_public_d hZF o Ψ Z F B := wi_public_sat_l hZF ..
  obtain ⟨Γ, fn, gs⟩ := ZF.exists_setFunctionFromTo_of_denote hZF I ψ η (source := D) (target := Z)
    (fun F hf => (total F hf).imp fun B hb => (sat F B).mpr hb)
    (fun F _ B C hb hc => ((sat F B).mp hb).unique_l hZF (fn0_function_l (ZF.modelsKP hZF) select.function).1 ((sat F C).mp hc))
    (fun F B _ hb => by
      obtain ⟨_, _, _, _, r, u, _, _, _, _, _, _, edge, pair⟩ := (sat F B).mp hb
      exact (pair.mem_l M zt (select.function.bound_l edge).2).1)
  exact ⟨D, Γ, domain, fn0_of_function_l (ZF.modelsKP hZF) fn,
    fun F B => (gs F B).trans (and_congr_right fun _ => sat F B)⟩

end YesMetaZFC.SetTheory.LargeCardinal
