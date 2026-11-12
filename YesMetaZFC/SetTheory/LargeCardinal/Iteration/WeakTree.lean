import YesMetaZFC.SetTheory.LargeCardinal.Iteration.Weak
import YesMetaZFC.SetTheory.LargeCardinal.Iteration.WeakAnswerTreeSyntax
import YesMetaZFC.SetTheory.LargeCardinal.Iteration.WeakAnswer

/-! # 强实际应答请求及其选择器公式

请求关系直接使用 `Wi_answer_tree_d`，故选择器得到的每个值都携带完整强证书。
-/
namespace YesMetaZFC.SetTheory.LargeCardinal

open Definitional.Project InnerModel Internal
universe u
variable {M : Structure.{u}} (hZF : M.Models ZF)

def wi_request_tree_m {d} (ω a A S o s₀ r u : Term d) : Formula 1 d := set[d] ⟪
  ∃ α H t B s,
    ⌜rd_triple0_m⌝ₚ(⌜r⌝ₛ, α, H, t) ∧
    ⌜kpair0_m⌝ₚ(⌜u⌝ₛ, B, s) ∧
    ⌜wi_answer_tree_m⌝ₚ(⌜ω⌝ₛ, ⌜a⌝ₛ, ⌜A⌝ₛ, ⌜S⌝ₛ, ⌜o⌝ₛ, ⌜s₀⌝ₛ, α, H, t, B, s)⟫
derive_free_closed wi_request_tree_m

theorem wi_request_tree_sat_l {d} (η : Env M d) (ω a A S o s₀ r u : Term d) :
    Formula.satisfies η (wi_request_tree_m ω a A S o s₀ r u) ↔
      Wi_request_tree_d hZF
        (ω.eval η) (a.eval η) (A.eval η) (S.eval η) (o.eval η) (s₀.eval η)
        (r.eval η) (u.eval η) := by
  simp only [wi_request_tree_m, Wi_request_tree_d, Formula.satisfies_exists_iff,
    Formula.satisfies_conj_iff, rd_triple0_sat_l hZF.1, kpair0_sat_l hZF.1,
    wi_answer_tree_sat_l hZF, Definitional.Term.eval_weaken]
  rfl

def wi_select_tree_m {d} (ω a A S o s₀ Z u₀ r u : Term d) : Formula 1 d := set[d] ⟪
  ⌜wi_request_tree_m⌝ₚ(⌜ω⌝ₛ, ⌜a⌝ₛ, ⌜A⌝ₛ, ⌜S⌝ₛ, ⌜o⌝ₛ, ⌜s₀⌝ₛ, ⌜r⌝ₛ, ⌜u⌝ₛ) ∨
  (⌜u⌝ₛ = ⌜u₀⌝ₛ ∧ ¬ (∃ v ∈ ⌜Z⌝ₛ,
    ⌜wi_request_tree_m⌝ₚ(⌜ω⌝ₛ, ⌜a⌝ₛ, ⌜A⌝ₛ, ⌜S⌝ₛ, ⌜o⌝ₛ, ⌜s₀⌝ₛ, ⌜r⌝ₛ, v)))⟫
derive_free_closed wi_select_tree_m

theorem wi_select_tree_sat_l {d} (η : Env M d) (ω a A S o s₀ Z u₀ r u : Term d) :
    Formula.satisfies η (wi_select_tree_m ω a A S o s₀ Z u₀ r u) ↔
      Wi_request_tree_d hZF
        (ω.eval η) (a.eval η) (A.eval η) (S.eval η) (o.eval η) (s₀.eval η)
        (r.eval η) (u.eval η) ∨
      (u.eval η = u₀.eval η ∧ ¬ ∃ v, M.mem v (Z.eval η) ∧
        Wi_request_tree_d hZF
          (ω.eval η) (a.eval η) (A.eval η) (S.eval η) (o.eval η) (s₀.eval η)
          (r.eval η) v) := by
  simp only [wi_select_tree_m, Formula.satisfies_disj_iff,
    Formula.satisfies_conj_iff, Formula.satisfies_extensionalEq_iff_eq hZF.1,
    Formula.satisfies_neg_iff, Formula.satisfies_existsMem_iff,
    wi_request_tree_sat_l hZF, Definitional.Term.eval_weaken]
  rfl

/-! 强选择器的具体 ZFC 出口。 -/
theorem wi_selector_tree_exists_l (hZFC : M.Models ZFC)
    {ω a A S o s₀ Z u₀ : M.Domain} (hu₀ : M.mem u₀ Z)
    (pair : KPair_d M u₀ o s₀) :
    ∃ Ψ, Wi_selector_tree_d (ZFC.models_zf_l hZFC) ω a A S o s₀ Z Ψ := by
  classical
  let hZF := ZFC.models_zf_l hZFC
  let I := kp_pair_l (ZF.modelsKP hZF)
  let η : Env M 8 :=
    (((((((⟨fun _ => ω, fun _ => ω⟩ : Env M 1).push a).push A).push S).push o).push s₀).push Z).push u₀
  let φ : BinarySchema 8 := { body :=
    (wi_select_tree_m (.bound 9) (.bound 8) (.bound 7) (.bound 6)
      (.bound 5) (.bound 4) (.bound 3) (.bound 2) (.bound 1) .newest) }
  have sat r u : φ.denote η r u ↔
      Wi_request_tree_d hZF ω a A S o s₀ r u ∨
        (u = u₀ ∧ ¬ ∃ v, M.mem v Z ∧ Wi_request_tree_d hZF ω a A S o s₀ r v) := by
    simp only [φ, BinarySchema.denote, wi_select_tree_m,
      Formula.satisfies_disj_iff, Formula.satisfies_conj_iff,
      Formula.satisfies_extensionalEq_iff_eq hZF.1, Formula.satisfies_neg_iff,
      Formula.satisfies_existsMem_iff, wi_request_tree_sat_l hZF,
      Definitional.Term.eval_weaken]
    rfl
  obtain ⟨Ψ, hf, selects⟩ := ZFC.uniformize_formula_l I hZFC φ η
    (X := Z) (Y := Z) (fun r _ => by
      by_cases good : ∃ v, M.mem v Z ∧ Wi_request_tree_d hZF ω a A S o s₀ r v
      · obtain ⟨u, hu, answer⟩ := good
        exact ⟨u, hu, (sat r u).mpr (Or.inl answer)⟩
      · exact ⟨u₀, hu₀, (sat r u₀).mpr (Or.inr ⟨rfl, good⟩)⟩)
  refine ⟨Ψ, fn0_of_function_l (ZF.modelsKP hZF) hf, ?_, ?_⟩
  · intro r u edge
    rcases (sat r u).mp (selects r u edge) with ⟨_, _, _, B, s, _, pu, _⟩ | ⟨eq, _⟩
    · exact ⟨B, s, pu⟩
    · exact ⟨o, s₀, eq.symm ▸ pair⟩
  · intro r u edge available
    exact ((sat r u).mp (selects r u edge)).elim id
      (fun hh => (hh.2 available).elim)

end YesMetaZFC.SetTheory.LargeCardinal

/-! 强选择器驱动的运行存在性。-/
namespace YesMetaZFC.SetTheory.LargeCardinal
open Definitional.Project InnerModel Internal
universe u
variable {M : Structure.{u}}
theorem wi_run_exists_tree_l (hZFC : M.Models ZFC) {ω χ Z Ω a A S o s₀ Ψ F : M.Domain}
    (hω : M.IsOmega ω) (hχ : M.IsRegularCardinal (kp_pair_l (ZF.modelsKP (ZFC.models_zf_l hZFC))) χ)
    (hωχ : M.mem ω χ) (hZ : H_d (kp_pair_l (ZF.modelsKP (ZFC.models_zf_l hZFC))) χ Z)
    (hΩ : M.IsOrdinal Ω) (hΩZ : M.mem Ω Z) (hoZ : M.mem o Z)
    (select : Wi_selector_tree_d (ZFC.models_zf_l hZFC) ω a A S o s₀ Z Ψ) (moves : Fn0_d Ω Z F) :
    ∃ H, Wi_run_d (ZFC.models_zf_l hZFC) o Ψ F Ω Z H ∧
      ∀ H', Wi_run_d (ZFC.models_zf_l hZFC) o Ψ F Ω Z H' → H' = H := by
  classical
  let hZF := ZFC.models_zf_l hZFC
  let I := kp_pair_l (ZF.modelsKP hZF)
  let η : Env M 3 := ((⟨fun _ => o, fun _ => o⟩ : Env M 1).push Ψ).push F
  have sat H s : wi_drive_schema.denote η H s ↔ Wi_drive_d o Ψ F H s := wi_drive_sat_l (ZF.modelsKP hZF) ..
  have zt := ZF.h_transitive_l I hZF hZ
  have ff := fn0_function_l (ZF.modelsKP hZF) moves
  have pf := fn0_function_l (ZF.modelsKP hZF) select.function
  have total H (seq : M.IsSequenceInBelow I H Ω Z) : ∃ s, Wi_drive_d o Ψ F H s := by
    obtain ⟨_, α, hα, seq⟩ := seq
    have hαZ := zt Ω hΩZ α hα
    have hh := ZFC.h_function_l hZFC hω hχ hωχ hZ hαZ seq.2
    have input : ∃ t, M.mem t Z ∧ Wi_input_d o F α t := by
      by_cases succ : ∃ ξ, M.SuccessorOf α ξ
      · obtain ⟨ξ, hξ⟩ := succ
        obtain ⟨t, ht, edge⟩ := moves.2.1 ξ (hΩ.transitive α hα ξ hξ.predecessor_mem)
        exact ⟨t, ht, Or.inl ⟨ξ, hξ, edge⟩⟩
      · exact ⟨o, hoZ, Or.inr ⟨fun ξ hξ => succ ⟨ξ, hξ⟩, rfl⟩⟩
    obtain ⟨t, ht, input⟩ := input
    obtain ⟨p, pp⟩ := I.total H t
    obtain ⟨r, pr⟩ := I.total α p
    have hr := ZFC.h_kpair_l hZFC hω hχ hωχ hZ pr hαZ (ZFC.h_kpair_l hZFC hω hχ hωχ hZ pp hh ht)
    obtain ⟨u, _, edge⟩ := select.function.2.1 r hr
    obtain ⟨B, s, pair⟩ := select.values r u edge
    exact ⟨s, α, t, r, u, B, seq.2.2.1, input, ⟨p, pp, pr⟩, edge, pair⟩
  have functional : M.IsClassFunctionOnSequencesInBelow I (wi_drive_schema.denote η) Ω Z := by
    intro H seq
    obtain ⟨s, hs⟩ := total H seq
    refine ⟨s, (sat H s).mpr hs, fun v hv => ?_⟩
    obtain ⟨_, α, _, seq⟩ := seq
    exact ((sat H v).mp hv).unique_l (ZF.modelsKP hZF) ⟨seq.1, seq.2.1, seq.2.2.1⟩ ff.1 pf.1 hs
  have into : M.MapsSequencesInBelowInto I (wi_drive_schema.denote η) Ω Z := by
    intro H s _ hs
    obtain ⟨_, _, r, u, _, _, _, _, edge, pair⟩ := (sat H s).mp hs
    exact (pair.mem_l M zt (select.function.bound_l edge).2).2
  obtain ⟨H, run, unique⟩ := ZF.recursiveSequenceIn_existsUnique hZF I η wi_drive_schema hΩ functional into
  have convert K : M.IsRecursiveSequenceIn I (wi_drive_schema.denote η) K Ω Z ↔ Wi_run_d hZF o Ψ F Ω Z K := by
    refine and_congr_right fun _ => forall_congr' fun i => imp_congr_right fun hi => forall_congr' fun s => imp_congr_right fun edge => ?_
    exact exists_congr fun J => and_congr_right fun _ => sat J s
  exact ⟨H, (convert H).mp run, fun K hk => unique K ((convert K).mpr hk)⟩


end YesMetaZFC.SetTheory.LargeCardinal

/-! 强选择器驱动的公开策略构造。-/
namespace YesMetaZFC.SetTheory.LargeCardinal
open Definitional.Project InnerModel Internal
universe u
variable {M : Structure.{u}}
theorem wi_strategy_tree_exists_l (hZFC : M.Models ZFC) {ω χ Z Ω a A S o s₀ Ψ : M.Domain}
    (hω : M.IsOmega ω) (hχ : M.IsRegularCardinal (kp_pair_l (ZF.modelsKP (ZFC.models_zf_l hZFC))) χ)
    (hωχ : M.mem ω χ) (hZ : H_d (kp_pair_l (ZF.modelsKP (ZFC.models_zf_l hZFC))) χ Z)
    (hΩ : M.IsOrdinal Ω) (hΩZ : M.mem Ω Z) (hoZ : M.mem o Z)
    (select : Wi_selector_tree_d (ZFC.models_zf_l hZFC) ω a A S o s₀ Z Ψ) :
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
    obtain ⟨H, run, _⟩ := wi_run_exists_tree_l hZFC hω hχ hωχ hZ (hΩ.mem hα) hαZ hoZ select ff
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

/-! 强树证书版的合法运行归纳。-/
namespace YesMetaZFC.SetTheory.LargeCardinal
open Definitional.Project InnerModel Internal
universe u
variable {M : Structure.{u}} (hZF : M.Models ZF)
local notation "I" => kp_pair_l (ZF.modelsKP hZF)
variable (hZFC : M.Models ZFC)
local notation "hZF'" => ZFC.models_zf_l hZFC
local notation "I'" => kp_pair_l (ZF.modelsKP hZF')

/-! 强树证书版的获胜对象。有限策略编码沿用旧接口，运行的每个回复
保留完整 `Wi_reply_tree_d` 证书。 -/
def Wi_winning_tree_d (hZ : M.Models ZF) (ω c Ω Z D Γ : M.Domain) : Prop :=
  ∃ a A S o s₀ Ψ α₀ T₀ Q₀ G₀ P₀,
    (∀ x, ¬ M.mem x o) ∧ M.SuccessorOf α₀ o ∧ Rd_quad_d s₀ T₀ Q₀ G₀ P₀ ∧
    Wi_state_d (kp_pair_l (ZF.modelsKP hZ)) ω α₀ T₀ Q₀ G₀ a A S P₀ ∧ Rd_entry_d o c Q₀ ∧
    Wi_strategy_d hZ o Ψ Ω Z D Γ ∧
    (∀ t d X R T Q G E L, Wi_tree_d t T Q G E L →
      It_nice_d hZ ω d ω T Q G E L → Smem_d (kp_pair_l (ZF.modelsKP hZ)) d X R →
      M.TransitiveSet X → M.CardinalLessOrEqual (kp_pair_l (ZF.modelsKP hZ)) X ω → M.mem t Z) ∧
    ∀ β, (β = Ω ∨ M.mem β Ω) → ∀ F, Fn0_d β Z F →
      ∃ R, Wi_run_d hZ o Ψ F β Z R ∧
        (∀ R', Wi_run_d hZ o Ψ F β Z R' → R' = R) ∧
        (Wi_legal_d hZ ω β F R →
          Wi_history_d hZ ω a A S β Z R ∧
          (∀ i s, Rd_entry_d i s R → Wi_reply_tree_d hZ ω a A S o s₀ Ψ F R i s) ∧
          ∀ α ξ F', M.mem α β → M.SuccessorOf α ξ →
            M.IsRestrictionOf (kp_pair_l (ZF.modelsKP hZ)) F' F α →
            ∃ B, Rd_entry_d F' B Γ ∧ Wi_play_tree_d hZ ω a A S F R α ξ B)

theorem Wi_winning_tree_d.to_winning_d {hZ : M.Models ZF}
    {ω c Ω Z D Γ : M.Domain} (h : Wi_winning_tree_d hZ ω c Ω Z D Γ) :
    Wi_winning_d hZ ω c Ω Z D Γ := by
  obtain ⟨a, A, S, o, s₀, Ψ, α₀, T₀, Q₀, G₀, P₀, ho, hα₀, pack₀, root, hc,
    strategy, nice, run⟩ := h
  refine ⟨a, A, S, o, s₀, Ψ, α₀, T₀, Q₀, G₀, P₀, ho, hα₀, pack₀, root, hc,
    strategy, nice, ?_⟩
  intro β within F moves
  obtain ⟨R, runR, unique, legal⟩ := run β within F moves
  refine ⟨R, runR, unique, ?_⟩
  intro hlegal
  obtain ⟨history, replies, plays⟩ := legal hlegal
  refine ⟨history, ?_, ?_⟩
  · intro i s hs
    exact (replies i s hs).to_reply_d
  · intro α ξ F' hα succ rf
    obtain ⟨B, hB, play⟩ := plays α ξ F' hα succ rf
    exact ⟨B, hB, play.to_play_d⟩

theorem wi_run_wins_tree_l {ω χ Z Ω a A S o s₀ Ψ F R θ α₀ T₀ Q₀ G₀ P₀ : M.Domain}
    (hω : M.IsOmega ω) (hχ : M.IsRegularCardinal I' χ) (hωχ : M.mem ω χ) (hZ : H_d I' χ Z)
    (hωZ : M.mem ω Z) (hA : M.mem A Z) (hΩ : M.IsOrdinal Ω)
    (count : ∀ i, M.mem i Ω → M.CardinalLessOrEqual I' i ω)
    (ho : ∀ x, ¬ M.mem x o) (hα₀ : M.SuccessorOf α₀ o) (pack₀ : Rd_quad_d s₀ T₀ Q₀ G₀ P₀)
    (root : Wi_state_d (kp_pair_l (ZF.modelsKP hZF')) ω α₀ T₀ Q₀ G₀ a A S P₀) (rank : V_d I' θ A) (ma : Smem_d I' a A S)
    (select : Wi_selector_tree_d hZF' ω a A S o s₀ Z Ψ) (run : Wi_run_d hZF' o Ψ F Ω Z R)
    (legal : Wi_legal_d hZF' ω Ω F R) :
    Wi_history_d hZF' ω a A S Ω Z R ∧ ∀ i s, Rd_entry_d i s R → Wi_reply_tree_d hZF' ω a A S o s₀ Ψ F R i s := by
  have answer {i H s} (hi : M.mem i Ω) (rh : M.IsRestrictionOf I' H R i)
      (hist : Wi_history_d hZF' ω a A S i Z H) (drive : Wi_drive_d o Ψ F H s) :
      Wi_reply_tree_d hZF' ω a A S o s₀ Ψ F R i s := by
    obtain ⟨α, t, r, u, B, dom, input, request, edge, pair⟩ := drive
    have seq := run.restriction hi rh
    have eq := Structure.IsDomainOf.eq (𝕀 := I') hZF'.1 dom seq.1.2.2.1
    subst α
    have available : ∃ C v, Wi_answer_tree_d hZF' ω a A S o s₀ i H t C v := by
      rcases (hΩ.mem hi).classify hZF'.1 with empty | ⟨ξ, hξ, succ⟩ | limit
      · have eq := hZF'.1.eq_of_same_members i o (fun x => iff_of_false (empty x) (ho x))
        subst i
        exact ⟨o, s₀, wi_answer_tree_root_l hZF' ho hα₀ pack₀ root hist⟩
      · have move : Rd_entry_d ξ t F := by
          rcases input with ⟨η, next, ht⟩ | ⟨no, _⟩
          · exact (Structure.SuccessorOf.predecessor_eq hZF'.1 hξ succ next).symm ▸ ht
          · exact (no ξ succ).elim
        obtain ⟨v, _, hv⟩ := hist.function.2.1 ξ succ.predecessor_mem
        obtain ⟨β, T, Q, G, P, hβ, pack, state⟩ := hist.rows ξ v hv
        have eq := Structure.SuccessorOf.eq hZF'.1 hβ succ
        subst β
        obtain ⟨c, hc⟩ := (state.diagram.model_domain ξ).mp succ.predecessor_mem
        obtain ⟨U, Q', G', E, L, pt, nice⟩ := legal ξ i v T Q G P c t hi succ ((rh.2 ξ v).mp hv).2 pack hc move
        exact wi_answer_tree_successor_l hZFC hist succ ⟨v, hv, pack⟩ hc pt nice rank ma
      · obtain ⟨v, hv⟩ := wi_answer_tree_limit_l hZFC hist limit (count i hi) ma (o := o) (s₀ := s₀) (t := t)
        exact ⟨o, v, hv⟩
    obtain ⟨C, v, av⟩ := available
    have next β (hb : M.SuccessorOf β i) : M.mem β Z := by
      have cn := ZF.countable_insert_l I' hZF' hω (count i hi) (fun x => (hb x).trans
        (or_congr Iff.rfl ⟨hZF'.1.eq_of_same_members x i, fun eq => eq ▸ fun _ => Iff.rfl⟩))
      exact (hZ β).mpr (ZF.hmem_of_subset_l I' hZF' hχ.isLimitOrdinal
        (KP.successor_isOrdinal (ZF.modelsKP hZF') (hΩ.mem hi) hb).transitive (fun _ h => h) hωχ cn)
    have av_old := av.to_answer_d
    obtain ⟨hC, hv⟩ := av_old.mem_l hZFC hω hχ hωχ hZ hωZ hA ho next
    obtain ⟨w, pw⟩ := (I').total C v
    have hw := ZFC.h_kpair_l hZFC hω hχ hωχ hZ pw hC hv
    exact ⟨H, t, r, u, B, rh, input, request, edge, pair,
      select.answer_l hZF' request pair edge ⟨w, hw, i, H, t, C, v, request, pw, av⟩⟩
  -- 归纳谓词是原一阶历史公式；合法 nice 条件只作为归纳步的已知事实使用。
  let η : Env M 6 := (((((⟨fun _ => ω, fun _ => ω⟩ : Env M 1).push a).push A).push S).push Z).push R
  let φ : UnarySchema 6 := { body := .forallE (.imp
    (Formula.isRestriction kpair_convention_l .newest (.bound 2) (.bound 1))
    (wi_history_m (.bound 7) (.bound 6) (.bound 5) (.bound 4) (.bound 1) (.bound 3) .newest)) }
  have sat α : φ.denote η α ↔ ∀ H, M.IsRestrictionOf I' H R α → Wi_history_d hZF' ω a A S α Z H := by
    simp only [φ, UnarySchema.denote, Formula.satisfies_forall_iff, Formula.satisfies_imp_iff,
      Formula.satisfies_isRestriction_iff I', wi_history_sat_l hZF']; rfl
  have all : φ.denote η Ω := by
    apply hΩ.inductionWithin (fun α => φ.denote η α)
    · obtain ⟨C, hc⟩ := ZF.separation_exists_d hZF' φ.neg η Ω
      exact ⟨C, fun i => (hc i).trans (and_congr_right fun _ => Formula.satisfies_neg_iff ..)⟩
    · intro α hα within ih
      apply (sat α).mpr
      intro H rh
      have sub : M.MemberSubset α Ω := within.elim (fun eq _ hi => eq ▸ hi) (fun hi => hΩ.transitive α hi)
      have get i s (hs : Rd_entry_d i s H) : Wi_reply_tree_d hZF' ω a A S o s₀ Ψ F R i s := by
        have read := (rh.2 i s).mp hs
        obtain ⟨J, rj, drive⟩ := run.2 i (sub i read.1) s read.2
        exact answer (sub i read.1) rj ((sat i).mp (ih i read.1) J rj) drive
      refine ⟨fn0_of_function_l (ZF.modelsKP hZF') (rh.isSetFunctionFromTo run.1.2 sub), ?_, ?_⟩
      · intro i s hs
        obtain ⟨_, _, _, _, _, _, _, _, _, _, β, T, Q, G, P, hβ, pack, state, _⟩ := get i s hs
        exact ⟨β, T, Q, G, P, hβ, pack, state⟩
      · intro i j T Q G P U Q' G' P' hij ⟨s, hs, ps⟩ ⟨t, ht, pt⟩
        obtain ⟨J, _, _, _, _, rj, _, _, _, _, _, V, Q'', G'', P'', _, pack, _, past, _⟩ := get j t ht
        obtain ⟨eqT, eqQ, eqG, eqP⟩ := pack.unique_l pt
        subst V Q'' G'' P''
        exact past i T Q G P ⟨s, (rj.2 i s).mpr ⟨hij, ((rh.2 i s).mp hs).2⟩, ps⟩
  have self : M.IsRestrictionOf I' R R Ω := ⟨run.1.2.1.1,
    fun i s => ⟨fun hs => ⟨run.1.2.input_mem_of_pairMember hs, hs⟩, And.right⟩⟩
  have history := (sat Ω).mp all R self
  refine ⟨history, fun i s hs => ?_⟩
  have hi := run.1.2.input_mem_of_pairMember hs
  obtain ⟨H, rh, drive⟩ := run.2 i hi s hs
  exact answer hi rh (history.restrict_l hZF' (hΩ.transitive i hi) rh) drive

end YesMetaZFC.SetTheory.LargeCardinal

/-! 强树证书版的 nice 弱可迭代性。-/
namespace YesMetaZFC.SetTheory.LargeCardinal
open Definitional.Project InnerModel Internal
universe u
variable {M : Structure.{u}}

variable (hZFC : M.Models ZFC)
local notation "hZF" => ZFC.models_zf_l hZFC
local notation "I" => kp_pair_l (ZF.modelsKP hZF)

theorem it_nice_weakly_iterable_tree_l {ω c X R K θ a A S π : M.Domain}
    (source : Ep_source_d I ω ω K X R) (mx : Smem_d I c X R) (count : M.CardinalLessOrEqual I X ω)
    (rank : V_d I θ A) (ma : Smem_d I a A S) (embed : Smap_d I ω c a X A π) :
    ∃ Ω Z D Γ, M.IsHartogsNumber I Ω ω ∧ Wi_winning_tree_d hZF ω c Ω Z D Γ := by
  have hω := source.omega
  obtain ⟨o, α₀, T₀, Q₀, G₀, P₀, ho, hα₀, root, hc, _⟩ := wi_root_l hZF source mx count ma embed
  obtain ⟨s₀, pack₀⟩ := rd_quad_exists_l (ZF.modelsKP hZF) T₀ Q₀ G₀ P₀
  obtain ⟨Ω, hΩ⟩ := ZF.exists_hartogsNumber hZF I ω
  obtain ⟨p, pp⟩ := rd_quad_exists_l (ZF.modelsKP hZF) s₀ A Ω ω
  obtain ⟨χ, Z, hχ, hωχ, hZ, hp⟩ := ZFC.h_cover_l I hZFC hω p
  have zt := ZF.h_transitive_l I hZF hZ
  obtain ⟨hs₀, hA, hΩZ, hωZ⟩ := pp.mem_l zt hp
  obtain ⟨z, hz, hzω⟩ := hω.1.1
  have eq := hZF.1.eq_of_same_members z o (fun x => iff_of_false (hz x) (ho x))
  have hoZ := zt ω hωZ o (eq ▸ hzω)
  obtain ⟨u₀, pair⟩ := (I).total o s₀
  obtain ⟨Ψ, select⟩ := wi_selector_tree_exists_l hZFC (ZFC.h_kpair_l hZFC hω hχ hωχ hZ pair hoZ hs₀) pair
    (ω := ω) (a := a) (A := A) (S := S)
  obtain ⟨D, Γ, strategy⟩ := wi_strategy_tree_exists_l hZFC hω hχ hωχ hZ hΩ.1 hΩZ hoZ select
  refine ⟨Ω, Z, D, Γ, hΩ, a, A, S, o, s₀, Ψ, α₀, T₀, Q₀, G₀, P₀,
    ho, hα₀, pack₀, root, hc, strategy, ?_, ?_⟩
  · intro t d Y W T Q G E L pack nice my yt cy
    exact pack.mem_l hZFC hω hχ hωχ hZ hωZ nice my cy
  · intro β within F moves
    have hb : M.IsOrdinal β := within.elim (fun eq => eq.symm ▸ hΩ.1) hΩ.1.mem
    have hbZ : M.mem β Z := within.elim (fun eq => eq.symm ▸ hΩZ) (zt Ω hΩZ β)
    have sub : M.MemberSubset β Ω := within.elim (fun eq _ hi => eq ▸ hi) (fun hi => hΩ.1.transitive β hi)
    obtain ⟨H, run, unique⟩ := wi_run_exists_tree_l hZFC hω hχ hωχ hZ hb hbZ hoZ select moves
    refine ⟨H, run, unique, fun legal => ?_⟩
    obtain ⟨history, replies⟩ := wi_run_wins_tree_l hZFC hω hχ hωχ hZ hωZ hA hb
      (fun i hi => (hΩ.2 i (hΩ.1.mem (sub i hi))).mp (sub i hi)) ho hα₀ pack₀ root rank ma select run legal
    refine ⟨history, replies, fun α ξ F' hα succ rf => ?_⟩
    have fn := fn0_of_function_l (ZF.modelsKP hZF)
      (rf.isSetFunctionFromTo (fn0_function_l (ZF.modelsKP hZF) moves) (hb.transitive α hα))
    obtain ⟨B, _, chosen⟩ := strategy.2.1.2.1 F' ((strategy.1 F').mpr ⟨α, ξ, sub α hα, succ, fn⟩)
    exact ⟨B, chosen, strategy.play_tree_l hZF (fn0_function_l (ZF.modelsKP hZF) select.function).1 ho moves run replies hα succ rf chosen⟩


end YesMetaZFC.SetTheory.LargeCardinal
