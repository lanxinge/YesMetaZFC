import YesMetaZFC.SetTheory.LargeCardinal.IterationWeakRun

/-! # 合法弱迭代对局的每一步都有实际应答

合法性只要求对手在当前模型上给出 nice ω 树。对历史正确性的原公式做超限归纳，
逐步证明所选应答真实存在，因而备用值永远不会造成一次合法对局的失败。
-/
namespace YesMetaZFC.SetTheory.LargeCardinal
open Definitional.Project InnerModel Internal
universe u
variable {M : Structure.{u}} (hZF : M.Models ZF)
local notation "I" => kp_pair_l (ZF.modelsKP hZF)

def Wi_legal_d (ω Ω F R : M.Domain) : Prop := ∀ i j s T Q G P c t,
  M.mem j Ω → M.SuccessorOf j i → Rd_entry_d i s R → Rd_quad_d s T Q G P → Rd_entry_d i c Q → Rd_entry_d i t F →
    ∃ U Q' G' E L, Wi_tree_d t U Q' G' E L ∧ It_nice_d hZF ω c ω U Q' G' E L

def Wi_reply_d (ω a A S o s₀ Ψ F R i s : M.Domain) : Prop := ∃ H t r u B,
  M.IsRestrictionOf I H R i ∧ Wi_input_d o F i t ∧ Rd_triple_d r i H t ∧ Rd_entry_d r u Ψ ∧
    KPair_d M u B s ∧ Wi_answer_d hZF ω a A S o s₀ i H t B s

variable (hZFC : M.Models ZFC)
local notation "hZF'" => ZFC.models_zf_l hZFC
local notation "I'" => kp_pair_l (ZF.modelsKP hZF')

theorem wi_run_wins_l {ω χ Z Ω a A S o s₀ Ψ F R θ α₀ T₀ Q₀ G₀ P₀ : M.Domain}
    (hω : M.IsOmega ω) (hχ : M.IsRegularCardinal I' χ) (hωχ : M.mem ω χ) (hZ : H_d I' χ Z)
    (hωZ : M.mem ω Z) (hA : M.mem A Z) (hΩ : M.IsOrdinal Ω)
    (count : ∀ i, M.mem i Ω → M.CardinalLessOrEqual I' i ω)
    (ho : ∀ x, ¬ M.mem x o) (hα₀ : M.SuccessorOf α₀ o) (pack₀ : Rd_quad_d s₀ T₀ Q₀ G₀ P₀)
    (root : Wi_state_d hZF' ω α₀ T₀ Q₀ G₀ a A S P₀) (rank : V_d I' θ A) (ma : Smem_d I' a A S)
    (select : Wi_selector_d hZF' ω a A S o s₀ Z Ψ) (run : Wi_run_d hZF' o Ψ F Ω Z R)
    (legal : Wi_legal_d hZF' ω Ω F R) :
    Wi_history_d hZF' ω a A S Ω Z R ∧ ∀ i s, Rd_entry_d i s R → Wi_reply_d hZF' ω a A S o s₀ Ψ F R i s := by
  have answer {i H s} (hi : M.mem i Ω) (rh : M.IsRestrictionOf I' H R i)
      (hist : Wi_history_d hZF' ω a A S i Z H) (drive : Wi_drive_d o Ψ F H s) :
      Wi_reply_d hZF' ω a A S o s₀ Ψ F R i s := by
    obtain ⟨α, t, r, u, B, dom, input, request, edge, pair⟩ := drive
    have seq := run.restriction hi rh
    have eq := Structure.IsDomainOf.eq (𝕀 := I') hZF'.1 dom seq.1.2.2.1
    subst α
    have available : ∃ C v, Wi_answer_d hZF' ω a A S o s₀ i H t C v := by
      rcases (hΩ.mem hi).classify hZF'.1 with empty | ⟨ξ, hξ, succ⟩ | limit
      · have eq := hZF'.1.eq_of_same_members i o (fun x => iff_of_false (empty x) (ho x))
        subst i
        exact ⟨o, s₀, wi_answer_root_l hZF' ho hα₀ pack₀ root hist⟩
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
        exact wi_answer_successor_l hZFC hist succ ⟨v, hv, pack⟩ hc pt nice rank ma
      · obtain ⟨v, hv⟩ := wi_answer_limit_l hZFC hist limit (count i hi) ma (o := o) (s₀ := s₀) (t := t)
        exact ⟨o, v, hv⟩
    obtain ⟨C, v, av⟩ := available
    have next β (hb : M.SuccessorOf β i) : M.mem β Z := by
      have cn := ZF.countable_insert_l I' hZF' hω (count i hi) (fun x => (hb x).trans
        (or_congr Iff.rfl ⟨hZF'.1.eq_of_same_members x i, fun eq => eq ▸ fun _ => Iff.rfl⟩))
      exact (hZ β).mpr (ZF.hmem_of_subset_l I' hZF' hχ.isLimitOrdinal
        (KP.successor_isOrdinal (ZF.modelsKP hZF') (hΩ.mem hi) hb).transitive (fun _ h => h) hωχ cn)
    obtain ⟨hC, hv⟩ := av.mem_l hZFC hω hχ hωχ hZ hωZ hA ho next
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
      have get i s (hs : Rd_entry_d i s H) : Wi_reply_d hZF' ω a A S o s₀ Ψ F R i s := by
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
