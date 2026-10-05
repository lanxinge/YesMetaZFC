import YesMetaZFC.SetTheory.LargeCardinal.ExtenderFiniteEvaluation
import YesMetaZFC.SetTheory.LargeCardinal.ExtenderTreeBranch
import YesMetaZFC.Model.SetTheory.Internal.EmbeddingAttemptRelative

/-! # 源中实际存在的完整初等嵌入尝试树

有限程序、有限赋值空间和双边真值表均由源的已证闭性给出。
先证明节点公式绝对，再用相对分离构造树；外部嵌入提供枝，树枝绝对性
返回源中真实存在的总图。
-/
namespace YesMetaZFC.SetTheory.LargeCardinal
open Definitional.Project InnerModel Internal Descriptive
universe u
variable {M : Structure.{u}} (hZF : M.Models ZF)
local notation "I" => kp_pair_l (ZF.modelsKP hZF)

theorem Ep_source_d.at_elementary_l {ω κ V Z W A R B S e n p Q J K : M.Domain}
    (source : Ep_source_d hZF ω κ V Z W) (hA : M.mem A Z) (hR : M.mem R Z)
    (hB : M.mem B Z) (hS : M.mem S Z) (hn : M.mem n ω)
    (hQ : Fseq_space_d I ω ω Q) (hJ : Fseq_space_d I ω A J) (hK : Fseq_space_d I ω B K) :
    At_relative_d (ZF.modelsKP hZF) Z ω A R B S e n p Q J K ↔ At_elementary_d I ω A R B S e n p := by
  constructor
  · intro h b l F E D q s t hb hF bound hE hD hq hs ht r hr
    obtain ⟨hFZ, _, L, hLZ, program⟩ := source.program_l hZF hF
    have prog := fb_program_of_l (ZF.modelsKP hZF) hF hb bound program.2.2.1
    obtain ⟨E', D', C, H, C', H', _, _, _, _, _, _, hE', hD', ev, ev', test⟩ :=
      h b l L F (source.transitive ω source.omega_mem b hb)
        (source.transitive ω source.omega_mem l hF.1) hLZ hFZ prog
    have space := (fv_space_l (ZF.modelsKP hZF) hb hJ).mp hE'
    have space' := (fv_space_l (ZF.modelsKP hZF) hb hK).mp hD'
    have eqE := hZF.1.eq_of_same_members E' E (fun f => (space f).trans (hE f).symm)
    have eqD := hZF.1.eq_of_same_members D' D (fun f => (space' f).trans (hD f).symm)
    subst E'; subst D'
    exact (ev.truth_l hZF source.omega prog hE hr).symm.trans
      ((test r hr q ((hQ q).mpr ⟨b, hb, fn0_function_l (ZF.modelsKP hZF)
        (hq.mono_target_l (source.omega.transitive hZF n hn))⟩)
        s ((hE s).mpr (fn0_function_l (ZF.modelsKP hZF) hs.1))
        t ((hD t).mpr (fn0_function_l (ZF.modelsKP hZF) ht.1)) hq hs ht).trans
          (ev'.truth_l hZF source.omega prog hD hr))
  · intro h b l L F _ _ _ _ program
    obtain ⟨E, hEZ, hE⟩ := source.finite_space_l hZF hA program.1
    obtain ⟨D, hDZ, hD⟩ := source.finite_space_l hZF hB program.1
    obtain ⟨C, H, hCZ, hHZ, ev⟩ := source.finite_evaluation_l hZF hA hR hEZ program hE
    obtain ⟨C', H', hC'Z, hH'Z, ev'⟩ := source.finite_evaluation_l hZF hB hS hDZ program hD
    obtain ⟨hF, bound⟩ := program.read_l hZF source.omega
    refine ⟨E, D, C, H, C', H', hEZ, hDZ, hCZ, hHZ, hC'Z, hH'Z,
      (fv_space_l (ZF.modelsKP hZF) program.1 hJ).mpr hE,
      (fv_space_l (ZF.modelsKP hZF) program.1 hK).mpr hD, ev, ev', fun r hr q _ s _ t _ hq hs ht => ?_⟩
    exact (ev.truth_l hZF source.omega program hE hr).trans
      ((h b l F E D q s t program.1 hF bound hE hD hq hs ht r hr).trans
        (ev'.truth_l hZF source.omega program hD hr).symm)

theorem Ep_source_d.at_tree_l {ω κ V Z W A R B S e τ : M.Domain}
    (source : Ep_source_d hZF ω κ V Z W) (hA : M.mem A Z) (hR : M.mem R Z)
    (hB : M.mem B Z) (hS : M.mem S Z) (he : M.mem e Z) (hτ : M.mem τ Z) :
    ∃ K T, M.mem K Z ∧ M.mem T Z ∧ Fseq_space_d I ω B K ∧ Tree_d K T ∧
      ∀ p, M.mem p T ↔ ∃ n, At_node_d I ω A R B S e τ n p := by
  obtain ⟨Q, hQZ, hQ⟩ := source.sequences.space ω source.omega_mem
  obtain ⟨J, hJZ, hJ⟩ := source.sequences.space A hA
  obtain ⟨K, hKZ, hK⟩ := source.sequences.space B hB
  obtain ⟨c, hc⟩ := source.code
  let hz : Nonempty {x : M.Domain // M.mem x Z} := ⟨⟨ω, source.omega_mem⟩⟩
  let ρ : Env (rt_model_l Z hz) 10 := ⟨Fin.cases ⟨ω, source.omega_mem⟩ (Fin.cases ⟨A, hA⟩
    (Fin.cases ⟨R, hR⟩ (Fin.cases ⟨B, hB⟩ (Fin.cases ⟨S, hS⟩ (Fin.cases ⟨e, he⟩
      (Fin.cases ⟨τ, hτ⟩ (Fin.cases ⟨Q, hQZ⟩ (Fin.cases ⟨J, hJZ⟩ (fun _ => ⟨K, hKZ⟩))))))))),
    fun _ => ⟨ω, source.omega_mem⟩⟩
  let φ : UnarySchema 10 := {
    body := at_node_m (.bound 1) (.bound 2) (.bound 3) (.bound 4)
      (.bound 5) (.bound 6) (.bound 7) .newest (.bound 8) (.bound 9) (.bound 10) }
  have read (p : (rt_model_l Z hz).Domain) : φ.denote ρ p ↔ ∃ n, At_node_d I ω A R B S e τ n p.val := by
    apply (at_node_relative_l (ZF.modelsKP hZF) source.transitive hz (ρ.push p)
      (.bound 1) (.bound 2) (.bound 3) (.bound 4) (.bound 5) (.bound 6) (.bound 7) .newest (.bound 8) (.bound 9) (.bound 10)).trans
    exact exists_congr fun n => ⟨fun ⟨hn, hf, coh, pre, el⟩ => ⟨hn, hf, coh, pre,
      (source.at_elementary_l hZF hA hR hB hS hn hQ hJ hK).mp el⟩,
      fun h => ⟨h.length, h.function, h.coherent, h.prescribed,
        (source.at_elementary_l hZF hA hR hB hS h.length hQ hJ hK).mpr h.elementary⟩⟩
  obtain ⟨T, hTZ, sub, spec⟩ := sc_separate_relative_l I hZF source.omega hc source.theory hz φ ρ hKZ
  have nodes p : M.mem p T ↔ ∃ n, At_node_d I ω A R B S e τ n p := by
    constructor
    · intro hp
      exact (read ⟨p, source.transitive T hTZ p hp⟩).mp ((spec ⟨p, source.transitive T hTZ p hp⟩).mp hp).2
    · rintro ⟨n, h⟩
      have hp := (hK p).mpr ⟨n, h.length, fn0_function_l (ZF.modelsKP hZF) h.function⟩
      exact (spec ⟨p, source.transitive K hKZ p hp⟩).mpr ⟨hp, (read _).mpr ⟨n, h⟩⟩
  refine ⟨K, T, hKZ, hTZ, hK, ⟨sub, fun p hp s hs hsp => ?_⟩, nodes⟩
  obtain ⟨n, hn⟩ := (nodes p).mp hp
  obtain ⟨m, hm, hf⟩ := (hK s).mp hs
  exact (nodes s).mpr ⟨m, hn.prefix_l hZF hm (fn0_of_function_l (ZF.modelsKP hZF) hf) hsp⟩

/-- 完整初等嵌入给出外部枝，再取得源内枝的每个合法有限尝试。 -/
theorem Ep_source_d.at_branch_l {ω κ V Z W c d A R B S e τ j : M.Domain}
    (source : Ep_source_d hZF ω κ V Z W) (branches : Sc_branch_d ω Z) (hA : M.mem A Z) (hR : M.mem R Z)
    (hB : M.mem B Z) (hS : M.mem S Z) (heZ : M.mem e Z) (hτ : M.mem τ Z)
    (hm : Smdl_d I c A R) (hn : Smdl_d I d B S) (hj : Smap_d I ω c d A B j)
    (he : Fn0_d ω A e) (hτj : ∀ x y, Rd_entry_d x y τ → Rd_entry_d x y j) :
    ∃ g, M.mem g Z ∧ Fn0_d ω B g ∧ ∀ n, M.mem n ω →
      ∃ p, At_node_d I ω A R B S e τ n p ∧ M.IsRestrictionOf I p g n := by
  obtain ⟨K, T, _, hTZ, hK, tree, nodes⟩ := source.at_tree_l hZF hA hR hB hS heZ hτ
  obtain ⟨g, hg⟩ := cp0_exists_l (ZF.modelsKP hZF) he (fn0_of_function_l (ZF.modelsKP hZF) hj.1.1)
  have gf := fn0_function_l (ZF.modelsKP hZF) hg.1
  have branch : Branch_d K T g := (Descriptive.tree_branch_l I hZF source.omega hK gf).mpr (by
    intro n hnat
    obtain ⟨p, hp, res, _⟩ := ds_prefix_l I hZF source.omega gf hnat
    have cp : Cp0_d n A B e j p := ⟨fn0_of_function_l (ZF.modelsKP hZF) hp, fun i hi => by
      obtain ⟨x, hx, y, hy, hix, hxy, hiy⟩ := hg.2 i (source.omega.transitive hZF n hnat i hi)
      exact ⟨x, hx, y, hy, hix, hxy, (res.2 i y).mpr ⟨hi, hiy⟩⟩⟩
    exact ⟨p, (nodes p).mpr ⟨n, at_node_of_l hZF source.omega hm hn hj he hτj hnat cp⟩, res⟩)
  obtain ⟨g', hgZ, hgf, hb⟩ := source.tree_branch_l hZF branches hB hTZ hK tree gf branch
  refine ⟨g', hgZ, fn0_of_function_l (ZF.modelsKP hZF) hgf, fun n hnat => ?_⟩
  obtain ⟨p, hp, res⟩ := (Descriptive.tree_branch_l I hZF source.omega hK hgf).mp hb n hnat
  obtain ⟨m, node⟩ := (nodes p).mp hp
  have fn := res.isSetFunctionFromTo hgf (source.omega.transitive hZF n hnat)
  have eq := (fn0_function_l (ZF.modelsKP hZF) node.function).2.1.eq hZF.1 fn.2.1
  exact ⟨p, eq ▸ node, res⟩

end YesMetaZFC.SetTheory.LargeCardinal
