import YesMetaZFC.SetTheory.Descriptive.Borel.NodeSets
import YesMetaZFC.SetTheory.Collapse.RelationGap

/-! # 从任意内部 Borel 码导出可数的标准层级界

难点是并节点：先在较低的上界形成 Σ 集，再升一层进入 Δ。
双层秩为此提供严格间隙，整树的节点解释函数提供实际可数族；全程只用 ZF。
-/
namespace YesMetaZFC.SetTheory.Descriptive
open Definitional.Project InnerModel
universe u
variable {M : Structure.{u}} {𝒞 : OrderedPairConvention} (I : 𝒞.Interpretation M)

theorem bcode_level_l (hZF : M.Models ZF) {ω X A S B c K} (hω : M.IsOmega ω)
    (hB : M.IsFunctionSpace I B ω X) (hS : Fseq_space_d I ω X S)
    (hc : M.CardinalLessOrEqual I A ω) (hcode : Bcode_d I ω A S c) (hden : Bden_d I ω A S B c K) :
    ∃ α, M.IsOrdinal α ∧ M.CardinalLessOrEqual I α ω ∧ Bsig_d I ω S B α K ∧ Bpi_d I ω S B α K := by
  classical
  obtain ⟨T, R, N, F, pack, ht⟩ := hcode
  obtain ⟨E, he⟩ := hc
  obtain ⟨D, hd⟩ := ZF.exists_inclusionInjection hZF I ht.tree.1
  have count := ZF.exists_compositionInjection hZF I hd he
  obtain ⟨κ, L, H, hk, hkω, hl, hh, gap⟩ := wr_gap_l I hZF hω ht.wf count
  obtain ⟨P, G, hp, hg, eg⟩ := bn_graph_l I hZF B T R N F
  let ρ : Env M 5 := ((((⟨fun _ => ω, fun _ => ω⟩ : Env M 1).push S).push B).push H).push G
  let φ : UnarySchema 5 := { body := .forallE (.forallE (.imp
    (Formula.orderedPairMem 𝒞 (.bound 2) (.bound 1) (.bound 4)) (.imp
    (Formula.orderedPairMem 𝒞 (.bound 2) .newest (.bound 3)) (.conj
    (bsig_m (𝒞 := 𝒞) (.bound 7) (.bound 6) (.bound 5) (.bound 1) .newest)
    (bpi_m (𝒞 := 𝒞) (.bound 7) (.bound 6) (.bound 5) (.bound 1) .newest))))) }
  have ep a : φ.denote ρ a ↔ ∀ α C, M.PairMember I a α H → M.PairMember I a C G →
      Bsig_d I ω S B α C ∧ Bpi_d I ω S B α C := by
    simp only [φ, UnarySchema.denote, Formula.satisfies_forall_iff, Formula.satisfies_imp_iff,
      Formula.satisfies_orderedPairMem_iff I, Formula.satisfies_conj_iff, bsig_sat_l I hZF.1, bpi_sat_l I hZF.1]; rfl
  have all := wf_rel_ind_l hZF ht.wf φ ρ (fun a ha ih => (ep a).mpr (by
    intro α C haα haC
    have hα := hk.mem (hh.output_mem_of_pairMember haα)
    obtain ⟨δ, hδκ, haδ⟩ := hl.2.2 a ha
    obtain ⟨hδα, below⟩ := gap a δ α haδ haα
    have hδ := hk.mem hδκ
    have hC := eg a C haC
    -- 叶解释为开闭柱集，在任意正层同时属于 Σ 与 Π。
    by_cases leaf : ∃ s, M.PairMember I a s F
    · obtain ⟨s, hs⟩ := leaf
      have cyl := bn_leaf_l I hZF ht hs hC
      obtain ⟨ho, hc⟩ := ds_cyl_clopen_l I hZF hω hB hS (ht.leaf a s hs).2.1 cyl
      exact ⟨bsig_open_l I hZF hα ⟨δ, hδα⟩ ho,
        bpi_closed_l I hZF hα ⟨δ, hδα⟩ ⟨ho.1, hc⟩⟩
    · by_cases neg : M.mem a N
      -- 补节点交换两种极性，再沿序数包含升层。
      · obtain ⟨b, hb, hba, unique⟩ := ht.neg a neg
        obtain ⟨γ, _, hbγ⟩ := hh.2.2 b hb
        obtain ⟨V, hvP, hbV⟩ := hg.2.2 b hb
        obtain ⟨sig, pi⟩ := (ep b).mp (ih b hb hba) γ V hbγ hbV
        have cm := bn_neg_l I hZF ht neg hb hba unique hC (eg b V hbV)
        have sub := (hp V).mp hvP
        have hγα := hα.transitive δ hδα γ (below b γ hb hba hbγ)
        exact ⟨bsig_mono_l I hZF hα (hα.transitive.memberSubset hγα) ((bsig_compl_l I hZF.1 sub cm).mpr pi),
          bpi_mono_l I hZF hα (hα.transitive.memberSubset hγα) ((bpi_compl_l I hZF.1 sub cm).mpr sig)⟩
      · obtain ⟨U, hu, eu⟩ := bn_union_family_l I hZF ht count hg eg ha neg leaf hC
        -- 子秩严格低于 δ，故并先落入 Σ⁰δ；δ < α 再给出 Π⁰α。
        by_cases ne : ∃ β, M.mem β δ
        · have low : Bsig_d I ω S B δ C := bsig_union_l I hZF hδ ne hu (by
            intro i V hi
            obtain ⟨b, hb, hba, hbV⟩ := eu i V hi
            obtain ⟨γ, _, hbγ⟩ := hh.2.2 b hb
            exact ⟨γ, below b γ hb hba hbγ, ((ep b).mp (ih b hb hba) γ V hbγ hbV).2⟩)
          exact ⟨bsig_mono_l I hZF hα (hα.transitive.memberSubset hδα) low,
            bsig_bpi_l I hZF (hω.1.1.elim fun z h => ⟨z, h.2⟩) hα hδα low⟩
        · have empty : ∀ x, ¬ M.mem x C := by
            intro x hx
            obtain ⟨i, V, hi, _⟩ := (hu.2.2 x).mp hx
            obtain ⟨b, hb, hba, _⟩ := eu i V hi
            obtain ⟨γ, _, hbγ⟩ := hh.2.2 b hb
            exact ne ⟨γ, below b γ hb hba hbγ⟩
          exact ⟨bsig_open_l I hZF hα ⟨δ, hδα⟩ (ds_open_empty_l empty),
            bpi_closed_l I hZF hα ⟨δ, hδα⟩ ⟨fun x hx => (empty x hx).elim, B,
              fun x => ⟨fun hx => ⟨hx, empty x⟩, And.left⟩, ds_open_whole_l I hZF hω hB hS⟩⟩))
  obtain ⟨z, hz, hzT⟩ := ht.root
  obtain ⟨α, hακ, hza⟩ := hh.2.2 z hzT
  obtain ⟨C, _, hzC⟩ := hg.2.2 z hzT
  have eqK : C = K := by
    apply hZF.1.eq_of_same_members C K
    intro x
    obtain ⟨V, hv, _⟩ := bsem_exists_unique_l I hZF ht.wf N F x
    exact (bn_mem_l I hZF ht.wf (eg z C hzC) hv).trans
      ((and_congr_right fun _ => (bsat_root_l I hZF pack ht hv hz).symm).trans (hden x).symm)
  obtain ⟨J, hj⟩ := ZF.exists_inclusionInjection hZF I (hk.transitive.memberSubset hακ)
  obtain ⟨Q, hq⟩ := hkω
  exact ⟨α, hk.mem hακ, ZF.exists_compositionInjection hZF I hj hq, eqK ▸ (ep z).mp (all z hzT) α C hza hzC⟩

end YesMetaZFC.SetTheory.Descriptive
