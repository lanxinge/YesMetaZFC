import YesMetaZFC.Model.SetTheory.Internal.SourceHierarchy
import YesMetaZFC.Model.SetTheory.Internal.SmallSkolemSyntax
import YesMetaZFC.SetTheory.CumulativeRelativeRestriction

/-! # 不可达支撑以下的实际小秩层枚举

整层用支撑枚举，每个严格较早层用支撑以下的序数枚举。见证均属于原源，
全称存在句子的初等传输覆盖新序数；严格秩截断保留同一层和同一枚举图。
-/
namespace YesMetaZFC.SetTheory.Internal
open Definitional.Project InnerModel
universe u
variable {M : Structure.{u}}

structure Sc_rank_size_d (I : kpair_convention_l.Interpretation M) (X L : M.Domain) : Prop where
  level : ∃ W f, M.mem W X ∧ Vr_d X L W ∧ M.mem f X ∧ M.IsSetBijectionFromTo I f L W
  lower : ∀ α, M.mem α L → ∃ W μ f,
    M.mem W X ∧ Vr_d X α W ∧ M.mem μ L ∧ M.mem f X ∧ M.IsSetBijectionFromTo I f μ W

def sc_rank_size_m {d} (L : Term d) : Formula 1 d := .conj
  (.existsE (.existsE (.conj (v_sigma_m L.weaken.weaken (.bound 1))
    (sh_bijection_m .newest L.weaken.weaken (.bound 1)))))
  (Formula.forallMem L (.existsE (Formula.existsMem L.weaken.weaken (.existsE
    (.conj (v_sigma_m (.bound 3) (.bound 2)) (sh_bijection_m .newest (.bound 1) (.bound 2)))))))
derive_free_closed sc_rank_size_m

theorem sc_rank_size_sat_l (hKP : M.Models KP) {X : M.Domain} (hX : M.TransitiveSet X)
    (nx : Nonempty {x // M.mem x X}) {d} (ρ : Env (rt_model_l X nx) d) (L : Term d) :
    Formula.satisfies ρ (sc_rank_size_m L) ↔ Sc_rank_size_d (kp_pair_l hKP) X (L.eval ρ).val := by
  have bij {n} (η : Env (rt_model_l X nx) n) (f A B : Term n) :
      Formula.satisfies η (sh_bijection_m f A B) ↔
        M.IsSetBijectionFromTo (kp_pair_l hKP) (f.eval η).val (A.eval η).val (B.eval η).val := by
    simpa only [eval_image_env_l (M := rt_model_l X nx) (N := M) Subtype.val] using
      (rt_model_delta_l hX nx (sh_bijection_delta_l ..) η).trans (sh_bijection_sat_l hKP ..)
  simp only [sc_rank_size_m, Formula.satisfies_conj_iff, Formula.satisfies_exists_iff,
    Formula.satisfies_forallMem_iff, Formula.satisfies_existsMem_iff,
    vr_sat_l hKP hX nx, bij, Definitional.Term.eval_weaken]
  constructor
  · rintro ⟨⟨W, f, rank, bf⟩, lower⟩
    refine ⟨⟨W.val, f.val, W.property, rank, f.property, bf⟩, fun α hα => ?_⟩
    obtain ⟨W, μ, hμ, f, rank, bf⟩ := lower ⟨α, hX (L.eval ρ).val (L.eval ρ).property α hα⟩ hα
    exact ⟨W.val, μ.val, f.val, W.property, rank, hμ, f.property, bf⟩
  · intro h
    obtain ⟨W, f, hW, rank, hf, bf⟩ := h.level
    refine ⟨⟨⟨W, hW⟩, ⟨f, hf⟩, rank, bf⟩, fun α hα => ?_⟩
    obtain ⟨W, μ, f, hW, rank, hμ, hf, bf⟩ := h.lower α.val hα
    exact ⟨⟨W, hW⟩, ⟨μ, hX (L.eval ρ).val (L.eval ρ).property μ hμ⟩, hμ, ⟨f, hf⟩, rank, bf⟩

theorem Smap_d.rank_size_l (hZF : M.Models ZF) {ω c d X R Y S j L L' : M.Domain}
    (hω : M.IsOmega ω) (hX : M.TransitiveSet X) (hY : M.TransitiveSet Y)
    (hm : Smem_d (kp_pair_l (ZF.modelsKP hZF)) c X R) (hn : Smem_d (kp_pair_l (ZF.modelsKP hZF)) d Y S)
    (hj : Smap_d (kp_pair_l (ZF.modelsKP hZF)) ω c d X Y j) (hL : Rd_entry_d L L' j) :
    Sc_rank_size_d (kp_pair_l (ZF.modelsKP hZF)) X L ↔ Sc_rank_size_d (kp_pair_l (ZF.modelsKP hZF)) Y L' := by
  let nx : Nonempty {x // M.mem x X} := ⟨⟨L, hj.1.1.input_mem_of_pairMember hL⟩⟩
  let ny : Nonempty {x // M.mem x Y} := ⟨⟨L', hj.1.1.output_mem_of_pairMember hL⟩⟩
  let ρ : Env (rt_model_l X nx) 1 := ⟨fun _ => ⟨L, hj.1.1.input_mem_of_pairMember hL⟩, fun _ => ⟨L, hj.1.1.input_mem_of_pairMember hL⟩⟩
  let η : Env (rt_model_l Y ny) 1 := ⟨fun _ => ⟨L', hj.1.1.output_mem_of_pairMember hL⟩, fun _ => ⟨L', hj.1.1.output_mem_of_pairMember hL⟩⟩
  obtain ⟨z, hz⟩ := KP.exists_empty (ZF.modelsKP hZF)
  have tr := spred_source_l _ hZF hω ⟨c, R, d, S, hm.empty_pred_l _ hz, hn.empty_pred_l _ hz, hj⟩ nx ny
    (sc_rank_size_m .newest) (by simp -implicitDefEqProofs) ρ η (fun _ => hL)
  exact (sc_rank_size_sat_l (ZF.modelsKP hZF) hX nx ρ .newest).symm.trans
    (tr.trans (sc_rank_size_sat_l (ZF.modelsKP hZF) hY ny η .newest))

theorem Sc_rank_size_d.rank_l (hZF : M.Models ZF) {X α V L : M.Domain}
    (hX : M.TransitiveSet X) (hV : M.mem V X) (rank : Vr_d X α V) (hα : M.IsLimitOrdinal α) (hL : M.mem L V)
    (h : Sc_rank_size_d (kp_pair_l (ZF.modelsKP hZF)) X L) : Sc_rank_size_d (kp_pair_l (ZF.modelsKP hZF)) V L := by
  have ht := rank.transitive_l hZF hX hV
  have move {β μ W f} (hβ : M.mem β V) (hμ : M.mem μ V) (hW : M.mem W X) (hw : Vr_d X β W)
      (hf : M.mem f X) (bf : M.IsSetBijectionFromTo (kp_pair_l (ZF.modelsKP hZF)) f μ W) :
      M.mem W V ∧ Vr_d V β W ∧ M.mem f V := by
    obtain ⟨hW', hw'⟩ := rank.rank_l hZF hX hV hα hβ hW hw
    exact ⟨hW', hw', rank.relation_mem_l hZF hX hV hα hμ hW' hf (fn0_of_function_l (ZF.modelsKP hZF) bf.1.1).1⟩
  obtain ⟨W, f, hW, hw, hf, bf⟩ := h.level
  obtain ⟨hW', hw', hf'⟩ := move hL hL hW hw hf bf
  refine ⟨⟨W, f, hW', hw', hf', bf⟩, fun β hβ => ?_⟩
  obtain ⟨W, μ, f, hW, hw, hμ, hf, bf⟩ := h.lower β hβ
  obtain ⟨hW', hw', hf'⟩ := move (ht L hL β hβ) (ht L hL μ hμ) hW hw hf bf
  exact ⟨W, μ, f, hW', hw', hμ, hf', bf⟩

end YesMetaZFC.SetTheory.Internal
