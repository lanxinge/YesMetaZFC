import YesMetaZFC.Model.SetTheory.Internal.SourceCollapse
import YesMetaZFC.SetTheory.Collapse.RelationSequence
import YesMetaZFC.SetTheory.HereditaryFunction

/-! # 源模型中的可数枝与良基绝对性

正则 Hχ 包含非良基关系的一条实际 ω 下降链。该存在性质沿完整初等嵌入
传递；结合塌缩的良基绝对性，外部下降链可换为模型内的下降链。
-/
namespace YesMetaZFC.SetTheory.Internal
open Definitional.Project InnerModel
universe u
variable {M : Structure.{u}}

def wf_chain_m {n} (ω A R f : Term n) : Formula 1 n := .conj (fn0_m ω A f)
  (Formula.forallMem ω (Formula.forallMem ω.weaken (.imp (KP.succ0_m .newest (.bound 1))
    (Formula.forallMem A.weaken.weaken (Formula.forallMem A.weaken.weaken.weaken
      (.imp (rd_entry0_m (.bound 3) (.bound 1) f.weaken.weaken.weaken.weaken)
        (.imp (rd_entry0_m (.bound 2) .newest f.weaken.weaken.weaken.weaken)
          (rd_entry0_m .newest (.bound 1) R.weaken.weaken.weaken.weaken))))))))
derive_free_closed wf_chain_m

theorem wf_chain_delta_l {n} (ω A R f : Term n) : (wf_chain_m ω A R f).IsDelta0 :=
  .conj (fn0_delta_l ..) (.forallMem _ (.forallMem _ (.imp (KP.succ0_delta_l ..)
    (.forallMem _ (.forallMem _ (.imp (rd_entry0_delta_l ..) (.imp (rd_entry0_delta_l ..) (rd_entry0_delta_l ..))))))))

theorem wf_chain_sat_l (hE : Extensional M) {n} (ρ : Env M n) (ω A R f : Term n) :
    Formula.satisfies ρ (wf_chain_m ω A R f) ↔
      Fn0_d (ω.eval ρ) (A.eval ρ) (f.eval ρ) ∧ Wf_desc_d (R.eval ρ) (f.eval ρ) := by
  simp only [wf_chain_m, Formula.satisfies_conj_iff, Formula.satisfies_forallMem_iff,
    Formula.satisfies_imp_iff, fn0_sat_l hE, KP.succ0_sat_l hE, rd_entry0_sat_l hE,
    Definitional.Term.eval_weaken, Definitional.Term.eval_newest]
  constructor
  · rintro ⟨hf, h⟩
    exact ⟨hf, fun i j x y hs hi hj => h i (hf.bound_l hi).1 j (hf.bound_l hj).1 hs
      x (hf.bound_l hi).2 y (hf.bound_l hj).2 hi hj⟩
  · exact fun ⟨hf, h⟩ => ⟨hf, fun i _ j _ hs x _ y _ => h i j x y hs⟩

def Sc_branch_d (ω X : M.Domain) : Prop := ∀ A R, M.mem A X → M.mem R X →
  ¬ Sc_wf_d X A R → ∃ f, M.mem f X ∧ Fn0_d ω A f ∧ Wf_desc_d R f

def sc_branch_m {n} (ω : Term n) : Formula 1 n := .forallE (.forallE
  (.imp (.neg (wf_rel_m (.bound 1) .newest))
    (.existsE (wf_chain_m ω.weaken.weaken.weaken (.bound 2) (.bound 1) .newest))))
derive_free_closed sc_branch_m

theorem sc_branch_sat_l (hE : Extensional M) {X ω : M.Domain} (hX : M.TransitiveSet X)
    (hω : M.mem ω X) (hn : Nonempty {x : M.Domain // M.mem x X}) :
    Formula.satisfies (⟨fun _ => ⟨ω, hω⟩, fun _ => ⟨ω, hω⟩⟩ : Env (rt_model_l X hn) 1)
      (sc_branch_m .newest) ↔ Sc_branch_d ω X := by
  have wf (η : Env (rt_model_l X hn) 3) :
      Formula.satisfies η (wf_rel_m (.bound 1) .newest) ↔ Sc_wf_d X (η.bound 1).val (η.bound 0).val :=
    (wf_rel_sat_l (rt_model_ext_l hE hX hn) η _ _).trans (sc_wf_relative_l hE hX hn _ _)
  have chain (η : Env (rt_model_l X hn) 4) :
      Formula.satisfies η (wf_chain_m (Term.newest : Term 1).weaken.weaken.weaken (.bound 2) (.bound 1) .newest) ↔
        Fn0_d (η.bound 3).val (η.bound 2).val (η.bound 0).val ∧ Wf_desc_d (η.bound 1).val (η.bound 0).val :=
    (rt_model_delta_l hX hn (wf_chain_delta_l ..) η).trans (wf_chain_sat_l hE ..)
  simp only [sc_branch_m, Formula.satisfies_forall_iff, Formula.satisfies_imp_iff,
    Formula.satisfies_neg_iff, Formula.satisfies_exists_iff, wf, chain]
  exact ⟨fun h A R hA hR hw => (h ⟨A, hA⟩ ⟨R, hR⟩ hw).elim fun f hf => ⟨f.val, f.property, hf⟩,
    fun h A R hw => (h A.val R.val A.property R.property hw).elim fun f hf => ⟨⟨f, hf.1⟩, hf.2⟩⟩

theorem sc_h_branch_l (hZFC : M.Models ZFC) {ω χ H : M.Domain}
    (hω : M.IsOmega ω) (hχ : M.IsRegularCardinal (kp_pair_l (ZF.modelsKP (ZFC.models_zf_l hZFC))) χ)
    (hωχ : M.mem ω χ) (hH : H_d (kp_pair_l (ZF.modelsKP (ZFC.models_zf_l hZFC))) χ H)
    (hωH : M.mem ω H) : Sc_branch_d ω H := by
  classical
  let hZF := ZFC.models_zf_l hZFC
  let I := kp_pair_l (ZF.modelsKP hZF)
  intro A R hA _ hw
  have hn : ¬ Wf_rel_d A R := fun h => hw (fun Y _ => h Y)
  have ex : ∃ f, Fn0_d ω A f ∧ Wf_desc_d R f := by
    apply Classical.byContradiction
    intro no
    exact hn (wf_of_no_desc_l hZF (ZFC.dc_l I hZFC hω) (fun f hf hd => no ⟨f, hf, hd⟩))
  obtain ⟨f, hf, hd⟩ := ex
  exact ⟨f, ZFC.h_function_l hZFC hω hχ hωχ hH hωH
    (fn0_function_l (ZF.modelsKP hZF) (hf.mono_target_l (ZF.h_transitive_l I hZF hH A hA))), hf, hd⟩

theorem Sc_branch_d.map_l (hZF : M.Models ZF) {ω c d X R Y S q : M.Domain}
    (hω : M.IsOmega ω) (h : Sc_branch_d ω X) (hX : M.TransitiveSet X) (hY : M.TransitiveSet Y)
    (hωX : M.mem ω X) (hm : Smem_d (kp_pair_l (ZF.modelsKP hZF)) c X R)
    (hn : Smem_d (kp_pair_l (ZF.modelsKP hZF)) d Y S)
    (hq : Smap_d (kp_pair_l (ZF.modelsKP hZF)) ω c d X Y q) : Sc_branch_d ω Y := by
  let I := kp_pair_l (ZF.modelsKP hZF)
  have fix := hq.omega_l I hZF hω hX hY hm hn hωX
  have hωY := hq.1.1.output_mem_of_pairMember fix
  let nx : Nonempty {a // M.mem a X} := ⟨⟨ω, hωX⟩⟩
  let ny : Nonempty {a // M.mem a Y} := ⟨⟨ω, hωY⟩⟩
  obtain ⟨e, he⟩ := KP.exists_empty (ZF.modelsKP hZF)
  have tr := spred_source_l I hZF hω ⟨c, R, d, S, hm.empty_pred_l I he, hn.empty_pred_l I he, hq⟩ nx ny
    (sc_branch_m (n := 1) .newest) (by simp -implicitDefEqProofs)
    ⟨fun _ => ⟨ω, hωX⟩, fun _ => ⟨ω, hωX⟩⟩ ⟨fun _ => ⟨ω, hωY⟩, fun _ => ⟨ω, hωY⟩⟩ (fun _ => fix)
  exact (sc_branch_sat_l hZF.1 hY hωY ny).mp (tr.mp ((sc_branch_sat_l hZF.1 hX hωX nx).mpr h))

/-- 只需把外部枝换为模型内某一枝，故不要求原枝自身属于模型。 -/
theorem sc_branch_absolute_l (hZF : M.Models ZF) {ω X A R : M.Domain} (hω : M.IsOmega ω)
    (hc : Sc_collapse_d X) (hb : Sc_branch_d ω X) (hA : M.mem A X) (hR : M.mem R X) :
    (∃ f, Fn0_d ω A f ∧ Wf_desc_d R f) ↔ ∃ f, M.mem f X ∧ Fn0_d ω A f ∧ Wf_desc_d R f := by
  refine ⟨?_, fun ⟨f, _, hf⟩ => ⟨f, hf⟩⟩
  rintro ⟨f, hf, hd⟩
  exact hb A R hA hR (fun hw => wf_no_desc_l hZF hω ((hc.wf_absolute_l (ZF.modelsKP hZF) hA hR).mp hw) hf hd)

end YesMetaZFC.SetTheory.Internal
