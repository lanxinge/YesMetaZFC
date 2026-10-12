import YesMetaZFC.Model.SetTheory.Internal.TuplePackCode

/-! # 在任意秩层中绑定原变量列的平坦前缀

绑定的是有限前缀码，其秩不高于原变量。随后任意固定原公式可读取它，
无需预设最大序数，也不把可能高一层的元组图作为当前模型的元素。
-/
namespace YesMetaZFC.SetTheory.Internal
open Definitional.Project InnerModel
universe u
variable {M : Structure.{u}} (hZF : M.Models ZF)
local notation "Q" => kp_pair_l (ZF.modelsKP hZF)
local notation "K" => fp_interpretation_l (ZF.models_kpi_l hZF)

theorem st_pack_bind_l {ω w b n : M.Domain} (hω : M.IsOmega ω) (hb : M.mem b ω)
    (hw : M.mem w b) (hn : M.mem n ω) (hnb : M.MemberSubset n b)
    {k : Nat} (φ : Formula 1 (k+1)) (hc : φ.FreeClosed) (σ : Fin k → M.Domain) (hσ : ∀ i, M.mem (σ i) b) :
    ∃ a m G u, Sformula_d Q ω a m G u ∧ ∀ η Y c R f g (hm : Smem_d Q c Y R)
      (ρ : Env (smdl_structure_l Q (R := R) hm.1.2.1) k),
      V_d Q η Y → M.mem ω Y → M.IsSetFunctionFromTo Q f ω Y → M.IsSetFunctionFromTo K g ω Y →
      Sx_graph_d Q K f g → M.PairMember Q w ω f → (∀ i, M.PairMember Q (σ i) (ρ.bound i).val f) →
        (Satisfies_d Q ω c a f ↔ ∃ p : (smdl_structure_l Q (R := R) hm.1.2.1).Domain,
          Fs_code_d K ω Y g n p.val ∧ Formula.satisfies (ρ.push p) φ) := by
  obtain ⟨m₀, G₀, u₀, prog, root, pack⟩ := st_pack_build_l hZF hω hb hw hn hnb
  obtain ⟨j, hj, hjω⟩ := hω.1.2 b hb
  obtain ⟨m₁, G₁, u₁, add, compile⟩ := source_compile_core_l Q hZF hω (source_core_l φ)
    (source_core_closed_l φ hc) (Fin.cases b σ) hjω
    (Fin.cases hj.predecessor_mem (fun i => (hj (σ i)).mpr (Or.inl (hσ i)))) prog
  obtain ⟨m₂, G₂, u₂, bothProg, both⟩ := sfm_and_l Q hZF hω add.program (add.span u₀ root) add.root
  obtain ⟨m, G, u, finalProg, ex⟩ := sfm_ex_l Q hZF hω bothProg.program hb bothProg.root
  obtain ⟨a, ha⟩ := (Q).total G u
  have form : Sformula_d Q ω a m G u := ⟨ha, finalProg.program, finalProg.root⟩
  refine ⟨a, m, G, u, form, fun η Y c R f g model ρ hY hωY ff fg agree fw values => ?_⟩
  obtain ⟨E, hE⟩ := ZF.exists_functionSpace hZF Q ω Y
  have hf := (hE f).mpr ff
  have hωη := (v_ordinal_l Q hY).transitive ω (ZF.v_ordinal_height_l hZF hY (hω.isOrdinal hZF) hωY)
  obtain ⟨H, trace, _⟩ := fp_trace_rank_l Q hZF hω hY hωη fg
  have body (p : (smdl_structure_l Q (R := R) model.1.2.1).Domain) f₁ (update : Senv_update_d Q f b p.val f₁) :
      Ssat_d Q Y R E G₂ m₂ u₂ f₁ ↔ Fs_code_d K ω Y g n p.val ∧ Formula.satisfies (ρ.push p) φ := by
    have fn₁ := update.function_l Q ff hb p.property
    have hf₁ := (hE f₁).mpr fn₁
    have old := update.agree_l Q (KP.mem_irrefl_d (ZF.modelsKP hZF) b)
    have fp := (update.2 b p.val).mpr (Or.inl ⟨rfl, rfl⟩)
    obtain ⟨g₁, hg₁, same₁⟩ := fn_recode_l Q K hZF fn₁
    obtain ⟨H₁, trace₁, _⟩ := fp_trace_rank_l Q hZF hω hY hωη hg₁
    have same : Senv_agree_d K n g₁ g := fun i x hi =>
      (same₁ i x).trans ((old i x (hnb i hi)).symm.trans (agree i x).symm)
    have codes : Fs_code_d K ω Y g₁ n p.val ↔ Fs_code_d K ω Y g n p.val :=
      ⟨fun h => h.transport_l K hZF hω hg₁ fg trace same,
        fun h => h.transport_l K hZF hω fg hg₁ trace₁ (fun i x hi => (same i x hi).symm)⟩
    have packed := (add.sat_l Q hZF prog root Y R E f₁).symm.trans
      ((pack η Y c R E f₁ g₁ p.val hY hωY model hE hf₁ hg₁ same₁ ((old w ω hw).mp fw) fp).trans codes)
    have atom := (compile Y R model.1.2.1 E hE f₁ hf₁ (ρ.push p)
      (Fin.cases fp (fun i => (old (σ i) (ρ.bound i).val (hσ i)).mp (values i)))).trans (source_core_sat_l φ (ρ.push p))
    exact (both Y R E f₁ hf₁).trans (and_congr packed atom)
  refine (satisfies_decode_l Q hZF.1 model.1 form hE).trans ((ex Y R E f hf).trans ⟨?_, ?_⟩)
  · rintro ⟨p, f₁, hp, update, truth⟩
    exact ⟨⟨p, hp⟩, (body ⟨p, hp⟩ f₁ update).mp truth⟩
  · rintro ⟨p, truth⟩
    obtain ⟨f₁, update, _⟩ := senv_update_exists_l Q hZF ff hb p.property
    exact ⟨p.val, f₁, p.property, update, (body p f₁ update).mpr truth⟩

end YesMetaZFC.SetTheory.Internal
