import YesMetaZFC.Model.SetTheory.Internal.TuplePackSyntax
import YesMetaZFC.Model.SetTheory.Internal.Sigma1Substructure

/-! # 内部打包程序的后继步

输出槽 b 保持固定。先把输出复制到新槽 c，再绑定 b 为旧前缀，
检验平坦配对；最后绑定 c。两次更新均保持原变量及 ω 参数。
-/
namespace YesMetaZFC.SetTheory.Internal
open Definitional.Project InnerModel
universe u
variable {M : Structure.{u}} (hZF : M.Models ZF)
local notation "Q" => kp_pair_l (ZF.modelsKP hZF)
local notation "K" => fp_interpretation_l (ZF.models_kpi_l hZF)

theorem st_pack_step_l {ω w b k l m G u : M.Domain} (hω : M.IsOmega ω) (hb : M.mem b ω)
    (hw : M.mem w b) (hk : M.mem k b) (hl : M.SuccessorOf l k)
    (hG : Sfm_d Q ω m G) (hu : M.mem u m) (pack : St_pack_d Q K ω w b k m G u) :
    ∃ m' G' u', Sfm_d Q ω m' G' ∧ M.mem u' m' ∧ St_pack_d Q K ω w b l m' G' u' := by
  have hwω := hω.transitive hZF b hb w hw
  have hkω := hω.transitive hZF b hb k hk
  obtain ⟨c, hc, hcω⟩ := hω.1.2 b hb
  obtain ⟨d, hd, hdω⟩ := hω.1.2 c hcω
  have below {i} (hi : M.mem i b) : M.mem i d := (hd i).mpr (Or.inl ((hc i).mpr (Or.inl hi)))
  let φ : Formula 1 4 := fp_pair0_m (.bound 3) (.bound 2) (.bound 1) .newest
  obtain ⟨m₁, G₁, v, add, compile⟩ := source_compile_core_l Q hZF hω (source_core_l φ)
    (source_core_closed_l φ (fp_pair0_m_freeClosed _ _ _ _ rfl rfl rfl rfl))
    (Fin.cases c (Fin.cases k (Fin.cases b (fun _ => w)))) hdω
    (Fin.cases hd.predecessor_mem (Fin.cases (below hk)
      (Fin.cases ((hd b).mpr (Or.inl hc.predecessor_mem)) (fun _ => below hw)))) hG
  obtain ⟨m₂, G₂, r₂, a₂, both₂⟩ := sfm_and_l Q hZF hω add.program (add.span u hu) add.root
  obtain ⟨m₃, G₃, r₃, a₃, ex₃⟩ := sfm_ex_l Q hZF hω a₂.program hb a₂.root
  obtain ⟨m₄, G₄, a₄, eq₄⟩ := sfm_eq_l Q hZF hω a₃.program hcω hb
  obtain ⟨m₅, G₅, r₅, a₅, both₅⟩ := sfm_and_l Q hZF hω a₄.program a₄.root (a₄.span r₃ a₃.root)
  obtain ⟨m₆, G₆, r₆, a₆, ex₆⟩ := sfm_ex_l Q hZF hω a₅.program hcω a₅.root
  refine ⟨m₆, G₆, r₆, a₆.program, a₆.root, fun μ Y a R E f g p hV hωY model hE hf hg fg hfw hfb => ?_⟩
  have fn := (hE f).mp hf
  have trans := ZF.v_transitive_l Q hZF hV
  have hωμ := (v_ordinal_l Q hV).transitive ω (ZF.v_ordinal_height_l hZF hV (hω.isOrdinal hZF) hωY)
  obtain ⟨H, trace, _⟩ := fp_trace_rank_l Q hZF hω hV hωμ hg
  obtain ⟨x, hxY, hfx⟩ := fn.2.2 k hkω
  have gx := (fg k x).mpr hfx
  have body z (hz : M.mem z Y) f₁ (copy : Senv_update_d Q f c z f₁) :
      Ssat_d Q Y R E G₅ m₅ r₅ f₁ ↔ z = p ∧ Fs_code_d K ω Y g l z := by
    have fn₁ := copy.function_l Q fn hcω hz
    have hf₁ := (hE f₁).mpr fn₁
    have old₁ := copy.agree_l Q (KP.mem_irrefl_d (ZF.modelsKP hZF) c)
    have fc := (copy.2 c z).mpr (Or.inl ⟨rfl, rfl⟩)
    have fb := (old₁ b p hc.predecessor_mem).mp hfb
    have inner q (hq : M.mem q Y) f₂ (update : Senv_update_d Q f₁ b q f₂) :
        Ssat_d Q Y R E G₂ m₂ r₂ f₂ ↔ Fs_code_d K ω Y g k q ∧ (K).Codes z q x := by
      have fn₂ := update.function_l Q fn₁ hb hq
      have hf₂ := (hE f₂).mpr fn₂
      have old₂ := update.agree_l Q (KP.mem_irrefl_d (ZF.modelsKP hZF) b)
      have old i y (hi : M.mem i b) : M.PairMember Q i y f ↔ M.PairMember Q i y f₂ :=
        (old₁ i y ((hc i).mpr (Or.inl hi))).trans (old₂ i y hi)
      have fw := (old w ω hw).mp hfw
      have fk := (old k x hk).mp hfx
      have fq := (update.2 b q).mpr (Or.inl ⟨rfl, rfl⟩)
      have cb : c ≠ b := fun eq => KP.mem_irrefl_d (ZF.modelsKP hZF) b (eq ▸ hc.predecessor_mem)
      have fz := (update.2 c z).mpr (Or.inr ⟨cb, fc⟩)
      obtain ⟨g₂, hg₂, fg₂⟩ := fn_recode_l Q K hZF fn₂
      obtain ⟨H₂, trace₂, _⟩ := fp_trace_rank_l Q hZF hω hV hωμ hg₂
      have same : Senv_agree_d K k g₂ g := fun i y hi => (fg₂ i y).trans
        ((old i y ((hω.members_areOrdinals hZF b hb).transitive k hk i hi)).symm.trans (fg i y).symm)
      have code_eq : Fs_code_d K ω Y g₂ k q ↔ Fs_code_d K ω Y g k q :=
        ⟨fun h => h.transport_l K hZF hω hg₂ hg trace same,
          fun h => h.transport_l K hZF hω hg hg₂ trace₂ (same.symm_l K)⟩
      have prev := (add.sat_l Q hZF hG hu Y R E f₂).symm.trans
        ((pack μ Y a R E f₂ g₂ q hV hωY model hE hf₂ hg₂ fg₂ fw fq).trans code_eq)
      let η : Env (smdl_structure_l Q (R := R) model.1.2.1) 4 :=
        ⟨Fin.cases ⟨z, hz⟩ (Fin.cases ⟨x, hxY⟩ (Fin.cases ⟨q, hq⟩ (fun _ => ⟨ω, hωY⟩))), fun _ => ⟨q, hq⟩⟩
      have atom : Ssat_d Q Y R E G₁ m₁ v f₂ ↔ (K).Codes z q x :=
        (compile Y R model.1.2.1 E hE f₂ hf₂ η (Fin.cases fz (Fin.cases fk (Fin.cases fq (fun _ => fw))))).trans
          ((source_core_sat_l φ η).trans ((smem_delta_image_l Q model trans (fp_pair0_delta_l ..) η).trans
            ((fp_pair0_sat_l (ZF.modelsKP hZF) (image_env_l
              (M := smdl_structure_l Q (R := R) model.1.2.1) (N := M) Subtype.val η)
              (.bound 3) (.bound 2) (.bound 1) .newest hω.1).trans
              (fp_fixed_l hZF.1 hω).symm)))
      exact (both₂ Y R E f₂ hf₂).trans (and_congr prev atom)
    have step : Ssat_d Q Y R E G₃ m₃ r₃ f₁ ↔ Fs_code_d K ω Y g l z := by
      refine (ex₃ Y R E f₁ hf₁).trans ⟨?_, ?_⟩
      · rintro ⟨q, f₂, hq, update, truth⟩
        obtain ⟨code, pair⟩ := (inner q hq f₂ update).mp truth
        exact (Fs_code_d.step_l K hZF.1 hω.1 hkω hl gx).mpr ⟨q, code, pair⟩
      · intro truth
        obtain ⟨q, code, pair⟩ := (Fs_code_d.step_l K hZF.1 hω.1 hkω hl gx).mp truth
        obtain ⟨f₂, update, _⟩ := senv_update_exists_l Q hZF fn₁ hb (code.bound_l K).2
        exact ⟨q, f₂, (code.bound_l K).2, update, (inner q (code.bound_l K).2 f₂ update).mpr ⟨code, pair⟩⟩
    exact (both₅ Y R E f₁ hf₁).trans (and_congr (eq₄ Y R E f₁ z p hE hf₁ fc fb)
      ((a₄.sat_l Q hZF a₃.program a₃.root Y R E f₁).symm.trans step))
  refine (ex₆ Y R E f hf).trans ⟨?_, ?_⟩
  · rintro ⟨z, f₁, hz, copy, truth⟩
    obtain ⟨eq, code⟩ := (body z hz f₁ copy).mp truth
    exact eq ▸ code
  · intro truth
    have hp := fn.output_mem_of_pairMember hfb
    obtain ⟨f₁, copy, _⟩ := senv_update_exists_l Q hZF fn hcω hp
    exact ⟨p, f₁, hp, copy, (body p hp f₁ copy).mpr ⟨rfl, truth⟩⟩

end YesMetaZFC.SetTheory.Internal
