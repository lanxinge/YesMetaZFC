import YesMetaZFC.Model.SetTheory.Internal.TuplePackStep

/-! # 任意内部有限元组的实际打包编译

以可分离的原公式规格作内部 ω 归纳。零步识别空集，后继步追加平坦配对；
输出槽在全部归纳步骤中固定，所得程序同时适用于所有实际秩层及赋值。
-/
namespace YesMetaZFC.SetTheory.Internal
open Definitional.Project InnerModel
universe u
variable {M : Structure.{u}} (hZF : M.Models ZF)
local notation "Q" => kp_pair_l (ZF.modelsKP hZF)
local notation "K" => fp_interpretation_l (ZF.models_kpi_l hZF)

theorem st_pack_zero_l {ω w b e : M.Domain} (hω : M.IsOmega ω) (hb : M.mem b ω)
    (he : ∀ x, ¬ M.mem x e) :
    ∃ m G u, Sfm_d Q ω m G ∧ M.mem u m ∧ St_pack_d Q K ω w b e m G u := by
  have heω := num_mem_l hZF.1 hω (show Num_d 0 e from he)
  have empty : Sfm_d Q ω e e := ⟨heω, Structure.IsSequenceOfLength.empty Q he,
    fun _ _ h => h.elim fun p hp => (he p hp.2).elim⟩
  obtain ⟨c, hc, hcω⟩ := hω.1.2 b hb
  let φ : Formula 1 1 := Formula.forallMem .newest .falsum
  have closed : φ.FreeClosed := by simp [φ, Formula.forallMem, Definitional.Formula.FreeClosed]
  have delta : φ.IsDelta0 := .forallMem _ .falsum
  obtain ⟨m, G, u, add, compile⟩ := source_compile_core_l Q hZF hω (source_core_l φ)
    (source_core_closed_l φ closed) (fun _ => b) hcω (fun _ => hc.predecessor_mem) empty
  refine ⟨m, G, u, add.program, add.root, fun μ Y a R E f g p hV hωY model hE hf hg _ _ hfb => ?_⟩
  have trans := ZF.v_transitive_l Q hZF hV
  have hωμ := ZF.v_ordinal_height_l hZF hV (hω.isOrdinal hZF) hωY
  obtain ⟨H, trace, _⟩ := fp_trace_rank_l Q hZF hω hV ((v_ordinal_l Q hV).transitive ω hωμ) hg
  have hp := ((hE f).mp hf).output_mem_of_pairMember hfb
  let η : Env (smdl_structure_l Q (R := R) model.1.2.1) 1 := ⟨fun _ => ⟨p, hp⟩, fun _ => ⟨p, hp⟩⟩
  have atom : Formula.satisfies (image_env_l (M := smdl_structure_l Q (R := R) model.1.2.1)
      (N := M) Subtype.val η) φ ↔ ∀ x, ¬ M.mem x p := by
    simp only [φ, Formula.satisfies_forallMem_iff, Formula.satisfies_falsum_iff]
    rfl
  exact ((compile Y R model.1.2.1 E hE f hf η (fun _ => hfb)).trans
    ((source_core_sat_l φ η).trans ((smem_delta_image_l Q model trans delta η).trans atom))).trans
      (trace.zero_code_l K hZF.1 he).symm

/-- 自动构造一个内部程序，读取前 n 个变量并在固定槽 b 检验其平坦前缀码。 -/
theorem st_pack_build_l {ω w b n : M.Domain} (hω : M.IsOmega ω) (hb : M.mem b ω)
    (hw : M.mem w b) (hn : M.mem n ω) (hnb : M.MemberSubset n b) :
    ∃ m G u, Sfm_d Q ω m G ∧ M.mem u m ∧ St_pack_d Q K ω w b n m G u := by
  let ρ : Env M 4 := ⟨Fin.cases n (Fin.cases b (Fin.cases w (fun _ => ω))), fun _ => ω⟩
  let φ : UnarySchema 4 := {
    body := .imp (Formula.subset .newest (.bound 1))
      (.existsE (.existsE (.existsE (.conj (sfm_m (𝒞 := kpair_convention_l) (.bound 7) (.bound 2) (.bound 1))
        (.conj (.mem .newest (.bound 2)) (st_pack_m (.bound 7) (.bound 6) (.bound 5) (.bound 3)
          (.bound 2) (.bound 1) .newest)))))) }
  have sat k : φ.denote ρ k ↔ (M.MemberSubset k n →
      ∃ m G u, Sfm_d Q ω m G ∧ M.mem u m ∧ St_pack_d Q K ω w b k m G u) := by
    simp only [φ, UnarySchema.denote, Formula.satisfies_imp_iff, Formula.satisfies_subset_iff,
      Formula.satisfies_exists_iff, Formula.satisfies_conj_iff, sfm_sat_l Q hZF.1,
      Formula.satisfies_mem_iff, st_pack_sat_l Q K hZF.1]; rfl
  have built : φ.denote ρ n := by
    apply hω.induction (fun k => φ.denote ρ k) (ZF.separation_exists_d hZF φ ρ ω) ?_ ?_ n hn
    · intro e he
      exact (sat e).mpr (fun _ => st_pack_zero_l hZF hω hb he)
    · intro k _ ih l hl
      refine (sat l).mpr fun hln => ?_
      obtain ⟨m, G, u, hG, hu, pack⟩ := (sat k).mp ih (fun i hi => hln i ((hl i).mpr (Or.inl hi)))
      exact st_pack_step_l hZF hω hb hw (hnb k (hln k hl.predecessor_mem)) hl hG hu pack
  exact (sat n).mp built (fun _ h => h)

end YesMetaZFC.SetTheory.Internal
