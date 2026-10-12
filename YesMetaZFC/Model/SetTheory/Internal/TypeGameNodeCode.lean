import YesMetaZFC.Model.SetTheory.Internal.TypeGameNodeSource
import YesMetaZFC.Model.SetTheory.Internal.FiniteSetCode
import YesMetaZFC.Model.SetTheory.Internal.Compiler

/-! # 类型游戏的内部有限节点程序

原变量之间任意排列；程序仅检验其中间坐标所成的集合是一张完整节点图。
只绑定该低秩图，不把原元组本身当作新增自由参数。
-/
namespace YesMetaZFC.SetTheory.Internal
open Definitional.Project InnerModel
universe u
variable {M : Structure.{u}} (hZF : M.Models ZF)
local notation "I" => kp_pair_l (ZF.modelsKP hZF)

theorem tg_node_build_l {ω e l b : M.Domain} (hω : M.IsOmega ω)
    (hl : M.mem l ω) (hb : M.mem b ω) (he : M.mem e l) (lb : M.MemberSubset l b)
    (σ : Fin 3 → M.Domain) (hσ : ∀ i, M.mem (σ i) b) :
    ∃ a m G u, Sformula_d I ω a m G u ∧ ∀ c X R f S s t k,
      Smem_d I c X R → M.TransitiveSet X → M.IsSetFunctionFromTo I f ω X →
      Rd_entry_d e S f → Rd_entry_d (σ 0) s f → Rd_entry_d (σ 1) t f → Rd_entry_d (σ 2) k f →
      (Satisfies_d I ω c a f ↔ ∃ g, M.mem g X ∧ Sg_set_d I e l f g ∧ Tg_node_d I k S s t g) := by
  obtain ⟨p, hs, hp⟩ := hω.1.2 b hb
  have bp := hs.predecessor_mem
  have up {i} (hi : M.mem i b) : M.mem i p := (hs i).mpr (Or.inl hi)
  obtain ⟨m₀, G₀, u₀, prog, root, set⟩ := sg_set_build_l I hZF hω hl hb hp bp (fun i hi => up (lb i hi))
  let φ : Formula 1 5 := tg_node_m (.bound 0) (.bound 1) (.bound 2) (.bound 3) (.bound 4)
  have hc : φ.FreeClosed := tg_node_m_freeClosed _ _ _ _ _ rfl rfl rfl rfl rfl
  let v : Fin 5 → M.Domain := Fin.cases (σ 2) (Fin.cases e (Fin.cases (σ 0) (Fin.cases (σ 1) (fun _ => b))))
  have hv : ∀ i, M.mem (v i) p := Fin.cases (up (hσ 2))
    (Fin.cases (up (lb e he)) (Fin.cases (up (hσ 0)) (Fin.cases (up (hσ 1)) (fun _ => bp))))
  obtain ⟨m₁, G₁, u₁, add, compile⟩ := source_compile_core_l I hZF hω (source_core_l φ)
    (source_core_closed_l φ hc) v hp hv prog
  obtain ⟨m₂, G₂, u₂, bothProg, both⟩ := sfm_and_l I hZF hω add.program (add.span u₀ root) add.root
  obtain ⟨m, G, u, finalProg, ex⟩ := sfm_ex_l I hZF hω bothProg.program hb bothProg.root
  obtain ⟨a, ca⟩ := (I).total G u
  have form : Sformula_d I ω a m G u := ⟨ca, finalProg.program, finalProg.root⟩
  refine ⟨a, m, G, u, form, fun c X R f S s t k model trans ff fS fs ft fk => ?_⟩
  obtain ⟨E, hE⟩ := ZF.exists_functionSpace hZF I ω X
  have hf := (hE f).mpr ff
  let nx : Nonempty {x // M.mem x X} := ⟨⟨S, ff.output_mem_of_pairMember fS⟩⟩
  have body g (hg : M.mem g X) f₁ (update : Senv_update_d I f b g f₁) :
      Ssat_d I X R E G₂ m₂ u₂ f₁ ↔ Sg_set_d I e l f g ∧ Tg_node_d I k S s t g := by
    have ff₁ := update.function_l I ff hb hg
    have hf₁ := (hE f₁).mpr ff₁
    have fb := (update.2 b g).mpr (Or.inl ⟨rfl, rfl⟩)
    have same := update.agree_l I (KP.mem_irrefl_d (ZF.modelsKP hZF) b)
    have sets : Sg_set_d I e l f₁ g ↔ Sg_set_d I e l f g :=
      forall_congr' fun x => iff_congr Iff.rfl (exists_congr fun i => and_congr_right fun hi =>
        and_congr_right fun _ => (same i x (lb i hi)).symm)
    have setRead := (add.sat_l I hZF prog root X R E f₁).symm.trans
      ((set c X R E f₁ g model trans hE hf₁ fb).trans sets)
    let ρ : Env (rt_model_l X nx) 5 := ⟨Fin.cases ⟨k, ff.output_mem_of_pairMember fk⟩
      (Fin.cases ⟨S, ff.output_mem_of_pairMember fS⟩ (Fin.cases ⟨s, ff.output_mem_of_pairMember fs⟩
        (Fin.cases ⟨t, ff.output_mem_of_pairMember ft⟩ (fun _ => ⟨g, hg⟩)))), fun _ => ⟨g, hg⟩⟩
    let η : Env (smdl_structure_l I (R := R) model.1.2.1) 5 := ⟨ρ.bound, ρ.free⟩
    have values : ∀ i, Rd_entry_d (v i) (η.bound i).val f₁ :=
      Fin.cases ((same (σ 2) k (hσ 2)).mp fk) (Fin.cases ((same e S (lb e he)).mp fS)
        (Fin.cases ((same (σ 0) s (hσ 0)).mp fs) (Fin.cases ((same (σ 1) t (hσ 1)).mp ft) (fun _ => fb))))
    have nodeRead := (compile X R model.1.2.1 E hE f₁ hf₁ η values).trans ((source_core_sat_l φ η).trans
      ((smem_formula_l I model nx φ ρ).symm.trans
        (tg_node_source_l trans nx (ZF.modelsKP hZF).1 (KP.exists_pair (ZF.modelsKP hZF)) ρ _ _ _ _ _)))
    exact (both X R E f₁ hf₁).trans (and_congr setRead nodeRead)
  refine (satisfies_decode_l I hZF.1 model.1 form hE).trans ((ex X R E f hf).trans ⟨?_, ?_⟩)
  · rintro ⟨g, f₁, hg, update, truth⟩
    exact ⟨g, hg, (body g hg f₁ update).mp truth⟩
  · rintro ⟨g, hg, truth⟩
    obtain ⟨f₁, update, _⟩ := senv_update_exists_l I hZF ff hb hg
    exact ⟨g, f₁, hg, update, (body g hg f₁ update).mpr truth⟩

end YesMetaZFC.SetTheory.Internal
