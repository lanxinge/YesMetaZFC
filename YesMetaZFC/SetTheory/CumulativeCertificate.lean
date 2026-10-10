import YesMetaZFC.SetTheory.Cumulative
import YesMetaZFC.SetTheory.InnerModel.Recursion.Graph
import YesMetaZFC.SetTheory.KP.Ordinal
import YesMetaZFC.SetTheory.Definitional.Project.Hierarchy.Levy

/-! # 累积层级的全称递归证书

历史函数和值域作为存在见证。全部局部检查有界，唯一无界变量枚举任意子集，
以核验真实幂集递归；由此给出累积层值关系的实际 Σ₂ 公式。
-/
namespace YesMetaZFC.SetTheory
open Definitional.Project InnerModel
universe u
variable {M : Structure.{u}}

def Vc_step_d (a B F W t : M.Domain) : Prop := M.mem t W ↔
  ∃ b, M.mem b a ∧ ∃ Y, M.mem Y B ∧ Rd_entry_d b Y F ∧ M.MemberSubset t Y

def vc_step_m {d} (a B F W t : Term d) : Formula 1 d :=
  .iff (.mem t W) (Formula.existsMem a (Formula.existsMem B.weaken
    (.conj (rd_entry0_m (.bound 1) .newest F.weaken.weaken) (Formula.subset t.weaken.weaken .newest))))
derive_free_closed vc_step_m

theorem vc_step_delta_l {d} (a B F W t : Term d) : (vc_step_m a B F W t).IsDelta0 :=
  .iff (.mem _ _) (.existsMem _ (.existsMem _ (.conj (rd_entry0_delta_l ..) (.atom _ _ _))))

theorem vc_step_sat_l (hE : Extensional M) {d} (ρ : Env M d) (a B F W t : Term d) :
    Formula.satisfies ρ (vc_step_m a B F W t) ↔
      Vc_step_d (a.eval ρ) (B.eval ρ) (F.eval ρ) (W.eval ρ) (t.eval ρ) := by
  simp only [vc_step_m, Vc_step_d, Formula.satisfies_iff_iff, Formula.satisfies_mem_iff,
    Formula.satisfies_existsMem_iff, Formula.satisfies_conj_iff, rd_entry0_sat_l hE,
    Formula.satisfies_subset_iff, Definitional.Term.eval_weaken, Definitional.Term.eval_newest]
  rfl

def Vc_d (a X B F t : M.Domain) : Prop := M.IsOrdinal a ∧ Fn0_d a B F ∧
  (∀ b, M.mem b a → ∀ Y, M.mem Y B → Rd_entry_d b Y F → Vc_step_d b B F Y t) ∧ Vc_step_d a B F X t

def vc_matrix_m {d} (a X B F t : Term d) : Formula 1 d :=
  .conj (KP.ord0_m a) (.conj (fn0_m a B F) (.conj
    (Formula.forallMem a (Formula.forallMem B.weaken (.imp
      (rd_entry0_m (.bound 1) .newest F.weaken.weaken)
      (vc_step_m (.bound 1) B.weaken.weaken F.weaken.weaken .newest t.weaken.weaken))))
    (vc_step_m a B F X t)))
derive_free_closed vc_matrix_m

theorem vc_matrix_delta_l {d} (a X B F t : Term d) : (vc_matrix_m a X B F t).IsDelta0 :=
  .conj (KP.ord0_delta_l _) (.conj (fn0_delta_l ..) (.conj
    (.forallMem _ (.forallMem _ (.imp (rd_entry0_delta_l ..) (vc_step_delta_l ..)))) (vc_step_delta_l ..)))

theorem vc_matrix_sat_l (hKP : M.Models KP) {d} (ρ : Env M d) (a X B F t : Term d) :
    Formula.satisfies ρ (vc_matrix_m a X B F t) ↔
      Vc_d (a.eval ρ) (X.eval ρ) (B.eval ρ) (F.eval ρ) (t.eval ρ) := by
  simp only [vc_matrix_m, Vc_d, Formula.satisfies_conj_iff, KP.ord0_sat_l hKP,
    fn0_sat_l hKP.1, Formula.satisfies_forallMem_iff, Formula.satisfies_imp_iff,
    rd_entry0_sat_l hKP.1, vc_step_sat_l hKP.1, Definitional.Term.eval_weaken]
  rfl

theorem vc_sound_l (hKP : M.Models KP) {a X B F : M.Domain} (h : ∀ t, Vc_d a X B F t) :
    V_d (kp_pair_l hKP) a X := by
  have hf := fn0_function_l hKP (h X).2.1
  refine ⟨F, ⟨⟨(h X).1, hf.1, hf.2.1⟩, ?_⟩, ?_⟩
  · intro b hb Y hY
    obtain ⟨P, hP⟩ := res0_exists_l hKP F b B
    have hr := res0_restriction_l hKP (h X).2.1 hP
    refine ⟨P, hr, fun t => ((h t).2.2.1 b hb Y (hf.output_mem_of_pairMember hY) hY).trans ?_⟩
    exact ⟨fun ⟨c, hc, Z, _, hz, ht⟩ => ⟨c, Z, (hr.2 c Z).mpr ⟨hc, hz⟩, ht⟩,
      fun ⟨c, Z, hz, ht⟩ => ⟨c, ((hr.2 c Z).mp hz).1, Z,
        hf.output_mem_of_pairMember ((hr.2 c Z).mp hz).2, ((hr.2 c Z).mp hz).2, ht⟩⟩
  · intro t
    exact ((h t).2.2.2).trans ⟨fun ⟨b, _, Y, _, hy, ht⟩ => ⟨b, Y, hy, ht⟩,
      fun ⟨b, Y, hy, ht⟩ => ⟨b, hf.input_mem_of_pairMember hy, Y, hf.output_mem_of_pairMember hy, hy, ht⟩⟩

theorem vc_complete_l (hKP : M.Models KP) {a X : M.Domain} (h : V_d (kp_pair_l hKP) a X) :
    ∃ B F, ∀ t, Vc_d a X B F t := by
  obtain ⟨F, hf, hx⟩ := h
  obtain ⟨B, hB⟩ := rd_fun_exists_l hKP .range F F F
  have hb Y : M.mem Y B ↔ ∃ b, Rd_entry_d b Y F := hB Y
  have hF : M.IsSetFunctionFromTo (kp_pair_l hKP) F a B :=
    ⟨hf.1.2.1, hf.1.2.2, fun b hba => (hf.1.2.2 b).mp hba |>.elim fun Y hy => ⟨Y, (hb Y).mpr ⟨b, hy⟩, hy⟩⟩
  refine ⟨B, F, fun t => ⟨hf.1.1, fn0_of_function_l hKP hF, ?_, ?_⟩⟩
  · intro b hba Y _ hY
    obtain ⟨P, hP, hp⟩ := hf.2 b hba Y hY
    exact (hp t).trans ⟨fun ⟨c, Z, hz, ht⟩ => ⟨c, ((hP.2 c Z).mp hz).1, Z,
      hF.output_mem_of_pairMember ((hP.2 c Z).mp hz).2, ((hP.2 c Z).mp hz).2, ht⟩,
      fun ⟨c, hc, Z, _, hz, ht⟩ => ⟨c, Z, (hP.2 c Z).mpr ⟨hc, hz⟩, ht⟩⟩
  · exact (hx t).trans ⟨fun ⟨b, Y, hy, ht⟩ =>
      ⟨b, hF.input_mem_of_pairMember hy, Y, hF.output_mem_of_pairMember hy, hy, ht⟩,
      fun ⟨b, _, Y, _, hy, ht⟩ => ⟨b, Y, hy, ht⟩⟩

def v_sigma_m {d} (a X : Term d) : Formula 1 d := .existsE (.existsE (.forallE
  (vc_matrix_m a.weaken.weaken.weaken X.weaken.weaken.weaken (.bound 2) (.bound 1) .newest)))
derive_free_closed v_sigma_m

theorem v_sigma_complexity_l {d} (a X : Term d) : (v_sigma_m a X).IsSigma2 :=
  .existsE (.existsE (.lift (.forallE (.lift (.base (vc_matrix_delta_l ..))))))

theorem v_sigma_sat_l (hKP : M.Models KP) {d} (ρ : Env M d) (a X : Term d) :
    Formula.satisfies ρ (v_sigma_m a X) ↔ V_d (kp_pair_l hKP) (a.eval ρ) (X.eval ρ) := by
  simp only [v_sigma_m, Formula.satisfies_exists_iff, Formula.satisfies_forall_iff,
    vc_matrix_sat_l hKP, Definitional.Term.eval_weaken]
  exact ⟨fun ⟨B, F, h⟩ => vc_sound_l hKP h, vc_complete_l hKP⟩

end YesMetaZFC.SetTheory
