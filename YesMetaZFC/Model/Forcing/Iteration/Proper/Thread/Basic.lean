import YesMetaZFC.Model.Forcing.Iteration.Proper.Thread.Step
import YesMetaZFC.Model.Forcing.Iteration.Proper.Natural
import YesMetaZFC.Model.SetTheory.ClassChoice

/-! # 变动主前缀与稠密名称的实际内部 ω 序列

原状态公式直接输入类上带指标依赖选择。每一转移的存在性由稠密名称、实际
投影和已证明的较短区间给出；返回的序列是模型内集合，覆盖非标准内部指标。
-/

namespace YesMetaZFC.Model.Forcing.Internal
open SetTheory SetTheory.Definitional.Project SetTheory.Internal
universe u
variable {M : SetTheory.Structure.{u}} (hZFC : M.Models ZFC)
local notation "hZF" => ZFC.models_zf_l hZFC
local notation "I" => kpair_interpretation_l M (And.left hZFC) (KP.exists_pair (ZF.modelsKP hZF))

theorem row_pr_thread_l {ω χ H c J d N S δ F G b β D V A Z E x}
    (hω : M.IsOmega ω) (hχ : M.IsLimitOrdinal χ) (hH : H_d I χ H)
    (hJ : ∀ u v, M.PairMember I u v J ↔ M.mem u H ∧ M.mem v H ∧ M.mem u v)
    (hSub : Ssub_d I c d H J N S) (hElem : Selem_d I ω c d)
    (h : Row_system_d I δ F G b) (hD : Entry_d M β D F) (hV : Entry_d M β V G)
    (hFN : M.mem F N) (hGN : M.mem G N) (hDN : M.mem D N) (hVN : M.mem V N)
    (hA : M.IsSetFunctionFromTo I A ω Z)
    (hi : ∀ i α, Entry_d M i α A → M.mem α N ∧ M.mem α β)
    (hm : Cc_increasing_d I A)
    (hP : ∀ i α, Entry_d M i α A → Row_pil_stage_d I F G b N α)
    (hE : M.IsSetFunctionFromTo I E ω N)
    (hd : ∀ i U, Entry_d M i U E → Dense_set_d M D V D U)
    (hx : Row_pr_thread_d I F G b D N A b x) :
    ∃ X Q, M.IsSetFunctionFromTo I Q ω X ∧ Entry_d M b x Q ∧
      (∀ i y, Entry_d M i y Q → Row_pr_thread_d I F G b D N A i y) ∧
      ∀ i j y z, M.SuccessorOf j i → Entry_d M i y Q → Entry_d M j z Q →
        Row_pr_advance_d I F G b D V N A E i y z := by
  let ρ : Env M 8 := ⟨Fin.cases F (Fin.cases G (Fin.cases b (Fin.cases D
    (Fin.cases V (Fin.cases N (Fin.cases A (fun _ => E))))))), fun _ => b⟩
  let θ : BinarySchema 8 := {
    body := row_pr_thread_m (.bound 2) (.bound 3) (.bound 4)
      (.bound 5) (.bound 7) (.bound 8) (.bound 1) .newest }
  let φ : UnarySchema 10 := {
    body := row_pr_advance_m (.bound 3) (.bound 4) (.bound 5)
      (.bound 6) (.bound 7) (.bound 8) (.bound 9) (.bound 10) (.bound 2) (.bound 1) .newest }
  have hθ i y : θ.denote ρ i y ↔ Row_pr_thread_d I F G b D N A i y :=
    row_pr_thread_sat_l I hZFC.1 _ _ _ _ _ _ _ _ _
  have hφ i y z : φ.denote ((ρ.push i).push y) z ↔ Row_pr_advance_d I F G b D V N A E i y z :=
    row_pr_advance_sat_l I hZFC.1 _ _ _ _ _ _ _ _ _ _ _ _
  have hβ := h.conditions.1.mem ((h.conditions.2.2 β).mpr ⟨D, hD⟩)
  have htr := ZF.h_transitive_l I hZF hH
  obtain ⟨X, Q, hQ, hz, hv, hs⟩ := ZFC.class_indexed_choice_l I hZFC θ φ ρ hω h.empty ((hθ b x).mpr hx) (by
    intro i j y hiω hj hy
    obtain ⟨α, B, R, hiα, hB, hR, hy⟩ := (hθ i y).mp hy
    obtain ⟨j', hj', hjω⟩ := hω.1.2 i hiω
    have he := hZFC.1.eq_of_same_members j' j (fun t => (hj' t).trans (hj t).symm)
    have hjω := he ▸ hjω
    obtain ⟨γ, _, hjγ⟩ := hA.2.2 j hjω
    have hγδ := h.conditions.1.transitive β ((h.conditions.2.2 β).mpr ⟨D, hD⟩) γ (hi j γ hjγ).2
    obtain ⟨C, hC⟩ := (h.conditions.2.2 γ).mp hγδ
    obtain ⟨T, hT⟩ := (h.relations.2.2 γ).mp hγδ
    obtain ⟨U, hUN, hiU⟩ := hE.2.2 i hiω
    have hαγ := hm i j α γ hj.predecessor_mem hiα hjγ
    have hBN := selem_entry_value_l I hJ htr hZF hω hSub hElem hFN (hi i α hiα).1 h.conditions.2.1.2 hB
    have hRN := selem_entry_value_l I hJ htr hZF hω hSub hElem hGN (hi i α hiα).1 h.relations.2.1.2 hR
    obtain ⟨z, hz, hm⟩ := row_pr_move_l hZFC hω hχ hH hJ hSub hElem (hi j γ hjγ).1 hαγ
      hBN hRN hDN hVN hUN (h.stages α B R hB hR) (h.stages γ C T hC hT).order
      (h.stages β D V hD hV).order (h.links α γ B R C T hB hR hC hT hαγ)
      (h.links γ β C T D V hC hT hD hV (hβ.transitive.memberSubset (hi j γ hjγ).2))
      (hP j γ hjγ α B R C T (hi i α hiα).1 hαγ hB hR hC hT) (hd i U hiU) hy
    exact ⟨z, (hθ j z).mpr ⟨γ, C, T, hjγ, hC, hT, hz⟩,
      (hφ i y z).mpr ⟨j, α, B, R, γ, C, T, U, hj, hiα, hjγ, hB, hR, hC, hT, hiU, hm⟩⟩)
  exact ⟨X, Q, hQ, hz, fun i y hy => (hθ i y).mp (hv i y hy),
    fun i j y z hj hy hz => (hφ i y z).mp (hs i j y z hj hy hz)⟩

end YesMetaZFC.Model.Forcing.Internal
