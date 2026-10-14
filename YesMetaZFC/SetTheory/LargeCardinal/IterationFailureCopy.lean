import YesMetaZFC.SetTheory.LargeCardinal.IterationCopyCut
import YesMetaZFC.SetTheory.LargeCardinal.IterationAttemptRegular
import YesMetaZFC.SetTheory.CumulativeRegularCover
import YesMetaZFC.SetTheory.Card.FiniteParameters

/-! # 返回失败自动产生正规根上的下降 nice 复制树

公共可数载体、联合尝试秩、容纳全部参数的正规根、完整复制历史及下降
秩段列均在本定理中构造。入口只保留原可数树及其到给定秩层的初等嵌入。
-/
namespace YesMetaZFC.SetTheory.LargeCardinal
open Definitional.Project InnerModel Internal
universe u
variable {M : Structure.{u}} (hZFC : M.Models ZFC)
local notation "hZF" => ZFC.models_zf_l hZFC
local notation "I" => kp_pair_l (ZF.modelsKP hZF)

theorem it_pnice_failure_copy_l {ω c X R T Q G E L o θ A a S π : M.Domain}
    (nice : It_pnice_d hZF ω c ω T Q G E L) (mx : Smem_d I c X R)
    (count : M.CardinalLessOrEqual I X ω) (ho : ∀ x, ¬ M.mem x o)
    (rank : V_d I θ A) (ma : Smem_d I a A S)
    (embed : Smap_d I ω c a X A π) (bad : ¬ It_return_d hZF ω o T Q G a A π) :
    ∃ δ Z z Rz Q' G' E' L' D N, M.IsRegularCardinal I δ ∧ M.mem ω δ ∧ V_d I δ Z ∧ Smem_d I z Z Rz ∧
      It_pnice_d hZF ω z ω T Q' G' E' L' ∧
      (∀ i a Y S, Rd_entry_d i a Q' → Smem_d I a Y S → Sc_power_d Y) ∧ It_cut_d hZF ω ω Q' E' D N ∧
      (∀ β, Rd_entry_d o β D → M.IsRegularCardinal I β ∧ M.mem θ β) ∧
      (∀ i p, Rd_entry_d i p E' → (∀ x, ¬ M.mem x p) → Rd_entry_d i p E) ∧
      ∀ k l g β γ, It_map_d G' k l g → M.mem k l → Rd_entry_d k β D → Rd_entry_d l γ D →
        ∃ ε, Rd_entry_d β ε g ∧ M.mem γ ε := by
  have hω := nice.tree.omega
  obtain ⟨X₀, R₀, K, mx₀, source⟩ := nice.tree.sources o c (nice.tree.root o ho)
  obtain ⟨ex, er⟩ := smdl_unique_l I mx₀.1 mx.1
  subst X₀ R₀
  -- 初等像的配对闭包迫使原目标高度为极限，无需另作假设。
  have ht := ZF.v_transitive_l I hZF rank
  have hωA := embed.1.1.output_mem_of_pairMember (embed.omega_l I hZF hω source.transitive ht mx ma source.omega_mem)
  have hθ := v_ordinal_l I rank
  have algebra := (source.theory.map_l I hZF hω source.transitive ht mx ma embed).algebra
  have limit : M.IsLimitOrdinal θ := by
    refine ⟨hθ, ⟨ω, ZF.v_ordinal_height_l hZF rank (hω.isOrdinal hZF) hωA⟩, ?_⟩
    intro β hβ
    have hβA := ZF.v_ordinal_mem_l I hZF rank hβ
    obtain ⟨p, hp, pair⟩ := algebra.pair β β hβA hβA
    obtain ⟨γ, W, hγ, vw, sub⟩ := (ZF.v_unfold_l I hZF rank p).mp hp
    exact ⟨γ, hγ, ZF.v_ordinal_height_l hZF vw (hθ.mem hβ) (sub β ((pair β).mpr (Or.inl rfl)))⟩
  obtain ⟨C, ι, trans, inj, cover⟩ := it_countable_cover_l hZFC nice.tree mx.1 count
  obtain ⟨U, B, W, F, en, space, regular⟩ := ja_failure_l hZFC nice.tree mx.1 count ho ma
    (fn0_of_function_l (ZF.modelsKP hZF) embed.1.1) limit.1 bad
  let v : Fin 12 → M.Domain := Fin.cases C (Fin.cases ι (Fin.cases T (Fin.cases Q (Fin.cases G
    (Fin.cases U (Fin.cases π (Fin.cases A (Fin.cases θ (Fin.cases B (Fin.cases W (fun _ => F)))))))))))
  obtain ⟨P, _, ps⟩ := ZF.finite_params_l I hZF hω v
  obtain ⟨δ, Z, hδ, above, outer, hP⟩ := ZFC.v_regular_cover_l I hZFC hω P
  have owned i : M.mem (v i) Z := ZF.v_transitive_l I hZF outer P hP (v i) ((ps (v i)).mpr ⟨i, rfl⟩)
  have hθ : M.mem θ δ := ZF.v_ordinal_height_l hZF outer limit.1 (owned 8)
  obtain ⟨B₀, F₀, hB₀, hF₀, cert, _⟩ := vr_source_l hZF outer hδ.isLimitOrdinal hθ rank
  have relative : Vr_d Z θ A := ⟨B₀, F₀, hB₀, hF₀, fun t _ => cert t⟩
  obtain ⟨z, row⟩ := ic_initial_row_l hZFC source mx ma embed above hδ outer (owned 7) relative limit
  obtain ⟨H, Q', G', _, _, hist, _, start, _⟩ := row.copy_l hZFC nice ho
  obtain ⟨E', L', D, N, copied, cut, root, pads, drop⟩ := hist.rank_cut_l hZF nice en start ho ma space regular
    (owned 8) (owned 11) (owned 0) (owned 1) trans inj cover
    (owned 2) (owned 3) (owned 4) (owned 5) (owned 6) (owned 9) (owned 10)
  obtain ⟨_, _, Rz, _, _, _, _, _, _, mz, _⟩ := row
  refine ⟨δ, Z, z, Rz, Q', G', E', L', D, N, hδ, above, outer, mz, copied, ?_, cut, root, pads, drop⟩
  intro i a Y S ha my
  obtain ⟨_, _, _, _, a₀, Y₀, _, _, _, ha₀, row⟩ := hist.at_l hZF ((hist.diagram.model_domain i).mpr ⟨a, ha⟩)
  have eq := hist.diagram.model_function.2 i a₀ a ha₀ ha
  subst a₀
  obtain ⟨_, _, _, _, _, _, _, _, _, model, _, _, full, _⟩ := row
  obtain ⟨rfl, _⟩ := smdl_unique_l I model.1 my.1
  exact full.power

end YesMetaZFC.SetTheory.LargeCardinal
