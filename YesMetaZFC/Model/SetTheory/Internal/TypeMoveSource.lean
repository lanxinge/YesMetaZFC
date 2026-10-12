import YesMetaZFC.Model.SetTheory.Internal.OrdinalAdditionSource
import YesMetaZFC.Model.SetTheory.Internal.TypeMove
import YesMetaZFC.Model.SetTheory.Internal.TypeLowerSource

/-! # 在 V(ν+ω) 中统一读取 V(ν+k) 的完整类型

公式自行求出层高、秩层和移动后的元组，只把原名字列及候选类型作为参数。
内部有限长度 k 和元组长度 n 都是对象自然数；读取覆盖原查询域的全部成员。
-/
namespace YesMetaZFC.SetTheory.Internal
open Definitional.Project InnerModel
universe u
variable {M : Structure.{u}}

def tm_type_m {d} (ω C κ k n Z E δ e ν t : Term d) : Formula 1 d := set[d] ⟪∃ β A h,
  ⌜Formula.isOrdinalAddition kpair_convention_l⌝ₚ(β, ⌜ν⌝ₛ, ⌜k⌝ₛ) ∧
  ⌜v_m FlatPairing.convention⌝ₚ(β, A) ∧
  ⌜Formula.isFunctionFromTo FlatPairing.convention⌝ₚ(h, ⌜n⌝ₛ, A) ∧
  ⌜tm_assign0_m⌝ₚ(⌜ω⌝ₛ, ⌜Z⌝ₛ, A, ⌜e⌝ₛ, ⌜ν⌝ₛ, ⌜E⌝ₛ, ⌜n⌝ₛ, h) ∧
  ⌜tf_lower_type_m⌝ₚ(⌜ω⌝ₛ, ⌜C⌝ₛ, ⌜κ⌝ₛ, ⌜n⌝ₛ, A, h, ⌜δ⌝ₛ, ⌜t⌝ₛ)⟫
derive_free_closed tm_type_m

/-- 第零坐标为移动高度，其余十个坐标为共同参数。 -/
def tm_type_f : Formula 1 11 := tm_type_m (.bound 1) (.bound 2) (.bound 3) (.bound 4)
  (.bound 5) (.bound 6) (.bound 7) (.bound 8) (.bound 9) .newest (.bound 10)

theorem tm_type_closed_l : tm_type_f.FreeClosed := by
  apply tm_type_m_freeClosed <;> rfl

variable (hZF : M.Models ZF) {ω η Y : M.Domain} (hω : M.IsOmega ω)
  (hη : M.IsLimitOrdinal η) (hY : V_d (kp_pair_l (ZF.modelsKP hZF)) η Y) (hωY : M.mem ω Y)
local notation "Q" => kp_pair_l (ZF.modelsKP hZF)
local notation "K" => fp_interpretation_l (ZF.models_kpi_l hZF)
local notation "T" => ZF.v_transitive_l Q hZF hY
local notation "ny" => Nonempty.intro (Subtype.mk ω hωY)
local notation "N" => rt_model_l Y ny
local notation "J" => rt_pair_l T ny (And.left hZF) (sc_v_pair_l hZF hη hY)
local notation "L" => fp_rank_interpretation_l Q hZF hω hY hωY

include hω hη hY in
theorem tm_type_source_l (C κ k n Z E δ e ν t : (N).Domain) {ξ β A B U D c R s : M.Domain}
    (hν : M.IsOrdinal ν.val) (hk : M.mem k.val ω)
    (sum : M.IsOrdinalAddition Q β ν.val k.val) (hβ : M.mem β η)
    (hA : V_d Q β A) (hων : M.MemberSubset ω β) (hκA : M.mem κ.val A)
    (hC : V_d Q ξ C.val) (hξ : M.IsLimitOrdinal ξ) (hωξ : M.mem ω ξ) (hκξ : M.mem κ.val ξ)
    (hB : V_d Q κ.val B) (constants : ∀ x, M.mem x U ↔ M.mem x B ∨ x = κ.val)
    (pool : Tt_pool_d Q ω n.val U D) (hm : Smem_d Q c A R) (hn : M.mem n.val ω)
    (names : Fn0_d n.val Z.val E.val) (assign : Tn_assign_d e.val e.val ν.val E.val s)
    (tuple : Fn0_d n.val A s) (point : M.mem δ.val A) :
    Formula.satisfies (⟨Fin.cases ν (Fin.cases ⟨ω, hωY⟩ (Fin.cases C (Fin.cases κ (Fin.cases k
      (Fin.cases n (Fin.cases Z (Fin.cases E (Fin.cases δ (Fin.cases e (fun _ => t)))))))))), fun _ => ν⟩ : Env N 11)
      tm_type_f ↔ Tt_truth_d Q ω c n.val s δ.val D t.val := by
  let ρ : Env N 11 := ⟨Fin.cases ν (Fin.cases ⟨ω, hωY⟩ (Fin.cases C (Fin.cases κ (Fin.cases k
    (Fin.cases n (Fin.cases Z (Fin.cases E (Fin.cases δ (Fin.cases e (fun _ => t)))))))))), fun _ => ν⟩
  have ext := rt_model_ext_l hZF.1 T ny
  have add (b : (N).Domain) : (N).IsOrdinalAddition J b ν k ↔ b.val = β := by
    obtain ⟨a, _, unique⟩ := ZF.ordinalAddition_existsUnique hZF Q ν.val (hω.members_areOrdinals hZF k.val hk)
    exact (rt_oa_l hZF hη hY ny ν k b hν).trans
      ⟨fun hb => (unique b.val hb).trans (unique β sum).symm, fun eq => eq.symm ▸ sum⟩
  have layer (b V : (N).Domain) (eq : b.val = β) : V_d L b V ↔ V.val = A :=
    (rt_fp_v_l Q hZF hω hY hωY b V).trans
      ⟨fun hv => ZF.v_unique_l Q hZF (eq ▸ hv) hA, fun ev => ev.symm ▸ eq.symm ▸ hA⟩
  have fn := rt_fp_function_from_l Q hZF hω hY hωY
  have mat (b V h : (N).Domain) : Formula.satisfies (((ρ.push b).push V).push h)
      (tm_assign0_m (.bound 4) (.bound 9) (.bound 1) (.bound 12) (.bound 3) (.bound 10) (.bound 8) .newest) ↔
      Tm_assign_d K Z.val V.val e.val ν.val E.val n.val h.val :=
    (rt_model_delta_l T ny (tm_assign0_delta_l ..) _).trans
      (tm_assign0_sat_l (ZF.models_kpi_l hZF) _ (.bound 4) (.bound 9) (.bound 1)
        (.bound 12) (.bound 3) (.bound 10) (.bound 8) .newest hω)
  have query (b V h : (N).Domain) (eq : V.val = A) (agree : Sx_graph_d Q K s h.val) :=
    tf_lower_type_source_l hZF hω hY hωY (((ρ.push b).push V).push h)
      (.bound 4) (.bound 5) (.bound 6) (.bound 8) (.bound 1) .newest (.bound 11) (.bound 13) rfl
      hC hξ hωξ hκξ (eq.symm ▸ hA) hων (eq.symm ▸ hκA) hB constants pool
      (eq.symm ▸ hm) hn (eq.symm ▸ tuple) (eq.symm ▸ point) agree
  change Formula.satisfies ρ tm_type_f ↔ _
  simp only [tm_type_f, tm_type_m, Formula.satisfies_exists_iff, Formula.satisfies_conj_iff,
    Formula.satisfies_isOrdinalAddition_iff J ext, v_sat_l L ext,
    Formula.satisfies_isFunctionFromTo_iff L ext, Definitional.Term.eval_weaken, Definitional.Term.eval_newest]
  constructor
  · rintro ⟨b, V, h, hb, hv, hh, matrix, truth⟩
    have eq := (layer b V ((add b).mp hb)).mp hv
    have flat := eq ▸ (fn h n V).mp hh
    have agree := (tm_assign_iff_l hZF names assign tuple flat).mp (eq ▸ (mat b V h).mp matrix)
    exact (query b V h eq agree).mp truth
  · intro truth
    let b : (N).Domain := ⟨β, ZF.v_ordinal_mem_l Q hZF hY hβ⟩
    let V : (N).Domain := ⟨A, ZF.v_mem_l Q hZF hA hY hβ⟩
    obtain ⟨h, flat, agree⟩ := fn_recode_l Q K hZF (fn0_function_l (ZF.modelsKP hZF) tuple)
    have hhY := ZF.v_subset_mem_l Q hZF hY V.property
      (fp_function_rank_l Q hZF hω hA hων (fun i hi => ZF.v_ordinal_mem_l Q hZF hA (hων i (hω.transitive hZF _ hn i hi))) flat)
    let h' : (N).Domain := ⟨h, hhY⟩
    exact ⟨b, V, h', (add b).mpr rfl, (layer b V rfl).mpr rfl, (fn h' n V).mpr flat,
      (mat b V h').mpr ((tm_assign_iff_l hZF names assign tuple flat).mpr agree), (query b V h' rfl agree).mpr truth⟩

end YesMetaZFC.SetTheory.Internal
