import YesMetaZFC.Model.SetTheory.Internal.FlatTruthSyntax
import YesMetaZFC.SetTheory.FlatPairing.RankObjects

/-! # 平坦真值方程与原满足关系一致

原程序的内部强归纳同时处理全部前缀编码。存在量词的更新赋值重新编码于
同一秩层；因而新方程不依赖外部良基性，也没有额外的真值或编码存在假设。
-/
namespace YesMetaZFC.SetTheory.Internal
open Definitional.Project
universe u
variable {M : Structure.{u}} {𝒞 : OrderedPairConvention} (I : 𝒞.Interpretation M) (hZF : M.Models ZF)
local notation "J" => fp_interpretation_l (ZF.models_kpi_l hZF)

/-- 对严格较早行的一次语义归纳步，供存在性和正确性两处共用。 -/
theorem ft_step_l {ω ν X R E F n b H T r c f p : M.Domain} (hω : M.IsOmega ω)
    (hV : V_d I ν X) (hων : M.MemberSubset ω ν) (hF : Sfm_d J ω n F)
    (hE : M.IsFunctionSpace J E ω X) (hH : Seval_d J X R E F n H)
    (hc : M.PairMember J r c F) (hf : M.mem f E) (hp : Fs_code_d J ω X f b p)
    (read : ∀ s, M.mem s r → ∀ g q, M.mem g E → Fs_code_d J ω X g b q →
      (M.PairMember J s q T ↔ Ssat_d J X R E F n s g)) :
    Ft_node_d J ω X R b T c f p ↔ Ssat_d J X R E F n r f := by
  rcases hF.2.2 r c hc with ⟨i, j, code, _, _⟩ | ⟨i, j, code, _, _⟩ |
    ⟨i, j, code, hi, hj⟩ | ⟨i, j, code, hi, hj⟩
  · rw [ft_node_decode_l J (ZF.modelsKP hZF) 0 code, ssat_op_l J hZF hF hH hc 0 code f]
    exact ⟨fun h => ⟨hf, h⟩, And.right⟩
  · rw [ft_node_decode_l J (ZF.modelsKP hZF) 1 code, ssat_op_l J hZF hF hH hc 1 code f]
    exact ⟨fun h => ⟨hf, h⟩, And.right⟩
  · rw [ft_node_decode_l J (ZF.modelsKP hZF) 2 code, ssat_nor_l J hZF hF hH hc code hf]
    exact not_congr (or_congr (read i hi f p hf hp) (read j hj f p hf hp))
  · rw [ft_node_decode_l J (ZF.modelsKP hZF) 3 code, ssat_exists_l J hZF hF hH hc code hf]
    constructor
    · rintro ⟨x, g, q, hx, update, cq, truth⟩
      have hg := (hE g).mpr (update.function_l J ((hE f).mp hf) hi hx)
      exact ⟨x, g, hx, update, (read j hj g q hg cq).mp truth⟩
    · rintro ⟨x, g, hx, update, truth⟩
      have hg := update.function_l J ((hE f).mp hf) hi hx
      obtain ⟨q, _, cq⟩ := fp_finite_rank_l I hZF hω hV hων hg (hp.bound_l J).1
      exact ⟨x, g, q, hx, update, cq, (read j hj g q ((hE g).mpr hg) cq).mpr truth⟩

/-- 任意满足四条平坦方程的实际表，都等于原内部满足关系。 -/
theorem Ft_eval_d.correct_l {ω ν X R E F n b T r f p : M.Domain} (hω : M.IsOmega ω)
    (hV : V_d I ν X) (hων : M.MemberSubset ω ν) (hF : Sfm_d J ω n F)
    (hE : M.IsFunctionSpace J E ω X) (h : Ft_eval_d J ω X R b F n T)
    (hr : M.mem r n) (hf : M.mem f E) (hp : Fs_code_d J ω X f b p) :
    M.PairMember J r p T ↔ Ssat_d J X R E F n r f := by
  obtain ⟨H, hH⟩ := seval_exists_l J hZF X R E F hF.2.1.1
  let ρ : Env M 8 := ⟨Fin.cases T (Fin.cases b (Fin.cases n (Fin.cases F
    (Fin.cases E (Fin.cases R (Fin.cases X (fun _ => ω))))))), fun _ => X⟩
  let φ : UnarySchema 8 := { body := .forallE (.forallE (.imp (.mem (.bound 1) (.bound 7)) (.imp
    (fs_code_m (𝒞 := FlatPairing.convention) (.bound 10) (.bound 9) (.bound 1) (.bound 4) .newest) (.iff
    (Formula.orderedPairMem FlatPairing.convention (.bound 2) .newest (.bound 3))
    (ssat_m (𝒞 := FlatPairing.convention) (.bound 9) (.bound 8) (.bound 7) (.bound 6) (.bound 5) (.bound 2) (.bound 1)))))) }
  have sat s : φ.denote ρ s ↔ ∀ g q, M.mem g E → Fs_code_d J ω X g b q →
      (M.PairMember J s q T ↔ Ssat_d J X R E F n s g) := by
    simp only [φ, UnarySchema.denote, Formula.satisfies_forall_iff, Formula.satisfies_imp_iff,
      Formula.satisfies_mem_iff, fs_code_sat_l J hZF.1, Formula.satisfies_iff_iff,
      Formula.satisfies_orderedPairMem_iff J, ssat_sat_l J hZF.1]; rfl
  apply (sat r).mp (sfm_induction_l J hZF hF φ ρ ?_ hr) f p hf hp
  intro s hs ih
  apply (sat s).mpr
  intro g q hg cq
  obtain ⟨c, hc⟩ := (hF.2.1.2.2 s).mp hs
  exact (h.2.2 s c g q hc ((hE g).mp hg) cq).trans
    (ft_step_l I hZF hω hV hων hF hE hH hc hg cq (fun t ht => (sat t).mp (ih t ht)))

/-- 平坦表由原满足关系分离得到，且整个表只占用一个后继秩层。 -/
theorem ft_eval_rank_l {ω ν μ X Y R E F n b : M.Domain} (hω : M.IsOmega ω)
    (hV : V_d I ν X) (hW : V_d I μ Y) (hs : M.SuccessorOf μ ν) (hων : M.MemberSubset ω ν)
    (hF : Sfm_d J ω n F) (hb : Sbound_d J F b) (hE : M.IsFunctionSpace J E ω X) :
    ∃ T, M.mem T Y ∧ Ft_eval_d J ω X R b F n T := by
  obtain ⟨H, hH⟩ := seval_exists_l J hZF X R E F hF.2.1.1
  let ρ : Env M 7 := ⟨Fin.cases b (Fin.cases n (Fin.cases F (Fin.cases E
    (Fin.cases R (Fin.cases X (fun _ => ω)))))), fun _ => X⟩
  let φ : BinarySchema 7 := { body := .conj (.mem (.bound 1) (.bound 3)) (.existsE (.conj
    (.mem .newest (.bound 6)) (.conj
    (fs_code_m (𝒞 := FlatPairing.convention) (.bound 9) (.bound 8) .newest (.bound 3) (.bound 1))
    (ssat_m (𝒞 := FlatPairing.convention) (.bound 8) (.bound 7) (.bound 6) (.bound 5) (.bound 4) (.bound 2) .newest)))) }
  have sat r p : φ.denote ρ r p ↔ M.mem r n ∧
      ∃ f, M.mem f E ∧ Fs_code_d J ω X f b p ∧ Ssat_d J X R E F n r f := by
    simp only [φ, BinarySchema.denote, Formula.satisfies_conj_iff, Formula.satisfies_mem_iff,
      Formula.satisfies_exists_iff, fs_code_sat_l J hZF.1, ssat_sat_l J hZF.1]; rfl
  obtain ⟨T, hT, val⟩ := ZF.exists_setRelationOn_of_denote hZF J φ ρ X
  have read r p : M.PairMember J r p T ↔ M.mem r n ∧
      ∃ f, M.mem f E ∧ Fs_code_d J ω X f b p ∧ Ssat_d J X R E F n r f := by
    refine (val r p).trans ⟨fun h => (sat r p).mp h.2.2, ?_⟩
    intro h
    obtain ⟨hr, f, hf, cp, ht⟩ := h
    have hrω := (hω.isOrdinal hZF).transitive n hF.1 r hr
    exact ⟨ZF.v_ordinal_mem_l I hZF hV (hων r hrω), (cp.bound_l J).2, (sat r p).mpr ⟨hr, f, hf, cp, ht⟩⟩
  have truth r (hr : M.mem r n) f p (hf : M.mem f E) (cp : Fs_code_d J ω X f b p) :
      M.PairMember J r p T ↔ Ssat_d J X R E F n r f := by
    refine (read r p).trans ⟨?_, fun h => ⟨hr, f, hf, cp, h⟩⟩
    rintro ⟨_, g, hg, cq, h⟩
    have agree := (cq.prefix_l J hZF hω ((hE g).mp hg) ((hE f).mp hf) cp).mp rfl
    exact (ssat_agree_l J hZF hF hb hE hr hg hf agree).mp h
  refine ⟨T, (ZF.v_successor_l I hZF hV hW hs T).mpr (fp_relation_rank_l I hZF hω hV hων hT),
    hT.1, ?_, ?_⟩
  · intro r p hp
    obtain ⟨hr, f, hf, cp, _⟩ := (read r p).mp hp
    exact ⟨hr, f, (hE f).mp hf, cp⟩
  · intro r c f p hc hf cp
    have hr := (hF.2.1.2.2 r).mpr ⟨c, hc⟩
    exact (truth r hr f p ((hE f).mpr hf) cp).trans
      (ft_step_l I hZF hω hV hων hF hE hH hc ((hE f).mpr hf) cp
        (fun s hs => truth s (hF.2.1.1.transitive r hr s hs))).symm

end YesMetaZFC.SetTheory.Internal
