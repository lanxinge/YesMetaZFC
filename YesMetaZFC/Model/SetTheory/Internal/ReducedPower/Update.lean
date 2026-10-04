import YesMetaZFC.Model.SetTheory.Internal.ReducedPower.Truth
import YesMetaZFC.Model.SetTheory.Internal.Assignment

/-! # 赋值族的逐点单变量更新

见证函数使用规范 Kuratowski 图，赋值仍采用结构码的有序对约定。
更新后的整族由唯一值收集得到，仅需 ZF。
-/
namespace YesMetaZFC.SetTheory.Internal
open Definitional.Project InnerModel
universe u
variable {M : Structure.{u}} {𝒞 : OrderedPairConvention} (I : 𝒞.Interpretation M)

def Rp_update_d (D E V i f W : M.Domain) : Prop := M.IsSetFunctionFromTo I W D E ∧ ∀ d w,
  M.PairMember I d w W ↔ M.mem d D ∧ ∃ v x, M.PairMember I d v V ∧ Rd_entry_d d x f ∧ Senv_update_d I v i x w

def rp_update_m {n} (D E V i f W : Term n) : Formula 1 n := .conj (Formula.isFunctionFromTo 𝒞 W D E)
  (.forallE (.forallE (.iff (Formula.orderedPairMem 𝒞 (.bound 1) .newest W.weaken.weaken)
    (.conj (.mem (.bound 1) D.weaken.weaken) (.existsE (.existsE (.conj
      (Formula.orderedPairMem 𝒞 (.bound 3) (.bound 1) V.weaken.weaken.weaken.weaken) (.conj
        (rd_entry0_m (.bound 3) .newest f.weaken.weaken.weaken.weaken)
        (senv_update_m (𝒞 := 𝒞) (.bound 1) i.weaken.weaken.weaken.weaken .newest (.bound 2))))))))))
derive_free_closed rp_update_m

theorem rp_update_sat_l (hE : Extensional M) {n} (ρ : Env M n) (D E V i f W : Term n) :
    Formula.satisfies ρ (rp_update_m (𝒞 := 𝒞) D E V i f W) ↔
      Rp_update_d I (D.eval ρ) (E.eval ρ) (V.eval ρ) (i.eval ρ) (f.eval ρ) (W.eval ρ) := by
  simp only [rp_update_m, Rp_update_d, Formula.satisfies_conj_iff, Formula.satisfies_isFunctionFromTo_iff I hE,
    Formula.satisfies_forall_iff, Formula.satisfies_iff_iff, Formula.satisfies_orderedPairMem_iff I,
    Formula.satisfies_mem_iff, Formula.satisfies_exists_iff, rd_entry0_sat_l hE,
    senv_update_sat_l I hE, Definitional.Term.eval_weaken]
  rfl

theorem rp_update_exists_l (hZF : M.Models ZF) {ω D Q E V i f} (hE : M.IsFunctionSpace I E ω Q)
    (hV : M.IsSetFunctionFromTo I V D E) (hi : M.mem i ω) (hf : Fn0_d D Q f) : ∃ W, Rp_update_d I D E V i f W := by
  let ρ : Env M 3 := ⟨Fin.cases f (Fin.cases i (fun _ => V)), fun _ => V⟩
  let φ : BinarySchema 3 := { body := .existsE (.existsE (.conj
    (Formula.orderedPairMem 𝒞 (.bound 3) (.bound 1) (.bound 6)) (.conj
      (rd_entry0_m (.bound 3) .newest (.bound 4)) (senv_update_m (𝒞 := 𝒞) (.bound 1) (.bound 5) .newest (.bound 2))))) }
  have sat d w : φ.denote ρ d w ↔ ∃ v x, M.PairMember I d v V ∧ Rd_entry_d d x f ∧ Senv_update_d I v i x w := by
    simp only [φ, BinarySchema.denote, Formula.satisfies_exists_iff, Formula.satisfies_conj_iff,
      Formula.satisfies_orderedPairMem_iff I, rd_entry0_sat_l hZF.1, senv_update_sat_l I hZF.1]
    rfl
  obtain ⟨W, hW, spec⟩ := ZF.exists_setFunctionFromTo_of_denote hZF I φ ρ (source := D) (target := E)
    (fun d hd => by
      obtain ⟨v, hv, hdv⟩ := hV.2.2 d hd
      obtain ⟨x, hx, hdx⟩ := hf.2.1 d hd
      obtain ⟨w, hw, _⟩ := senv_update_exists_l I hZF ((hE v).mp hv) hi hx
      exact ⟨w, (sat d w).mpr ⟨v, x, hdv, hdx, hw⟩⟩)
    (fun d hd w z hw hz => by
      obtain ⟨v, x, hv, hx, hw⟩ := (sat d w).mp hw
      obtain ⟨v', x', hv', hx', hz⟩ := (sat d z).mp hz
      have ev := hV.1.2 d v' v hv' hv
      have ex := hf.2.2 d hd x' (hf.bound_l hx').2 x (hf.bound_l hx).2 hx' hx
      exact senv_update_unique_l I hZF.1 hw (ev ▸ ex ▸ hz))
    (fun d w _ hw => by
      obtain ⟨v, x, hv, hx, hw⟩ := (sat d w).mp hw
      exact (hE w).mpr (hw.function_l I ((hE v).mp (hV.output_mem_of_pairMember hv)) hi (hf.bound_l hx).2))
  exact ⟨W, hW, fun d w => (spec d w).trans (and_congr_right fun _ => sat d w)⟩

def Rp_ex_d (Q E i Z B : M.Domain) : Prop := ∀ v, M.mem v B ↔ M.mem v E ∧
  ∃ x, M.mem x Q ∧ ∃ w, M.mem w Z ∧ Senv_update_d I v i x w

def rp_ex_m {n} (Q E i Z B : Term n) : Formula 1 n := .forallE (.iff (.mem .newest B.weaken)
  (.conj (.mem .newest E.weaken) (Formula.existsMem Q.weaken (Formula.existsMem Z.weaken.weaken
    (senv_update_m (𝒞 := 𝒞) (.bound 2) i.weaken.weaken.weaken (.bound 1) .newest)))))
derive_free_closed rp_ex_m

theorem rp_ex_sat_l (hE : Extensional M) {n} (ρ : Env M n) (Q E i Z B : Term n) :
    Formula.satisfies ρ (rp_ex_m (𝒞 := 𝒞) Q E i Z B) ↔
      Rp_ex_d I (Q.eval ρ) (E.eval ρ) (i.eval ρ) (Z.eval ρ) (B.eval ρ) := by
  simp only [rp_ex_m, Rp_ex_d, Formula.satisfies_forall_iff, Formula.satisfies_iff_iff,
    Formula.satisfies_mem_iff, Formula.satisfies_conj_iff, Formula.satisfies_existsMem_iff,
    senv_update_sat_l I hE, Definitional.Term.eval_weaken]
  rfl

theorem rp_ex_exists_l (hZF : M.Models ZF) (Q E i Z : M.Domain) : ∃ B, Rp_ex_d I Q E i Z B := by
  let ρ : Env M 3 := ⟨Fin.cases Z (Fin.cases i (fun _ => Q)), fun _ => Q⟩
  let φ : UnarySchema 3 := { body := Formula.existsMem (.bound 3) (Formula.existsMem (.bound 2)
    (senv_update_m (𝒞 := 𝒞) (.bound 2) (.bound 4) (.bound 1) .newest)) }
  obtain ⟨B, hB⟩ := ZF.separation_exists_d hZF φ ρ E
  refine ⟨B, fun v => (hB v).trans (and_congr_right fun _ => ?_)⟩
  simp only [φ, Formula.satisfies_existsMem_iff, senv_update_sat_l I hZF.1]
  rfl

/-- 从一个实际见证函数向逐点存在量词传输，不需要选择或滤子公理。 -/
theorem rp_ex_update_l {D Q E U V i f W Z B} (hV : M.IsSetFunctionFromTo I V D E)
    (hf : Fn0_d D Q f) (hW : Rp_update_d I D E V i f W) (hB : Rp_ex_d I Q E i Z B)
    (h : Rp_holds_d I U W Z) : Rp_holds_d I U V B := by
  obtain ⟨A, hA, ht⟩ := h
  refine ⟨A, hA, fun d hd => ?_⟩
  obtain ⟨w, hdw, hw⟩ := ht d hd
  obtain ⟨_, v, x, hdv, hdx, he⟩ := (hW.2 d w).mp hdw
  exact ⟨v, hdv, (hB v).mpr ⟨hV.output_mem_of_pairMember hdv, x, (hf.bound_l hdx).2, w, hw, he⟩⟩

end YesMetaZFC.SetTheory.Internal
