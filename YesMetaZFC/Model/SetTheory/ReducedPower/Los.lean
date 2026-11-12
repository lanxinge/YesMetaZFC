import YesMetaZFC.Model.SetTheory.ReducedPower.SourceModel
import YesMetaZFC.Model.SetTheory.Internal.Theory
import YesMetaZFC.SetTheory.DependentChoice

/-! # 赋值族在超滤意义下的真值

真值由实际大集合承载，逆像由分离构造。合取只用共同细化，否定只对容许代数中
的真值逆像应用二择；完整幂集版本由相对版本实例化。这里不使用见证选择。
-/
namespace YesMetaZFC.SetTheory.Internal
open Definitional.Project
universe u
variable {M : Structure.{u}} {𝒞 : OrderedPairConvention} (I : 𝒞.Interpretation M)

def Rp_holds_d (U V Z : M.Domain) : Prop := ∃ A, M.mem A U ∧ ∀ d, M.mem d A →
  ∃ v, M.PairMember I d v V ∧ M.mem v Z

def rp_holds_m {d} (U V Z : Term d) : Formula 1 d := Formula.existsMem U (Formula.forallMem .newest
  (.existsE (.conj (Formula.orderedPairMem 𝒞 (.bound 1) .newest V.weaken.weaken.weaken)
    (.mem .newest Z.weaken.weaken.weaken))))
derive_free_closed rp_holds_m

theorem rp_holds_sat_l {d} (ρ : Env M d) (U V Z : Term d) :
    Formula.satisfies ρ (rp_holds_m (𝒞 := 𝒞) U V Z) ↔ Rp_holds_d I (U.eval ρ) (V.eval ρ) (Z.eval ρ) := by
  simp only [rp_holds_m, Rp_holds_d, Formula.satisfies_existsMem_iff, Formula.satisfies_forallMem_iff,
    Formula.satisfies_exists_iff, Formula.satisfies_conj_iff, Formula.satisfies_orderedPairMem_iff I,
    Formula.satisfies_mem_iff, Definitional.Term.eval_weaken]
  rfl

theorem Rp_holds_d.mono_l {U V Z T} (h : Rp_holds_d I U V Z) (hs : M.MemberSubset Z T) : Rp_holds_d I U V T :=
  h.imp fun _ ha => ⟨ha.1, fun d hd => (ha.2 d hd).imp fun v hv => ⟨hv.1, hs v hv.2⟩⟩

def Rp_trace_d (D V Z A : M.Domain) : Prop := ∀ d, M.mem d A ↔
  M.mem d D ∧ ∃ v, M.PairMember I d v V ∧ M.mem v Z

def rp_trace_m {n} (D V Z A : Term n) : Formula 1 n := .forallE (.iff (.mem .newest A.weaken)
  (.conj (.mem .newest D.weaken) (.existsE (.conj
    (Formula.orderedPairMem 𝒞 (.bound 1) .newest V.weaken.weaken) (.mem .newest Z.weaken.weaken)))))
derive_free_closed rp_trace_m

theorem rp_trace_sat_l {n} (ρ : Env M n) (D V Z A : Term n) :
    Formula.satisfies ρ (rp_trace_m (𝒞 := 𝒞) D V Z A) ↔
      Rp_trace_d I (D.eval ρ) (V.eval ρ) (Z.eval ρ) (A.eval ρ) := by
  simp only [rp_trace_m, Rp_trace_d, Formula.satisfies_forall_iff, Formula.satisfies_iff_iff,
    Formula.satisfies_mem_iff, Formula.satisfies_conj_iff, Formula.satisfies_exists_iff,
    Formula.satisfies_orderedPairMem_iff I, Definitional.Term.eval_weaken]
  rfl

theorem rp_trace_exists_l (hZF : M.Models ZF) (D V Z : M.Domain) : ∃ A, Rp_trace_d I D V Z A := by
  let ρ : Env M 2 := ⟨Fin.cases Z (fun _ => V), fun _ => V⟩
  let φ : UnarySchema 2 := { body := .existsE (.conj (Formula.orderedPairMem 𝒞 (.bound 1) .newest (.bound 3))
    (.mem .newest (.bound 2))) }
  obtain ⟨A, hA⟩ := ZF.separation_exists_d hZF φ ρ D
  refine ⟨A, fun d => ?_⟩
  rw [hA d]
  simp only [φ, Formula.satisfies_exists_iff, Formula.satisfies_conj_iff,
    Formula.satisfies_orderedPairMem_iff I, Formula.satisfies_mem_iff]
  rfl

theorem rp_trace_member_l {D P U V Z A} (hU : FilterZF.Rel_ultra_d (ℳ := M) D P U)
    (hA : Rp_trace_d I D V Z A) (ha : M.mem A P) : M.mem A U ↔ Rp_holds_d I U V Z := by
  refine ⟨fun h => ⟨A, h, fun d hd => ((hA d).mp hd).2⟩, ?_⟩
  rintro ⟨B, hBU, hB⟩
  exact hU.upward B A hBU ha (fun d hd => (hA d).mpr ⟨hU.base.bounds B hBU d hd, hB d hd⟩)

theorem rp_holds_conj_l {D U V Z T B} (hU : FilterZF.Base_d (ℳ := M) D U) (hV : M.IsSetFunction I V)
    (hB : ∀ v, M.mem v B ↔ M.mem v Z ∧ M.mem v T) : Rp_holds_d I U V B ↔ Rp_holds_d I U V Z ∧ Rp_holds_d I U V T := by
  refine ⟨fun h => ⟨h.mono_l I (fun v hv => ((hB v).mp hv).1), h.mono_l I (fun v hv => ((hB v).mp hv).2)⟩, ?_⟩
  rintro ⟨⟨A, hAU, hA⟩, ⟨C, hCU, hC⟩⟩
  obtain ⟨E, hEU, hEA, hEC⟩ := hU.meet A C hAU hCU
  refine ⟨E, hEU, fun d hd => ?_⟩
  obtain ⟨v, hv, hvZ⟩ := hA d (hEA d hd)
  obtain ⟨w, hw, hwT⟩ := hC d (hEC d hd)
  exact ⟨v, hv, (hB v).mpr ⟨hvZ, hV.2 d w v hw hv ▸ hwT⟩⟩

theorem rp_holds_relative_not_l {D E P U V Z T A B} (hU : FilterZF.Rel_ultra_d (ℳ := M) D P U)
    (hV : M.IsSetFunctionFromTo I V D E) (hT : ∀ v, M.mem v T ↔ M.mem v E ∧ ¬ M.mem v Z)
    (hA : Rp_trace_d I D V Z A) (hB : Rp_trace_d I D V T B) (ha : M.mem A P) (hb : M.mem B P) :
    Rp_holds_d I U V T ↔ ¬ Rp_holds_d I U V Z := by
  have comp d : M.mem d B ↔ M.mem d D ∧ ¬ M.mem d A := by
    rw [hB d]
    constructor
    · rintro ⟨hd, v, hv, hvT⟩
      refine ⟨hd, fun hdA => ?_⟩
      obtain ⟨_, w, hw, hwZ⟩ := (hA d).mp hdA
      exact ((hT v).mp hvT).2 (hV.1.2 d w v hw hv ▸ hwZ)
    · rintro ⟨hd, hn⟩
      obtain ⟨v, hvE, hv⟩ := hV.2.2 d hd
      exact ⟨hd, v, hv, (hT v).mpr ⟨hvE, fun hvZ => hn ((hA d).mpr ⟨hd, v, hv, hvZ⟩)⟩⟩
  exact (rp_trace_member_l I hU hB hb).symm.trans
    ((hU.complement_l ha hb comp).trans (not_congr (rp_trace_member_l I hU hA ha)))

theorem rp_holds_not_l (hZF : M.Models ZF) {D E U V Z T} (hU : FilterZF.Maximal_d (ℳ := M) D U)
    (hV : M.IsSetFunctionFromTo I V D E) (hT : ∀ v, M.mem v T ↔ M.mem v E ∧ ¬ M.mem v Z) :
    Rp_holds_d I U V T ↔ ¬ Rp_holds_d I U V Z := by
  obtain ⟨P, hP⟩ := ZF.exists_powerSet hZF D
  obtain ⟨A, hA⟩ := rp_trace_exists_l I hZF D V Z
  obtain ⟨B, hB⟩ := rp_trace_exists_l I hZF D V T
  exact rp_holds_relative_not_l I (FilterZF.maximal_relative_l (ZF.modelsKP hZF) hU hP) hV hT hA hB
    ((hP A).mpr fun d hd => ((hA d).mp hd).1) ((hP B).mpr fun d hd => ((hB d).mp hd).1)

theorem rp_holds_nor_l (hZF : M.Models ZF) {D E U V Z T B} (hU : FilterZF.Maximal_d (ℳ := M) D U)
    (hV : M.IsSetFunctionFromTo I V D E) (hB : ∀ v, M.mem v B ↔ M.mem v E ∧ ¬ (M.mem v Z ∨ M.mem v T)) :
    Rp_holds_d I U V B ↔ ¬ (Rp_holds_d I U V Z ∨ Rp_holds_d I U V T) := by
  obtain ⟨A, hA⟩ := KP.difference_exists_d (ZF.modelsKP hZF) Z E
  obtain ⟨C, hC⟩ := KP.difference_exists_d (ZF.modelsKP hZF) T E
  have spec v : M.mem v B ↔ M.mem v A ∧ M.mem v C := (hB v).trans (by
    rw [hA v, hC v]
    exact ⟨fun ⟨hv, hn⟩ => ⟨⟨hv, fun hz => hn (Or.inl hz)⟩, hv, fun ht => hn (Or.inr ht)⟩,
      fun ⟨⟨hv, hz⟩, _, ht⟩ => ⟨hv, fun h => h.elim hz ht⟩⟩)
  exact (rp_holds_conj_l I hU.1.base_l hV.1 spec).trans
    ((and_congr (rp_holds_not_l I hZF hU hV hA) (rp_holds_not_l I hZF hU hV hC)).trans
      ⟨fun ⟨hz, ht⟩ h => h.elim hz ht, fun h => ⟨fun hz => h (Or.inl hz), fun ht => h (Or.inr ht)⟩⟩)

end YesMetaZFC.SetTheory.Internal

/-! ## 赋值族的逐点单变量更新

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

/-! ## 从逐列代表函数读取商赋值

赋值族 V 的每列是一个实际 D→Q 函数，投影到对应等价类即得到商赋值。
列函数唯一，故整个构造使用 ZF 的唯一值收集，不需要选择代表元。
-/
namespace YesMetaZFC.SetTheory.Internal
open Definitional.Project InnerModel
universe u
variable {M : Structure.{u}} {𝒞 : OrderedPairConvention} (I : 𝒞.Interpretation M)

def Rp_column_d (D V i f : M.Domain) : Prop := ∀ d, M.mem d D → ∀ v, M.PairMember I d v V →
  ∀ x, Rd_entry_d d x f ↔ M.PairMember I i x v

def rp_column_m {n} (D V i f : Term n) : Formula 1 n := Formula.forallMem D (.forallE
  (.imp (Formula.orderedPairMem 𝒞 (.bound 1) .newest V.weaken.weaken) (.forallE
    (.iff (rd_entry0_m (.bound 2) .newest f.weaken.weaken.weaken)
      (Formula.orderedPairMem 𝒞 i.weaken.weaken.weaken .newest (.bound 1))))))
derive_free_closed rp_column_m

theorem rp_column_sat_l (hE : Extensional M) {n} (ρ : Env M n) (D V i f : Term n) :
    Formula.satisfies ρ (rp_column_m (𝒞 := 𝒞) D V i f) ↔
      Rp_column_d I (D.eval ρ) (V.eval ρ) (i.eval ρ) (f.eval ρ) := by
  simp only [rp_column_m, Rp_column_d, Formula.satisfies_forallMem_iff, Formula.satisfies_forall_iff,
    Formula.satisfies_imp_iff, Formula.satisfies_orderedPairMem_iff I, Formula.satisfies_iff_iff,
    rd_entry0_sat_l hE, Definitional.Term.eval_weaken]
  rfl

theorem rp_column_exists_l (hZF : M.Models ZF) {ω D Q E V i} (hE : M.IsFunctionSpace I E ω Q)
    (hV : M.IsSetFunctionFromTo I V D E) (hi : M.mem i ω) : ∃ f, Fn0_d D Q f ∧ Rp_column_d I D V i f := by
  let ρ : Env M 2 := ⟨Fin.cases i (fun _ => V), fun _ => V⟩
  let φ : BinarySchema 2 := { body := .existsE (.conj
    (Formula.orderedPairMem 𝒞 (.bound 2) .newest (.bound 4)) (Formula.orderedPairMem 𝒞 (.bound 3) (.bound 1) .newest)) }
  have sat d x : φ.denote ρ d x ↔ ∃ v, M.PairMember I d v V ∧ M.PairMember I i x v := by
    simp only [φ, BinarySchema.denote, Formula.satisfies_exists_iff, Formula.satisfies_conj_iff, Formula.satisfies_orderedPairMem_iff I]
    rfl
  obtain ⟨f, hf, spec⟩ := ZF.exists_setFunctionFromTo_of_denote hZF (kp_pair_l (ZF.modelsKP hZF)) φ ρ
    (source := D) (target := Q) (fun d hd => by
      obtain ⟨v, hv, hdv⟩ := hV.2.2 d hd
      obtain ⟨x, _, hix⟩ := ((hE v).mp hv).2.2 i hi
      exact ⟨x, (sat d x).mpr ⟨v, hdv, hix⟩⟩)
    (fun d _ x y hx hy => by
      obtain ⟨v, hdv, hix⟩ := (sat d x).mp hx
      obtain ⟨w, hdw, hiy⟩ := (sat d y).mp hy
      exact ((hE v).mp (hV.output_mem_of_pairMember hdv)).1.2 i x y hix (hV.1.2 d w v hdw hdv ▸ hiy))
    (fun d x _ hx => ((sat d x).mp hx).elim fun v hv =>
      ((hE v).mp (hV.output_mem_of_pairMember hv.1)).output_mem_of_pairMember hv.2)
  refine ⟨f, fn0_of_function_l (ZF.modelsKP hZF) hf, fun d hd v hv x => ?_⟩
  refine (show Rd_entry_d d x f ↔ M.mem d D ∧ φ.denote ρ d x from spec d x).trans ?_
  rw [sat d x]
  exact ⟨fun ⟨_, w, hw, hx⟩ => hV.1.2 d w v hw hv ▸ hx, fun hx => ⟨hd, v, hv, hx⟩⟩

theorem rp_column_unique_l (hE : Extensional M) {D Q E V i f g} (hV : M.IsSetFunctionFromTo I V D E)
    (hf : Fn0_d D Q f) (hg : Fn0_d D Q g) (hF : Rp_column_d I D V i f) (hG : Rp_column_d I D V i g) : f = g := by
  apply hf.ext_l hE hg
  intro d hd
  obtain ⟨v, _, hv⟩ := hV.2.2 d hd
  obtain ⟨x, _, hx⟩ := hf.2.1 d hd
  exact ⟨x, hx, (hG d hd v hv x).mpr ((hF d hd v hv x).mp hx)⟩

def Rp_eval_d (ω D p V e : M.Domain) : Prop := ∀ i, M.mem i ω → ∃ f B,
  M.PairMember I f B p ∧ M.PairMember I i B e ∧ Rp_column_d I D V i f

def rp_eval_m {n} (ω D p V e : Term n) : Formula 1 n := Formula.forallMem ω (.existsE (.existsE (.conj
  (Formula.orderedPairMem 𝒞 (.bound 1) .newest p.weaken.weaken.weaken) (.conj
    (Formula.orderedPairMem 𝒞 (.bound 2) .newest e.weaken.weaken.weaken)
    (rp_column_m (𝒞 := 𝒞) D.weaken.weaken.weaken V.weaken.weaken.weaken (.bound 2) (.bound 1))))))
derive_free_closed rp_eval_m

theorem rp_eval_sat_l (hE : Extensional M) {n} (ρ : Env M n) (ω D p V e : Term n) :
    Formula.satisfies ρ (rp_eval_m (𝒞 := 𝒞) ω D p V e) ↔
      Rp_eval_d I (ω.eval ρ) (D.eval ρ) (p.eval ρ) (V.eval ρ) (e.eval ρ) := by
  simp only [rp_eval_m, Rp_eval_d, Formula.satisfies_forallMem_iff, Formula.satisfies_exists_iff,
    Formula.satisfies_conj_iff, Formula.satisfies_orderedPairMem_iff I, rp_column_sat_l I hE, Definitional.Term.eval_weaken]
  rfl

theorem rp_eval_exists_l (hZF : M.Models ZF) {ω D Q E U G p C V} (hp : Rp_map_d I D Q U G p C)
    (hG : ∀ f, Fn0_d D Q f → M.mem f G) (hE : M.IsFunctionSpace I E ω Q) (hV : M.IsSetFunctionFromTo I V D E) :
    ∃ e, M.IsSetFunctionFromTo I e ω C ∧ Rp_eval_d I ω D p V e := by
  let ρ : Env M 4 := ⟨Fin.cases V (Fin.cases D (Fin.cases p (fun _ => G))), fun _ => D⟩
  let φ : BinarySchema 4 := { body := Formula.existsMem (.bound 5) (.conj
    (Formula.orderedPairMem 𝒞 .newest (.bound 1) (.bound 5)) (rp_column_m (𝒞 := 𝒞) (.bound 4) (.bound 3) (.bound 2) .newest)) }
  have sat i B : φ.denote ρ i B ↔ ∃ f, M.mem f G ∧ M.PairMember I f B p ∧ Rp_column_d I D V i f := by
    simp only [φ, BinarySchema.denote, Formula.satisfies_existsMem_iff, Formula.satisfies_conj_iff,
      Formula.satisfies_orderedPairMem_iff I, rp_column_sat_l I hZF.1]
    rfl
  obtain ⟨e, he, spec⟩ := ZF.exists_setFunctionFromTo_of_denote hZF I φ ρ (source := ω) (target := C)
    (fun i hi => by
      obtain ⟨f, hf, hc⟩ := rp_column_exists_l I hZF hE hV hi
      obtain ⟨B, _, hb⟩ := hp.projection.2.2 f (hG f hf)
      exact ⟨B, (sat i B).mpr ⟨f, hG f hf, hb, hc⟩⟩)
    (fun i _ B A hB hA => by
      obtain ⟨f, hf, hfp, hF⟩ := (sat i B).mp hB
      obtain ⟨g, hg, hgp, hG⟩ := (sat i A).mp hA
      have eq := rp_column_unique_l I hZF.1 hV (hp.functions f hf) (hp.functions g hg) hF hG
      exact hp.projection.1.2 f B A hfp (eq.symm ▸ hgp))
    (fun i B _ hB => ((sat i B).mp hB).elim fun _ hf => hp.projection.output_mem_of_pairMember hf.2.1)
  refine ⟨e, he, fun i hi => ?_⟩
  obtain ⟨B, _, hb⟩ := he.2.2 i hi
  obtain ⟨f, _, hfp, hc⟩ := (sat i B).mp ((spec i B).mp hb).2
  exact ⟨f, B, hfp, hb, hc⟩

theorem Rp_eval_d.update_l {ω D Q E p V e i f B W e'} (h : Rp_eval_d I ω D p V e)
    (hf : Fn0_d D Q f) (hp : M.PairMember I f B p) (hW : Rp_update_d I D E V i f W)
    (he : Senv_update_d I e i B e') : Rp_eval_d I ω D p W e' := by
  intro j hj
  classical
  by_cases eq : j = i
  · subst j
    refine ⟨f, B, hp, (he.2 i B).mpr (Or.inl ⟨rfl, rfl⟩), fun d hd w hw x => ?_⟩
    obtain ⟨_, v, y, _, hy, hrow⟩ := (hW.2 d w).mp hw
    refine ⟨fun hx => (hrow.2 i x).mpr (Or.inl ⟨rfl, ?_⟩), fun hx => ?_⟩
    · exact hf.2.2 d hd x (hf.bound_l hx).2 y (hf.bound_l hy).2 hx hy
    · rcases (hrow.2 i x).mp hx with ⟨_, hxy⟩ | ⟨hn, _⟩
      · exact hxy.symm ▸ hy
      · exact (hn rfl).elim
  · obtain ⟨g, A, hgp, hje, hg⟩ := h j hj
    refine ⟨g, A, hgp, (he.2 j A).mpr (Or.inr ⟨eq, hje⟩), fun d hd w hw x => ?_⟩
    obtain ⟨_, v, _, hv, _, hrow⟩ := (hW.2 d w).mp hw
    exact (hg d hd v hv x).trans ⟨fun hx => (hrow.2 j x).mpr (Or.inr ⟨eq, hx⟩),
      fun hx => ((hrow.2 j x).mp hx).elim (fun he => (eq he.1).elim) And.right⟩

end YesMetaZFC.SetTheory.Internal

/-! ## 原子真值与商关系的精确对应 -/
namespace YesMetaZFC.SetTheory.Internal
open Definitional.Project InnerModel
universe u
variable {M : Structure.{u}} {𝒞 : OrderedPairConvention} (I : 𝒞.Interpretation M)

theorem rp_holds_rel_l {D Q E U V R i j f g Z} (hU : ∀ A, M.mem A U → M.MemberSubset A D)
    (hV : M.IsSetFunctionFromTo I V D E) (hf : Fn0_d D Q f) (hg : Fn0_d D Q g)
    (hF : Rp_column_d I D V i f) (hG : Rp_column_d I D V j g)
    (hZ : ∀ v, M.mem v Z ↔ M.mem v E ∧ ∃ x y, M.PairMember I i x v ∧ M.PairMember I j y v ∧ M.PairMember I x y R) :
    Rp_holds_d I U V Z ↔ Rp_rel_d I Q U R f g := by
  constructor
  · rintro ⟨A, hAU, hA⟩
    refine ⟨A, hAU, fun d hd => ?_⟩
    obtain ⟨v, hv, hvZ⟩ := hA d hd
    obtain ⟨_, x, y, hx, hy, hxy⟩ := (hZ v).mp hvZ
    have hdx := (hF d (hU A hAU d hd) v hv x).mpr hx
    have hdy := (hG d (hU A hAU d hd) v hv y).mpr hy
    exact ⟨x, (hf.bound_l hdx).2, y, (hg.bound_l hdy).2, hdx, hdy, hxy⟩
  · rintro ⟨A, hAU, hA⟩
    refine ⟨A, hAU, fun d hd => ?_⟩
    obtain ⟨v, hvE, hv⟩ := hV.2.2 d (hU A hAU d hd)
    obtain ⟨x, _, y, _, hx, hy, hxy⟩ := hA d hd
    exact ⟨v, hv, (hZ v).mpr ⟨hvE, x, y, (hF d (hU A hAU d hd) v hv x).mp hx,
      (hG d (hU A hAU d hd) v hv y).mp hy, hxy⟩⟩

theorem rp_holds_eq_l {D Q E U V i j f g Z} (hU : ∀ A, M.mem A U → M.MemberSubset A D)
    (hV : M.IsSetFunctionFromTo I V D E) (hf : Fn0_d D Q f)
    (hF : Rp_column_d I D V i f) (hG : Rp_column_d I D V j g)
    (hZ : ∀ v, M.mem v Z ↔ M.mem v E ∧ ∃ x, M.PairMember I i x v ∧ M.PairMember I j x v) :
    Rp_holds_d I U V Z ↔ Rp_eq_d Q U f g := by
  constructor
  · rintro ⟨A, hAU, hA⟩
    refine ⟨A, hAU, fun d hd => ?_⟩
    obtain ⟨v, hv, hvZ⟩ := hA d hd
    obtain ⟨_, x, hx, hy⟩ := (hZ v).mp hvZ
    have hdx := (hF d (hU A hAU d hd) v hv x).mpr hx
    exact ⟨x, (hf.bound_l hdx).2, hdx, (hG d (hU A hAU d hd) v hv x).mpr hy⟩
  · rintro ⟨A, hAU, hA⟩
    refine ⟨A, hAU, fun d hd => ?_⟩
    obtain ⟨v, hvE, hv⟩ := hV.2.2 d (hU A hAU d hd)
    obtain ⟨x, _, hx, hy⟩ := hA d hd
    exact ⟨v, hv, (hZ v).mpr ⟨hvE, x, (hF d (hU A hAU d hd) v hv x).mp hx,
      (hG d (hU A hAU d hd) v hv x).mp hy⟩⟩

end YesMetaZFC.SetTheory.Internal

/-! ## 内部程序行上的 Łoś 归纳性质

归纳对象是模型中的行号，性质是下方给出的实际原公式；赋值族、商赋值和
源真值集都在模型内量化，不以外部标准公式归纳代替内部程序归纳。
-/
namespace YesMetaZFC.SetTheory.Internal
open Definitional.Project
universe u
variable {M : Structure.{u}} {𝒞 : OrderedPairConvention} (I : 𝒞.Interpretation M)

def Rp_los_d (ω D U p E H C T K F n r : M.Domain) : Prop := ∀ V e Z,
  M.IsSetFunctionFromTo I V D E → M.mem e K → M.PairMember I r Z H → Rp_eval_d I ω D p V e →
    (Rp_holds_d I U V Z ↔ Ssat_d I C T K F n r e)

def rp_los_m {d} (ω D U p E H C T K F n r : Term d) : Formula 1 d := .forallE (.forallE (.forallE
  (.imp (Formula.isFunctionFromTo 𝒞 (.bound 2) D.weaken.weaken.weaken E.weaken.weaken.weaken)
    (.imp (.mem (.bound 1) K.weaken.weaken.weaken)
      (.imp (Formula.orderedPairMem 𝒞 r.weaken.weaken.weaken .newest H.weaken.weaken.weaken)
        (.imp (rp_eval_m (𝒞 := 𝒞) ω.weaken.weaken.weaken D.weaken.weaken.weaken p.weaken.weaken.weaken (.bound 2) (.bound 1))
          (.iff (rp_holds_m (𝒞 := 𝒞) U.weaken.weaken.weaken (.bound 2) .newest)
            (ssat_m (𝒞 := 𝒞) C.weaken.weaken.weaken T.weaken.weaken.weaken K.weaken.weaken.weaken
              F.weaken.weaken.weaken n.weaken.weaken.weaken r.weaken.weaken.weaken (.bound 1)))))))))
derive_free_closed rp_los_m

theorem rp_los_sat_l (hE : Extensional M) {d} (ρ : Env M d) (ω D U p E H C T K F n r : Term d) :
    Formula.satisfies ρ (rp_los_m (𝒞 := 𝒞) ω D U p E H C T K F n r) ↔
      Rp_los_d I (ω.eval ρ) (D.eval ρ) (U.eval ρ) (p.eval ρ) (E.eval ρ) (H.eval ρ)
        (C.eval ρ) (T.eval ρ) (K.eval ρ) (F.eval ρ) (n.eval ρ) (r.eval ρ) := by
  simp only [rp_los_m, Rp_los_d, Formula.satisfies_forall_iff, Formula.satisfies_imp_iff,
    Formula.satisfies_isFunctionFromTo_iff I hE, Formula.satisfies_mem_iff, Formula.satisfies_orderedPairMem_iff I,
    rp_eval_sat_l I hE, Formula.satisfies_iff_iff, rp_holds_sat_l I, ssat_sat_l I hE, Definitional.Term.eval_weaken]
  rfl

end YesMetaZFC.SetTheory.Internal

/-! ## 存在量词的实际内部见证函数

先在大集合上统一选取见证，再在其余指标取固定值，得到全定义的模型内函数图。
选择只用于此统一化步骤；逆向传输和整族赋值更新均沿用 ZF 层。
-/
namespace YesMetaZFC.SetTheory.Internal
open Definitional.Project InnerModel
universe u
variable {M : Structure.{u}} {𝒞 : OrderedPairConvention} (I : 𝒞.Interpretation M)

theorem rp_exists_l (hZFC : M.Models ZFC) {ω D Q E U V i Z B}
    (hE : M.IsFunctionSpace I E ω Q) (hV : M.IsSetFunctionFromTo I V D E)
    (hU : ∀ A, M.mem A U → M.MemberSubset A D) (hQ : ∃ x, M.mem x Q) (hi : M.mem i ω)
    (hB : Rp_ex_d I Q E i Z B) : Rp_holds_d I U V B ↔
      ∃ f W, Fn0_d D Q f ∧ Rp_update_d I D E V i f W ∧ Rp_holds_d I U W Z := by
  let hZF := ZFC.models_zf_l hZFC
  constructor
  · rintro ⟨A, hAU, hA⟩
    obtain ⟨z, hz⟩ := hQ
    let ρ : Env M 5 := ⟨Fin.cases z (Fin.cases Z (Fin.cases i (Fin.cases V (fun _ => A)))), fun _ => Q⟩
    let φ : BinarySchema 5 := {
      body := .disj
        (.conj (.mem (.bound 1) (.bound 6)) (.existsE (Formula.existsMem (.bound 4) (.conj
          (Formula.orderedPairMem 𝒞 (.bound 3) (.bound 1) (.bound 7))
          (senv_update_m (𝒞 := 𝒞) (.bound 1) (.bound 6) (.bound 2) .newest)))))
        (.conj (.neg (.mem (.bound 1) (.bound 6))) (Formula.extensionalEq .newest (.bound 2))) }
    have sat d x : φ.denote ρ d x ↔
        (M.mem d A ∧ ∃ v w, M.mem w Z ∧ M.PairMember I d v V ∧ Senv_update_d I v i x w) ∨ (¬ M.mem d A ∧ x = z) := by
      simp only [φ, BinarySchema.denote, Formula.satisfies_disj_iff, Formula.satisfies_conj_iff,
        Formula.satisfies_mem_iff, Formula.satisfies_exists_iff, Formula.satisfies_existsMem_iff,
        Formula.satisfies_orderedPairMem_iff I, senv_update_sat_l I hZF.1, Formula.satisfies_neg_iff,
        Formula.satisfies_extensionalEq_iff_eq hZF.1]
      rfl
    obtain ⟨f, hf, select⟩ := ZFC.uniformize_formula_l (kp_pair_l (ZF.modelsKP hZF)) hZFC φ ρ
      (X := D) (Y := Q) (fun d _ => by
        classical
        by_cases hd : M.mem d A
        · obtain ⟨v, hdv, hv⟩ := hA d hd
          obtain ⟨_, x, hx, w, hw, he⟩ := (hB v).mp hv
          exact ⟨x, hx, (sat d x).mpr (Or.inl ⟨hd, v, w, hw, hdv, he⟩)⟩
        · exact ⟨z, hz, (sat d z).mpr (Or.inr ⟨hd, rfl⟩)⟩)
    have hf' := fn0_of_function_l (ZF.modelsKP hZF) hf
    obtain ⟨W, hW⟩ := rp_update_exists_l I hZF hE hV hi hf'
    refine ⟨f, W, hf', hW, A, hAU, fun d hd => ?_⟩
    obtain ⟨x, _, hdx⟩ := hf'.2.1 d (hU A hAU d hd)
    rcases (sat d x).mp (select d x hdx) with ⟨_, v, w, hw, hdv, he⟩ | ⟨hn, _⟩
    · exact ⟨w, (hW.2 d w).mpr ⟨hU A hAU d hd, v, x, hdv, hdx, he⟩, hw⟩
    · exact (hn hd).elim
  · rintro ⟨f, W, hf, hW, h⟩
    exact rp_ex_update_l I hV hf hW hB h

/-- 存在量词的真值集与见证函数一并给出，所有中间集合均在模型内部构造。 -/
theorem rp_quantifier_l (hZFC : M.Models ZFC) {ω D Q E U V i}
    (hE : M.IsFunctionSpace I E ω Q) (hV : M.IsSetFunctionFromTo I V D E)
    (hU : ∀ A, M.mem A U → M.MemberSubset A D) (hQ : ∃ x, M.mem x Q) (hi : M.mem i ω) (Z : M.Domain) :
    ∃ B, Rp_ex_d I Q E i Z B ∧ (Rp_holds_d I U V B ↔
      ∃ f W, Fn0_d D Q f ∧ Rp_update_d I D E V i f W ∧ Rp_holds_d I U W Z) := by
  obtain ⟨B, hB⟩ := rp_ex_exists_l I (ZFC.models_zf_l hZFC) Q E i Z
  exact ⟨B, hB, rp_exists_l I hZFC hE hV hU hQ hi hB⟩

/-- 直接消费合法内部程序行及其实际真值表，不假定公式码外部标准。 -/
theorem rp_quantifier_row_l (hZFC : M.Models ZFC) {ω D Q R E U V F n H r c i j Z B}
    (hF : Sfm_d I ω n F) (hH : Seval_d I Q R E F n H) (hc : M.PairMember I r c F)
    (hs : Sop_d I 3 c i j) (hB : M.PairMember I r B H) (hZ : M.PairMember I j Z H)
    (hE : M.IsFunctionSpace I E ω Q) (hV : M.IsSetFunctionFromTo I V D E)
    (hU : ∀ A, M.mem A U → M.MemberSubset A D) (hQ : ∃ x, M.mem x Q) :
    Rp_holds_d I U V B ↔ ∃ f W, Fn0_d D Q f ∧ Rp_update_d I D E V i f W ∧ Rp_holds_d I U W Z := by
  let hZF := ZFC.models_zf_l hZFC
  have hi : M.mem i ω := by
    rcases hF.2.2 r c hc with ⟨a, b, ht, ha, hb⟩ | ⟨a, b, ht, ha, hb⟩ | ⟨a, b, ht, ha, hb⟩ | ⟨a, b, ht, ha, hb⟩ <;>
      obtain ⟨he, rfl, rfl⟩ := sop_injective_l I (ZF.modelsKP hZF) hs ht <;> cases he
    exact ha
  apply rp_exists_l I hZFC hE hV hU hQ hi
  intro v
  have row := (seval_row_l I hZF hF hH hc hB v).trans (and_congr_right fun _ =>
    snode_decode_l I (ZF.modelsKP hZF) 3 hs)
  refine row.trans ⟨?_, ?_⟩
  · rintro ⟨hv, Z', hZ', x, w, hx, he, hw⟩
    have eq := hH.1.2.1.2 j Z' Z hZ' hZ
    exact ⟨hv, x, hx, w, eq ▸ hw, he⟩
  · rintro ⟨hv, x, hx, w, hw, he⟩
    exact ⟨hv, Z, hZ, x, w, hx, he, hw⟩

end YesMetaZFC.SetTheory.Internal

/-! ## 全部内部程序行的 Łoś 定理

在真实可分离的行性质上作内部强归纳。原子步读取商投影，或非步使用超滤二择，
存在步构造真实见证函数及更新后的赋值族。此处代表族明确为全部背景内部函数。
-/
namespace YesMetaZFC.SetTheory.Internal
open Definitional.Project InnerModel
universe u
variable {M : Structure.{u}} {𝒞 : OrderedPairConvention} (I : 𝒞.Interpretation M)

theorem rp_los_l (hZFC : M.Models ZFC) {ω D Q U R c G p C T E K F n H r}
    (hU : FilterZF.Maximal_d (ℳ := M) D U) (hM : Rp_model_d I D Q U R c G p C T)
    (hG : ∀ f, Fn0_d D Q f → M.mem f G) (hE : M.IsFunctionSpace I E ω Q)
    (hK : M.IsFunctionSpace I K ω C) (hF : Sfm_d I ω n F) (hH : Seval_d I Q R E F n H)
    (hr : M.mem r n) : Rp_los_d I ω D U p E H C T K F n r := by
  let hZF := ZFC.models_zf_l hZFC
  obtain ⟨J, hJ⟩ := seval_exists_l I hZF C T K F hF.2.1.1
  have hQ : ∃ x, M.mem x Q := by
    obtain ⟨B, hB⟩ := hM.code.2.1
    obtain ⟨f, hf⟩ := (hM.map.range B).mp hB
    obtain ⟨d, hd⟩ := hU.2.1 D hU.1.2.1
    exact ((hM.map.functions f (hM.map.projection.input_mem_of_pairMember hf)).2.1 d hd).imp fun _ hx => hx.1
  let ρ : Env M 11 := ⟨Fin.cases n (Fin.cases F (Fin.cases K (Fin.cases T (Fin.cases C (Fin.cases H
    (Fin.cases E (Fin.cases p (Fin.cases U (Fin.cases D (fun _ => ω)))))))))), fun _ => ω⟩
  let φ : UnarySchema 11 := {
    body := rp_los_m (𝒞 := 𝒞) (.bound 11) (.bound 10) (.bound 9) (.bound 8)
      (.bound 7) (.bound 6) (.bound 5) (.bound 4) (.bound 3) (.bound 2) (.bound 1) .newest }
  have sat s : φ.denote ρ s ↔ Rp_los_d I ω D U p E H C T K F n s := rp_los_sat_l I hZF.1 ..
  suffices h : φ.denote ρ r from (sat r).mp h
  apply sfm_induction_l I hZF hF φ ρ ?_ hr
  intro r hr ih
  apply (sat r).mpr
  intro V e Z hV he hZ hv
  obtain ⟨o, ho⟩ := (hF.2.1.2.2 r).mp hr
  rcases hF.2.2 r o ho with ⟨i, j, hs, hi, hj⟩ | ⟨i, j, hs, hi, hj⟩ | ⟨i, j, hs, hi, hj⟩ | ⟨i, j, hs, hi, hj⟩
  · obtain ⟨f, B, hf, hie, hfc⟩ := hv i hi
    obtain ⟨g, A, hg, hje, hgc⟩ := hv j hj
    have src v := (seval_row_l I hZF hF hH ho hZ v).trans
      (and_congr_right fun _ => snode_decode_l I (ZF.modelsKP hZF) 0 hs)
    exact (rp_holds_rel_l I hU.1.1 hV (hM.map.functions f (hM.map.projection.input_mem_of_pairMember hf))
      (hM.map.functions g (hM.map.projection.input_mem_of_pairMember hg)) hfc hgc src).trans
      ((hM.relation f g B A hf hg).symm.trans (ssat_rel_l I hZF hF hJ ho hs hK he hie hje).symm)
  · obtain ⟨f, B, hf, hie, hfc⟩ := hv i hi
    obtain ⟨g, A, hg, hje, hgc⟩ := hv j hj
    have src v := (seval_row_l I hZF hF hH ho hZ v).trans
      (and_congr_right fun _ => snode_decode_l I (ZF.modelsKP hZF) 1 hs)
    exact (rp_holds_eq_l I hU.1.1 hV (hM.map.functions f (hM.map.projection.input_mem_of_pairMember hf)) hfc hgc src).trans
      ((rp_kernel_l I hZF.1 hU.1.base_l hM.map hf hg).symm.trans (ssat_eq_l I hZF hF hJ ho hs hK he hie hje).symm)
  · obtain ⟨A, hA⟩ := (hH.1.2.2 i).mp (hH.1.1.transitive r hr i hi)
    obtain ⟨B, hB⟩ := (hH.1.2.2 j).mp (hH.1.1.transitive r hr j hj)
    have spec v : M.mem v Z ↔ M.mem v E ∧ ¬ (M.mem v A ∨ M.mem v B) := by
      have src := (seval_row_l I hZF hF hH ho hZ v).trans
        (and_congr_right fun _ => snode_decode_l I (ZF.modelsKP hZF) 2 hs)
      refine src.trans ⟨?_, ?_⟩
      · rintro ⟨hv, A', B', hA', hB', ht⟩
        exact ⟨hv, hH.1.2.1.2 i A' A hA' hA ▸ hH.1.2.1.2 j B' B hB' hB ▸ ht⟩
      · exact fun ⟨hv, ht⟩ => ⟨hv, A, B, hA, hB, ht⟩
    exact (rp_holds_nor_l I hZF hU hV spec).trans ((not_congr (or_congr
      ((sat i).mp (ih i hi) V e A hV he hA hv) ((sat j).mp (ih j hj) V e B hV he hB hv))).trans
        (ssat_nor_l I hZF hF hJ ho hs he).symm)
  · obtain ⟨A, hA⟩ := (hH.1.2.2 j).mp (hH.1.1.transitive r hr j hj)
    rw [rp_quantifier_row_l I hZFC hF hH ho hs hZ hA hE hV hU.1.1 hQ,
      ssat_exists_l I hZF hF hJ ho hs he]
    constructor
    · rintro ⟨f, W, hf, hW, hw⟩
      obtain ⟨B, hB, hfB⟩ := hM.map.projection.2.2 f (hG f hf)
      obtain ⟨e', he', hk⟩ := senv_update_exists_l I hZF ((hK e).mp he) hi hB
      exact ⟨B, e', hB, he', ((sat j).mp (ih j hj) W e' A hW.1 ((hK e').mpr hk) hA
        (hv.update_l I hf hfB hW he')).mp hw⟩
    · rintro ⟨B, e', hB, he', ht⟩
      obtain ⟨f, hfB⟩ := (hM.map.range B).mp hB
      have hf := hM.map.functions f (hM.map.projection.input_mem_of_pairMember hfB)
      obtain ⟨W, hW⟩ := rp_update_exists_l I hZF hE hV hi hf
      have hk := (hK e').mpr (he'.function_l I ((hK e).mp he) hi hB)
      exact ⟨f, W, hf, hW, ((sat j).mp (ih j hj) W e' A hW.1 hk hA (hv.update_l I hf hfB hW he')).mpr ht⟩

/-- 统一满足关系上的 Łoś 方程，公式遍历全部实际内部代码。 -/
theorem rp_satisfies_l (hZFC : M.Models ZFC) {ω D Q U R c G p C T s A E V e a}
    (hU : FilterZF.Maximal_d (ℳ := M) D U) (hM : Rp_model_d I D Q U R c G p C T)
    (hG : ∀ f, Fn0_d D Q f → M.mem f G) (hs : Smdl_d I s Q R) (hA : Scode_d I ω A)
    (hE : M.IsFunctionSpace I E ω Q) (hV : M.IsSetFunctionFromTo I V D E)
    (he : M.IsSetFunctionFromTo I e ω C) (hv : Rp_eval_d I ω D p V e) (ha : M.mem a A) :
    Satisfies_d I ω c a e ↔ ∃ B, M.mem B U ∧ ∀ d, M.mem d B →
      ∃ v, M.PairMember I d v V ∧ Satisfies_d I ω s a v := by
  let hZF := ZFC.models_zf_l hZFC
  obtain ⟨n, F, r, hf⟩ := (hA a).mp ha
  obtain ⟨K, hK⟩ := ZF.exists_functionSpace hZF I ω C
  obtain ⟨H, hH⟩ := seval_exists_l I hZF Q R E F hf.2.1.2.1.1
  obtain ⟨Z, hZ⟩ := (hH.1.2.2 r).mp hf.2.2
  have src v := (satisfies_decode_l I hZF.1 hs hf hE).trans (ssat_value_l I hZF hH hZ v)
  have los := rp_los_l I hZFC hU hM hG hE hK hf.2.1 hH hf.2.2 V e Z hV ((hK e).mpr he) hZ hv
  refine (satisfies_decode_l I hZF.1 hM.code hf hK).trans (los.symm.trans ?_)
  exact exists_congr fun B => and_congr_right fun _ => forall_congr' fun d =>
    imp_congr Iff.rfl (exists_congr fun v => and_congr_right fun _ => (src v).symm)

/-- 商赋值和完整内部代码集自动构造，不把“存在代表赋值”作为操作参数。 -/
theorem rp_los_assignment_l (hZFC : M.Models ZFC) {ω D Q U R c G p C T s E V}
    (hω : M.IsOmega ω) (hU : FilterZF.Maximal_d (ℳ := M) D U) (hM : Rp_model_d I D Q U R c G p C T)
    (hG : ∀ f, Fn0_d D Q f → M.mem f G) (hs : Smdl_d I s Q R)
    (hE : M.IsFunctionSpace I E ω Q) (hV : M.IsSetFunctionFromTo I V D E) : ∃ e A,
      M.IsSetFunctionFromTo I e ω C ∧ Rp_eval_d I ω D p V e ∧ Scode_d I ω A ∧
      ∀ a, M.mem a A → (Satisfies_d I ω c a e ↔ ∃ B, M.mem B U ∧ ∀ d, M.mem d B →
        ∃ v, M.PairMember I d v V ∧ Satisfies_d I ω s a v) := by
  let hZF := ZFC.models_zf_l hZFC
  obtain ⟨e, he, hv⟩ := rp_eval_exists_l I hZF hM.map hG hE hV
  obtain ⟨A, hA⟩ := scode_exists_l I hZF hω
  exact ⟨e, A, he, hv, hA, fun _ ha => rp_satisfies_l I hZFC hU hM hG hs hA hE hV he hv ha⟩

end YesMetaZFC.SetTheory.Internal
