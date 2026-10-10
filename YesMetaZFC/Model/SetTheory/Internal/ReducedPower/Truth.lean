import YesMetaZFC.Model.SetTheory.Internal.ReducedPower.Model

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
  exact rp_holds_relative_not_l I (FilterZF.maximal_relative_l hZF hU hP) hV hT hA hB
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
