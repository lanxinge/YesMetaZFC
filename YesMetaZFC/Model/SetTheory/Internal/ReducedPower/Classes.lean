import YesMetaZFC.Model.SetTheory.Internal.ReducedPower.Relation
import YesMetaZFC.Model.SetTheory.Internal.Structure
import YesMetaZFC.SetTheory.Ord.Arithmetic.Recursion

/-! # 模型内的函数等价类集合与投影

每个类由指定函数族上的分离得到，全部类由内部函数图的值域收集。
投影的核恰好是几乎处处相等，无须选择各类的代表元。
-/
namespace YesMetaZFC.SetTheory.Internal
open Definitional.Project InnerModel
universe u
variable {M : Structure.{u}} {𝒞 : OrderedPairConvention} (I : 𝒞.Interpretation M)

def Rp_class_d (Q U G f B : M.Domain) : Prop := ∀ g, M.mem g B ↔ M.mem g G ∧ Rp_eq_d Q U f g

def rp_class_m {d} (Q U G f B : Term d) : Formula 1 d := .forallE (.iff (.mem .newest B.weaken)
  (.conj (.mem .newest G.weaken) (rp_eq_m Q.weaken U.weaken f.weaken .newest)))
derive_free_closed rp_class_m

theorem rp_class_sat_l (hE : Extensional M) {d} (ρ : Env M d) (Q U G f B : Term d) :
    Formula.satisfies ρ (rp_class_m Q U G f B) ↔
      Rp_class_d (Q.eval ρ) (U.eval ρ) (G.eval ρ) (f.eval ρ) (B.eval ρ) := by
  simp only [rp_class_m, Rp_class_d, Formula.satisfies_forall_iff, Formula.satisfies_iff_iff,
    Formula.satisfies_mem_iff, Formula.satisfies_conj_iff, rp_eq_sat_l hE, Definitional.Term.eval_weaken]
  rfl

theorem rp_class_exists_l (hZF : M.Models ZF) (Q U G f : M.Domain) : ∃ B, Rp_class_d Q U G f B := by
  let ρ : Env M 3 := ⟨Fin.cases f (Fin.cases U (fun _ => Q)), fun _ => Q⟩
  let φ : UnarySchema 3 := { body := rp_eq_m (.bound 3) (.bound 2) (.bound 1) .newest }
  obtain ⟨B, hB⟩ := ZF.separation_exists_d hZF φ ρ G
  exact ⟨B, fun g => (hB g).trans (and_congr_right fun _ => rp_eq_sat_l hZF.1 _ _ _ _ _)⟩

theorem rp_class_eq_l (hE : Extensional M) {D Q U G f g B C}
    (hU : FilterZF.Base_d (ℳ := M) D U) (hG : ∀ f, M.mem f G → Fn0_d D Q f)
    (hf : M.mem f G) (hg : M.mem g G) (hB : Rp_class_d Q U G f B) (hC : Rp_class_d Q U G g C) :
    B = C ↔ Rp_eq_d Q U f g := by
  constructor
  · intro he
    have hfB := (hB f).mpr ⟨hf, rp_eq_refl_l hU (hG f hf)⟩
    exact ((hC f).mp (he ▸ hfB)).2.symm_l
  · intro he
    apply hE.eq_of_same_members B C
    intro v
    exact (hB v).trans ((and_congr_right fun _ =>
      ⟨fun hv => he.symm_l.trans_l hU (hG f hf) hv,
        fun hv => he.trans_l hU (hG g hg) hv⟩).trans (hC v).symm)

/-- 从实际候选集合中分离合法代表；候选可取源模型自身，而不要求全部背景函数。 -/
theorem rp_family_exists_l (hKP : M.Models KP) (D Q B : M.Domain) :
    ∃ G, ∀ f, M.mem f G ↔ M.mem f B ∧ Fn0_d D Q f := by
  let ρ : Env M 2 := ⟨Fin.cases Q (fun _ => D), fun _ => D⟩
  let φ : Delta0UnarySchema 2 := { body := fn0_m (.bound 2) (.bound 1) .newest, delta0 := fn0_delta_l .. }
  obtain ⟨G, hG⟩ := KP.separation_exists_d hKP φ ρ B
  exact ⟨G, fun f => (hG f).trans (and_congr_right fun _ => fn0_sat_l hKP.1 _ _ _ _)⟩

structure Rp_map_d (D Q U G p C : M.Domain) : Prop where
  functions : ∀ f, M.mem f G → Fn0_d D Q f
  projection : M.IsSetFunctionFromTo I p G C
  range : M.IsRangeOf I C p
  classes : ∀ f B, M.PairMember I f B p ↔ M.mem f G ∧ Rp_class_d Q U G f B

def rp_map_m {d} (D Q U G p C : Term d) : Formula 1 d := .conj
  (.forallE (.imp (.mem .newest G.weaken) (fn0_m D.weaken Q.weaken .newest))) (.conj
    (Formula.isFunctionFromTo 𝒞 p G C) (.conj (Formula.isRange 𝒞 C p) (.forallE (.forallE (.iff
      (Formula.orderedPairMem 𝒞 (.bound 1) .newest p.weaken.weaken) (.conj (.mem (.bound 1) G.weaken.weaken)
        (rp_class_m Q.weaken.weaken U.weaken.weaken G.weaken.weaken (.bound 1) .newest)))))))
derive_free_closed rp_map_m

theorem rp_map_sat_l (hE : Extensional M) {d} (ρ : Env M d) (D Q U G p C : Term d) :
    Formula.satisfies ρ (rp_map_m (𝒞 := 𝒞) D Q U G p C) ↔
      Rp_map_d I (D.eval ρ) (Q.eval ρ) (U.eval ρ) (G.eval ρ) (p.eval ρ) (C.eval ρ) := by
  simp only [rp_map_m, Formula.satisfies_conj_iff, Formula.satisfies_forall_iff, Formula.satisfies_imp_iff,
    Formula.satisfies_iff_iff, Formula.satisfies_mem_iff, fn0_sat_l hE,
    Formula.satisfies_isFunctionFromTo_iff I hE, Formula.satisfies_isRange_iff I,
    Formula.satisfies_orderedPairMem_iff I, rp_class_sat_l hE, Definitional.Term.eval_weaken]
  exact ⟨fun h => ⟨h.1, h.2.1, h.2.2.1, h.2.2.2⟩, fun h => ⟨h.functions, h.projection, h.range, h.classes⟩⟩

theorem rp_map_exists_l (hZF : M.Models ZF) {D Q U G}
    (hG : ∀ f, M.mem f G → Fn0_d D Q f) : ∃ p C, Rp_map_d I D Q U G p C := by
  obtain ⟨P, hP⟩ := ZF.exists_powerSet hZF G
  let ρ : Env M 3 := ⟨Fin.cases G (Fin.cases U (fun _ => Q)), fun _ => Q⟩
  let φ : BinarySchema 3 := { body := rp_class_m (.bound 4) (.bound 3) (.bound 2) (.bound 1) .newest }
  have sat f B : φ.denote ρ f B ↔ Rp_class_d Q U G f B := rp_class_sat_l hZF.1 _ _ _ _ _ _
  obtain ⟨p, hp, spec⟩ := ZF.exists_setFunctionFromTo_of_denote hZF I φ ρ (source := G) (target := P)
    (fun f _ => (rp_class_exists_l hZF Q U G f).imp fun B hB => (sat f B).mpr hB)
    (fun f _ B C hB hC => hZF.1.eq_of_same_members B C (fun g => ((sat f B).mp hB g).trans ((sat f C).mp hC g).symm))
    (fun f B _ hB => (hP B).mpr fun g hg => (((sat f B).mp hB g).mp hg).1)
  obtain ⟨C, hC⟩ := ZF.exists_range_of_setFunction hZF I hp.1 hp.2.1
  exact ⟨p, C, ⟨hG, ⟨hp.1, hp.2.1, fun f hf => (hp.2.2 f hf).imp fun B hB =>
    ⟨(hC B).mpr ⟨f, hB.2⟩, hB.2⟩⟩, hC, fun f B => (spec f B).trans (and_congr_right fun _ => sat f B)⟩⟩

theorem rp_kernel_l (hE : Extensional M) {D Q U G p C f g B E}
    (hU : FilterZF.Base_d (ℳ := M) D U) (hp : Rp_map_d I D Q U G p C)
    (hf : M.PairMember I f B p) (hg : M.PairMember I g E p) : B = E ↔ Rp_eq_d Q U f g := by
  obtain ⟨hfG, hB⟩ := (hp.classes f B).mp hf
  obtain ⟨hgG, hE'⟩ := (hp.classes g E).mp hg
  exact rp_class_eq_l hE hU hp.functions hfG hgG hB hE'

theorem Rp_map_d.representative_l {D X U G p C f B} (hU : FilterZF.Base_d (ℳ := M) D U)
    (h : Rp_map_d I D X U G p C) (hf : M.PairMember I f B p) : M.mem f B := by
  obtain ⟨hfG, hB⟩ := (h.classes f B).mp hf
  exact (hB f).mpr ⟨hfG, rp_eq_refl_l hU (h.functions f hfG)⟩

/-- 类中的每个成员都是这个类的代表，无需选择规范代表。 -/
theorem Rp_map_d.member_l (hE : Extensional M) {D X U G p C f B}
    (hU : FilterZF.Base_d (ℳ := M) D U) (h : Rp_map_d I D X U G p C)
    (hB : M.mem B C) (hf : M.mem f B) : M.PairMember I f B p := by
  obtain ⟨g, hg⟩ := (h.range B).mp hB
  obtain ⟨hfG, hgf⟩ := ((h.classes g B).mp hg).2 f |>.mp hf
  obtain ⟨E, _, he⟩ := h.projection.2.2 f hfG
  exact ((rp_kernel_l I hE hU h hg he).mpr hgf).symm ▸ he

end YesMetaZFC.SetTheory.Internal
