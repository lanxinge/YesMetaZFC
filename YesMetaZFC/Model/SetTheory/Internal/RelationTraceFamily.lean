import YesMetaZFC.Model.SetTheory.Internal.PointwiseTrace

/-! # 原关系源实际拥有的子集族

每个背景子集必须由原模型中的集合码沿既有坐标图读出。
分离构造这一精确的集合族；任意内部逐点真值集都落在同一族中。
-/
namespace YesMetaZFC.SetTheory.Internal
open Definitional.Project InnerModel
universe u
variable {M : Structure.{u}} {𝒞 : OrderedPairConvention} (I : 𝒞.Interpretation M)

def Rt_trace_d (D t R B A : M.Domain) : Prop := ∀ s, M.mem s A ↔ M.mem s D ∧
  ∃ x, M.PairMember I s x t ∧ M.PairMember I x B R

def rt_trace_m {d} (D t R B A : Term d) : Formula 1 d := .forallE
  (.iff (.mem .newest A.weaken) (.conj (.mem .newest D.weaken) (.existsE
    (.conj (Formula.orderedPairMem 𝒞 (.bound 1) .newest t.weaken.weaken)
      (Formula.orderedPairMem 𝒞 .newest B.weaken.weaken R.weaken.weaken)))))
derive_free_closed rt_trace_m

theorem rt_trace_sat_l {d} (ρ : Env M d) (D t R B A : Term d) :
    Formula.satisfies ρ (rt_trace_m (𝒞 := 𝒞) D t R B A) ↔
      Rt_trace_d I (D.eval ρ) (t.eval ρ) (R.eval ρ) (B.eval ρ) (A.eval ρ) := by
  simp only [rt_trace_m, Rt_trace_d, Formula.satisfies_forall_iff, Formula.satisfies_iff_iff,
    Formula.satisfies_mem_iff, Formula.satisfies_conj_iff, Formula.satisfies_exists_iff,
    Formula.satisfies_orderedPairMem_iff I, Definitional.Term.eval_weaken]; rfl

def Rt_source_d (X R D t P : M.Domain) : Prop := ∀ A, M.mem A P ↔
  ∃ B, M.mem B X ∧ Rt_trace_d I D t R B A

theorem rt_trace_exists_l (hZF : M.Models ZF) (D t R B : M.Domain) : ∃ A, Rt_trace_d I D t R B A := by
  let ρ : Env M 3 := ⟨Fin.cases t (Fin.cases R (fun _ => B)), fun _ => D⟩
  let φ : UnarySchema 3 := { body := .existsE (.conj
    (Formula.orderedPairMem 𝒞 (.bound 1) .newest (.bound 2))
    (Formula.orderedPairMem 𝒞 .newest (.bound 4) (.bound 3))) }
  obtain ⟨A, spec⟩ := ZF.separation_exists_d hZF φ ρ D
  refine ⟨A, fun s => (spec s).trans (and_congr_right fun _ => ?_)⟩
  simp only [φ, Formula.satisfies_exists_iff, Formula.satisfies_conj_iff,
    Formula.satisfies_orderedPairMem_iff I]; rfl

theorem rt_source_exists_l (hZF : M.Models ZF) (X R D t : M.Domain) : ∃ P, Rt_source_d I X R D t P := by
  let ρ : Env M 4 := ⟨Fin.cases D (Fin.cases t (Fin.cases R (fun _ => X))), fun _ => X⟩
  let φ : UnarySchema 4 := {
    body := Formula.existsMem (.bound 4)
      (rt_trace_m (𝒞 := 𝒞) (.bound 2) (.bound 3) (.bound 4) .newest (.bound 1)) }
  obtain ⟨Q, power⟩ := ZF.exists_powerSet hZF D
  obtain ⟨P, spec⟩ := ZF.separation_exists_d hZF φ ρ Q
  have read A : φ.denote ρ A ↔ ∃ B, M.mem B X ∧ Rt_trace_d I D t R B A := by
    simp only [φ, UnarySchema.denote, Formula.satisfies_existsMem_iff, rt_trace_sat_l I]; rfl
  refine ⟨P, fun A => (spec A).trans ?_⟩
  exact ⟨fun h => (read A).mp h.2, fun h => ⟨(power A).mpr (fun s hs => h.elim fun _ hb => ((hb.2 s).mp hs).1),
    (read A).mpr h⟩⟩

theorem Rt_source_d.pointwise_l {X R D t P d B A b E F n r a}
    (h : Rt_source_d I X R D t P) (ft : M.IsSetFunctionFromTo I t D X)
    (domain : ∀ s x, M.PairMember I s x t → M.PairMember I x d R)
    (hB : M.mem B X) (trace : Rt_trace_d I D t R B A)
    (truth : ∀ x, M.mem x X → (M.PairMember I x B R ↔
      M.PairMember I x d R ∧ Pe_sat_d I b d X R E F n r a x)) :
    M.mem A P ∧ ∀ s x, M.PairMember I s x t →
      (M.mem s A ↔ Pe_sat_d I b d X R E F n r a x) := by
  refine ⟨(h A).mpr ⟨B, hB, trace⟩, fun s x hsx => ?_⟩
  apply (trace s).trans
  constructor
  · rintro ⟨_, y, hsy, hy⟩
    have eq := ft.1.2 s y x hsy hsx
    exact ((truth x (ft.output_mem_of_pairMember hsx)).mp (eq ▸ hy)).2
  · intro hx
    exact ⟨ft.input_mem_of_pairMember hsx, x, hsx,
      (truth x (ft.output_mem_of_pairMember hsx)).mpr ⟨domain s x hsx, hx⟩⟩

end YesMetaZFC.SetTheory.Internal
