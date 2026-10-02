import YesMetaZFC.SetTheory.InnerModel.OD.Definition

/-! # 序数可定义的实际偏函数图

将原二元公式的唯一值部分限制到一个真实累积层，得到 OD 偏函数。它为固定
集合参数的定义提供统一内部编码，输入集合不必属于 OD。
-/
namespace YesMetaZFC.SetTheory.InnerModel
open Definitional.Project
universe u
variable {M : Structure.{u}}

def od_unique_s {n} (φ : BinarySchema n) : BinarySchema n where
  body := .conj φ.body (.forallE (.imp
    (binary_pred_m φ (fun i => .bound ⟨i.val+3, by omega⟩) (.bound 2) .newest)
    (Formula.extensionalEq .newest (.bound 1))))
  freeClosed := by simp -implicitDefEqProofs [Definitional.Formula.FreeClosed]

theorem od_unique_sat_l (hE : Extensional M) {n} (φ : BinarySchema n) (ρ : Env M n) (a x : M.Domain) :
    (od_unique_s φ).denote ρ a x ↔ φ.denote ρ a x ∧ ∀ y, φ.denote ρ a y → y = x := by
  simp only [od_unique_s, BinarySchema.denote, Formula.satisfies_conj_iff, Formula.satisfies_forall_iff,
    Formula.satisfies_imp_iff, binary_pred_sat_l, Formula.satisfies_extensionalEq_iff_eq hE]
  rfl

def Od_graph_d (I : kpair_convention_l.Interpretation M) {n} (φ : BinarySchema n)
    (ρ : Env M n) (V F : M.Domain) : Prop := M.IsSetRelation I F ∧ ∀ a x,
  M.PairMember I a x F ↔ M.mem a V ∧ M.mem x V ∧ φ.denote ρ a x

def od_graph_m {n d} (φ : BinarySchema n) (e : Fin n → Term d) (V F : Term d) : Formula 1 d :=
  .conj (Formula.isRelation kpair_convention_l F) (.forallE (.forallE (.iff
    (Formula.orderedPairMem kpair_convention_l (.bound 1) .newest F.weaken.weaken)
    (.conj (.mem (.bound 1) V.weaken.weaken) (.conj (.mem .newest V.weaken.weaken)
      (binary_pred_m φ (fun i => (e i).weaken.weaken) (.bound 1) .newest))))))

@[simp] theorem od_graph_closed_l {n d} (φ : BinarySchema n) (e : Fin n → Term d) (V F : Term d)
    (he : ∀ i, (e i).freeSupport = []) (hV : V.freeSupport = []) (hF : F.freeSupport = []) :
    (od_graph_m φ e V F).FreeClosed := by
  simp -implicitDefEqProofs [od_graph_m, Definitional.Formula.FreeClosed, he, hV, hF]

theorem od_graph_sat_l (I : kpair_convention_l.Interpretation M) {n d} (φ : BinarySchema n)
    (ρ : Env M d) (e : Fin n → Term d) (V F : Term d) :
    Formula.satisfies ρ (od_graph_m φ e V F) ↔
      Od_graph_d I φ ⟨fun i => (e i).eval ρ, ρ.free⟩ (V.eval ρ) (F.eval ρ) := by
  simp only [od_graph_m, Od_graph_d, Formula.satisfies_conj_iff, Formula.satisfies_isRelation_iff I,
    Formula.satisfies_forall_iff, Formula.satisfies_iff_iff, Formula.satisfies_orderedPairMem_iff I,
    Formula.satisfies_mem_iff, binary_pred_sat_l, Definitional.Term.eval_weaken]
  rfl

def od_graph_s {n} (φ : BinarySchema n) : UnarySchema (n+1) := {
  body := .existsE (.conj (v_m kpair_convention_l (.bound 2) .newest)
    (od_graph_m φ (fun i => .bound ⟨i.val+3, by omega⟩) .newest (.bound 1))) }

theorem od_graph_schema_l (I : kpair_convention_l.Interpretation M) (hE : Extensional M) {n}
    (φ : BinarySchema n) (ρ : Env M n) (a F : M.Domain) :
    (od_graph_s φ).denote (ρ.push a) F ↔ ∃ V, V_d I a V ∧ Od_graph_d I φ ρ V F := by
  simp only [od_graph_s, UnarySchema.denote, Formula.satisfies_exists_iff, Formula.satisfies_conj_iff,
    v_sat_l I hE, od_graph_sat_l I]
  rfl

/-- 只要某行唯一指定 x，就有一个 OD 偏函数在该行取值 x。 -/
theorem od_graph_exists_l (hZF : M.Models ZF) (I : kpair_convention_l.Interpretation M)
    {n} (φ : BinarySchema n) (ρ : Env M n) (hρ : ∀ i, M.IsOrdinal (ρ.bound i))
    {A x : M.Domain} (hx : ∀ y, φ.denote ρ A y ↔ y = x) :
    ∃ F, Od_d F ∧ M.IsSetFunction I F ∧ M.PairMember I A x F := by
  obtain ⟨P, hP⟩ := KP.exists_pair (ZF.modelsKP hZF) A x
  obtain ⟨a, V, hv, hp⟩ := ZF.v_cover_l I hZF P
  have ht := ZF.v_transitive_l I hZF hv
  let ψ := od_unique_s φ
  obtain ⟨F, hf, hF⟩ := ZF.exists_setRelationOn_of_denote hZF I ψ ρ V
  have graph : Od_graph_d I ψ ρ V F := ⟨hf.1, hF⟩
  have hOD : Od_d F := by
    apply od_of_unique_l hZF (od_graph_s ψ) (ρ.push a) (Fin.cases (v_ordinal_l I hv) hρ)
    intro G
    refine (od_graph_schema_l I hZF.1 ψ ρ a G).trans ⟨?_, fun he => he.symm ▸ ⟨V, hv, graph⟩⟩
    rintro ⟨W, hw, hg⟩
    have eq := ZF.v_unique_l I hZF hw hv; subst W
    exact hg.1.eq_of_pairMember_iff hZF.1 hf.1 (fun u y => (hg.2 u y).trans (hF u y).symm)
  refine ⟨F, hOD, ⟨hf.1, fun u y z hy hz => ?_⟩, ?_⟩
  · exact ((od_unique_sat_l hZF.1 φ ρ u z).mp ((hF u z).mp hz).2.2).2 y
      ((od_unique_sat_l hZF.1 φ ρ u y).mp ((hF u y).mp hy).2.2).1
  · exact (hF A x).mpr ⟨ht P hp A ((hP A).mpr (Or.inl rfl)), ht P hp x ((hP x).mpr (Or.inr rfl)),
      (od_unique_sat_l hZF.1 φ ρ A x).mpr ⟨(hx x).mpr rfl, fun y hy => (hx y).mp hy⟩⟩

end YesMetaZFC.SetTheory.InnerModel
