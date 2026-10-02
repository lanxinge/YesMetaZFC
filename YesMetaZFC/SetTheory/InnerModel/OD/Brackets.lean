import YesMetaZFC.SetTheory.InnerModel.OD.Graph

/-! # 固定整个集合参数的 OD[A]

用实际 OD 偏函数在 A 处的值定义。图由原内部满足关系编码；下文证明它恰好
等价于原公式从 A 与序数参数唯一可定义，因而不把 A 的成员逐个加入参数域。
-/
namespace YesMetaZFC.SetTheory.InnerModel
open Definitional.Project
universe u
variable {M : Structure.{u}}

def ob_s : BinarySchema 0 := { body := .existsE (.conj (od_m .newest)
  (.conj (Formula.isFunction kpair_convention_l .newest)
    (Formula.orderedPairMem kpair_convention_l (.bound 2) (.bound 1) .newest))) }

def Ob_d (A x : M.Domain) : Prop := ob_s.denote ⟨Fin.elim0, fun _ => A⟩ A x
def ob_m {d} (A x : Term d) : Formula 1 d := binary_pred_m ob_s Fin.elim0 A x
derive_free_closed ob_m

theorem ob_sat_l {d} (ρ : Env M d) (A x : Term d) : Formula.satisfies ρ (ob_m A x) ↔ Ob_d (A.eval ρ) (x.eval ρ) :=
  (binary_pred_sat_l ob_s ρ Fin.elim0 A x).trans
    (Formula.closed_env_l _ ob_s.freeClosed (funext (Fin.cases rfl (Fin.cases rfl (fun i => Fin.elim0 i)))))

theorem ob_decode_l (I : kpair_convention_l.Interpretation M) (hE : Extensional M) {A x} :
    Ob_d A x ↔ ∃ F, Od_d F ∧ M.IsSetFunction I F ∧ M.PairMember I A x F := by
  simp only [Ob_d, ob_s, BinarySchema.denote, Formula.satisfies_exists_iff, Formula.satisfies_conj_iff,
    od_sat_l, Formula.satisfies_isFunction_iff I hE, Formula.satisfies_orderedPairMem_iff I]
  rfl

def Ob_eval_d (I : kpair_convention_l.Interpretation M) (q A x : M.Domain) : Prop :=
  ∃ F, Od_eval_d I q F ∧ M.IsSetFunction I F ∧ M.PairMember I A x F

def ob_eval_m {d} (q A x : Term d) : Formula 1 d := .existsE
  (.conj (od_eval_m (𝒞 := kpair_convention_l) q.weaken .newest)
    (.conj (Formula.isFunction kpair_convention_l .newest)
      (Formula.orderedPairMem kpair_convention_l A.weaken x.weaken .newest)))
derive_free_closed ob_eval_m

theorem ob_eval_sat_l (I : kpair_convention_l.Interpretation M) (hE : Extensional M)
    {d} (ρ : Env M d) (q A x : Term d) :
    Formula.satisfies ρ (ob_eval_m q A x) ↔ Ob_eval_d I (q.eval ρ) (A.eval ρ) (x.eval ρ) := by
  simp only [ob_eval_m, Ob_eval_d, Formula.satisfies_exists_iff, Formula.satisfies_conj_iff,
    od_eval_sat_l I hE, Formula.satisfies_isFunction_iff I hE, Formula.satisfies_orderedPairMem_iff I,
    Definitional.Term.eval_weaken]
  rfl

theorem ob_eval_unique_l (I : kpair_convention_l.Interpretation M) (hZF : M.Models ZF) {q A x y}
    (h : Ob_eval_d I q A x) (g : Ob_eval_d I q A y) : x = y := by
  obtain ⟨F, hf, hF, hx⟩ := h
  obtain ⟨G, hg, _, hy⟩ := g
  have eq := od_eval_unique_l I hZF hg hf; subst G
  exact hF.2 A x y hx hy

theorem ob_code_l (I : kpair_convention_l.Interpretation M) (hZF : M.Models ZF) {A x} :
    Ob_d A x ↔ ∃ q, Ob_eval_d I q A x := by
  rw [ob_decode_l I hZF.1]
  exact ⟨fun ⟨F, hf, hF, hx⟩ => ((od_code_range_l I hZF).mp hf).elim fun q hq => ⟨q, F, hq, hF, hx⟩,
    fun ⟨q, F, hq, hF, hx⟩ => ⟨F, (od_code_range_l I hZF).mpr ⟨q, hq⟩, hF, hx⟩⟩

def Ob_ext_d (A x : M.Domain) : Prop := ∃ n, ∃ φ : BinarySchema n, ∃ ρ : Env M n,
  (∀ i, M.IsOrdinal (ρ.bound i)) ∧ ∀ y, φ.denote ρ A y ↔ y = x

theorem ob_source_l (hZF : M.Models ZF) {n} (φ : BinarySchema n) (ρ : Env M n)
    (hρ : ∀ i, M.IsOrdinal (ρ.bound i)) {A x} (h : ∀ y, φ.denote ρ A y ↔ y = x) : Ob_d A x := by
  let I := kpair_interpretation_l M hZF.1 (KP.exists_pair (ZF.modelsKP hZF))
  exact (ob_decode_l I hZF.1).mpr (od_graph_exists_l hZF I φ ρ hρ h)

/-- 包括非标准模型在内，固定 A 的内部定义仍对应标准原公式。 -/
theorem ob_iff_external_l (hZF : M.Models ZF) {A x : M.Domain} : Ob_d A x ↔ Ob_ext_d A x := by
  constructor
  · intro h
    let I := kpair_interpretation_l M hZF.1 (KP.exists_pair (ZF.modelsKP hZF))
    obtain ⟨q, hq⟩ := (ob_code_l I hZF).mp h
    let φ : BinarySchema 1 := { body := ob_eval_m (.bound 2) (.bound 1) .newest }
    let ρ : Env M 1 := ⟨fun _ => q, fun _ => q⟩
    have ho : M.IsOrdinal q := hq.elim fun _ h => od_eval_ordinal_l I hZF h.1
    exact ⟨1, φ, ρ, fun _ => ho, fun y => (ob_eval_sat_l I hZF.1 _ _ _ _).trans
      ⟨fun hy => ob_eval_unique_l I hZF hy hq, fun he => he.symm ▸ hq⟩⟩
  · exact fun ⟨_, φ, ρ, hρ, h⟩ => ob_source_l hZF φ ρ hρ h

theorem ob_parameter_l (hZF : M.Models ZF) (A : M.Domain) : Ob_d A A := by
  let φ : BinarySchema 0 := { body := Formula.extensionalEq .newest (.bound 1) }
  exact ob_source_l hZF φ ⟨Fin.elim0, fun _ => A⟩ (fun i => Fin.elim0 i)
    (fun _ => Formula.satisfies_extensionalEq_iff_eq hZF.1 _ _ _)

theorem ob_ordinal_l (hZF : M.Models ZF) (A : M.Domain) {x} (hx : M.IsOrdinal x) : Ob_d A x := by
  let φ : BinarySchema 1 := { body := Formula.extensionalEq .newest (.bound 2) }
  exact ob_source_l hZF φ ⟨fun _ => x, fun _ => x⟩ (fun _ => hx)
    (fun _ => Formula.satisfies_extensionalEq_iff_eq hZF.1 _ _ _)

end YesMetaZFC.SetTheory.InnerModel
