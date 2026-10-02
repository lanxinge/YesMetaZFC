import YesMetaZFC.SetTheory.InnerModel.OD.Parameters
import YesMetaZFC.SetTheory.Card.FiniteSequenceJoin
import YesMetaZFC.SetTheory.InnerModel.Recursion.Graph

/-! # OD[A] 与 OD(A) 的统一内部参数域

false 只把整个 A 作为参数；true 另外允许 A 中的内部有限序列。后者的长度
属于模型自身的 ω，不把非标准参数列误当作宿主有限列表。
-/
namespace YesMetaZFC.SetTheory.InnerModel
open Definitional.Project
universe u
variable {M : Structure.{u}}

def Oa_seq_d (A s : M.Domain) : Prop := ∃ ω n, M.IsOmega ω ∧ M.mem n ω ∧ Fn0_d n A s
def oa_seq_m {d} (A s : Term d) : Formula 1 d := .existsE (.existsE
  (.conj (Formula.isOmega (.bound 1)) (.conj (.mem .newest (.bound 1)) (fn0_m .newest A.weaken.weaken s.weaken.weaken))))
derive_free_closed oa_seq_m

theorem oa_seq_sat_l (hE : Extensional M) {d} (ρ : Env M d) (A s : Term d) :
    Formula.satisfies ρ (oa_seq_m A s) ↔ Oa_seq_d (A.eval ρ) (s.eval ρ) := by
  simp only [oa_seq_m, Oa_seq_d, Formula.satisfies_exists_iff, Formula.satisfies_conj_iff,
    Formula.satisfies_isOmega_iff, Formula.satisfies_mem_iff, fn0_sat_l hE, Definitional.Term.eval_weaken]
  rfl

theorem oa_seq_decode_l (hZF : M.Models ZF) {ω A s} (hω : M.IsOmega ω) : Oa_seq_d A s ↔
    ∃ n, M.mem n ω ∧ M.IsSetFunctionFromTo (kp_pair_l (ZF.modelsKP hZF)) s n A := by
  constructor
  · rintro ⟨v, n, hv, hn, hf⟩
    exact ⟨n, hv.2 ω hω.1 n hn, fn0_function_l (ZF.modelsKP hZF) hf⟩
  · exact fun ⟨n, hn, hf⟩ => ⟨ω, n, hω, hn, fn0_of_function_l (ZF.modelsKP hZF) hf⟩

def Oa_param_d (k : Bool) (A p : M.Domain) : Prop :=
  if k then ∃ s, Oa_seq_d A s ∧ KPair_d M p A s else p = A
def oa_param_m {d} (k : Bool) (A p : Term d) : Formula 1 d :=
  if k then .existsE (.conj (oa_seq_m A.weaken .newest) (kpair_m p.weaken A.weaken .newest))
  else Formula.extensionalEq p A
@[simp] theorem oa_param_closed_l {d} (k : Bool) (A p : Term d) (hA : A.freeSupport = []) (hp : p.freeSupport = []) :
    (oa_param_m k A p).FreeClosed := by cases k <;> simp -implicitDefEqProofs [oa_param_m, Definitional.Formula.FreeClosed, hA, hp]

theorem oa_param_sat_l (hE : Extensional M) {d} (ρ : Env M d) (k : Bool) (A p : Term d) :
    Formula.satisfies ρ (oa_param_m k A p) ↔ Oa_param_d k (A.eval ρ) (p.eval ρ) := by
  cases k <;> simp only [oa_param_m, Oa_param_d, Bool.false_eq_true, ↓reduceIte,
    Formula.satisfies_exists_iff, Formula.satisfies_conj_iff, oa_seq_sat_l hE, kpair_sat_l M hE,
    Formula.satisfies_extensionalEq_iff_eq hE, Definitional.Term.eval_weaken, Definitional.Term.eval_newest]

def Oa_d (k : Bool) (A x : M.Domain) : Prop := ∃ p, Oa_param_d k A p ∧ Ob_d p x
def oa_m {d} (k : Bool) (A x : Term d) : Formula 1 d := .existsE
  (.conj (oa_param_m k A.weaken .newest) (ob_m .newest x.weaken))
@[simp] theorem oa_closed_l {d} (k : Bool) (A x : Term d) (hA : A.freeSupport = []) (hx : x.freeSupport = []) :
    (oa_m k A x).FreeClosed := by simp -implicitDefEqProofs [oa_m, Definitional.Formula.FreeClosed, hA, hx]

theorem oa_sat_l (hE : Extensional M) {d} (ρ : Env M d) (k : Bool) (A x : Term d) :
    Formula.satisfies ρ (oa_m k A x) ↔ Oa_d k (A.eval ρ) (x.eval ρ) := by
  simp only [oa_m, Oa_d, Formula.satisfies_exists_iff, Formula.satisfies_conj_iff,
    oa_param_sat_l hE, ob_sat_l, Definitional.Term.eval_weaken, Definitional.Term.eval_newest]

theorem oa_bracket_l {A x : M.Domain} : Oa_d false A x ↔ Ob_d A x :=
  ⟨fun ⟨p, hp, h⟩ => (show p = A from hp) ▸ h, fun h => ⟨A, rfl, h⟩⟩

/-- 圆括号的陈述：整个 A 加一条内部有限 A 参数列。 -/
abbrev Op_d (A x : M.Domain) := Oa_d true A x
theorem op_statement_l (hZF : M.Models ZF) {ω A x} (hω : M.IsOmega ω) : Op_d A x ↔
    ∃ n s p, M.mem n ω ∧ M.IsSetFunctionFromTo (kp_pair_l (ZF.modelsKP hZF)) s n A ∧
      KPair_d M p A s ∧ Ob_d p x := by
  exact ⟨fun ⟨p, ⟨s, hs, hp⟩, hx⟩ => ((oa_seq_decode_l hZF hω).mp hs).elim fun n hn =>
      ⟨n, s, p, hn.1, hn.2, hp, hx⟩,
    fun ⟨n, s, p, hn, hs, hp, hx⟩ => ⟨p, ⟨s, (oa_seq_decode_l hZF hω).mpr ⟨n, hn, hs⟩, hp⟩, hx⟩⟩

theorem oa_seed_l (hZF : M.Models ZF) (k : Bool) (A : M.Domain) :
    ∃ p, Oa_param_d k A p ∧ Ob_d p A := by
  cases k with
  | false => exact ⟨A, rfl, ob_parameter_l hZF A⟩
  | true =>
    obtain ⟨ω, hω⟩ := ZF.exists_omega hZF
    obtain ⟨e, he, heω⟩ := hω.1.1
    obtain ⟨p, hp⟩ := (kp_pair_l (ZF.modelsKP hZF)).total A e
    have hs : Oa_seq_d A e := ⟨ω, e, hω, heω,
      (fun z hz => (he z hz).elim), (fun z hz => (he z hz).elim), (fun z hz => (he z hz).elim)⟩
    exact ⟨p, ⟨e, hs, hp⟩, (ob_pair_components_l hZF p (ob_parameter_l hZF p) hp).1⟩

theorem oa_of_ob_l (hZF : M.Models ZF) (k : Bool) {A x : M.Domain} (h : Ob_d A x) : Oa_d k A x := by
  obtain ⟨p, hp, ha⟩ := oa_seed_l hZF k A
  exact ⟨p, hp, ob_trans_l hZF ha h⟩

end YesMetaZFC.SetTheory.InnerModel
