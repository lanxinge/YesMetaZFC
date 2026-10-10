import YesMetaZFC.Model.Forcing.Proper.Base
import YesMetaZFC.Model.Forcing.Internal.Maximum.Basic
import YesMetaZFC.Model.Forcing.Internal.Reflection.Countermodel

/-! # proper 后继的统一 club 名称

从被迫 proper 的原公式，先由 ZF 语义后果取得 club 的存在力迫，再连续应用
最大值原理。输出的内部 ω、底集与 club 名称在原条件上同时满足精确见证规格。
-/

namespace YesMetaZFC.Model.Forcing.Internal
open SetTheory SetTheory.Definitional.Project
universe u

def pr_name_body_m : Formula 1 5 := .conj (Formula.isOmega (.bound 2))
  (pr_base_m (.bound 2) (.bound 3) (.bound 4) (.bound 3) (.bound 1) .newest)
@[simp] theorem pr_name_body_closed_l : pr_name_body_m.FreeClosed := by
  simp only [pr_name_body_m, Definitional.Formula.FreeClosed]
  exact ⟨Formula.isOmega_freeClosed _ rfl, pr_base_m_freeClosed _ _ _ _ _ _ rfl rfl rfl rfl rfl rfl⟩

def pr_name_env_l {M : SetTheory.Structure.{u}} (A T w X C : M.Domain) : Env M 5 :=
  (((ord_env_l M A T).push w).push X).push C

def Pr_name_d (M : SetTheory.Structure.{u}) (B R z b A T w X C : M.Domain) : Prop :=
  Name_d M B A ∧ Name_d M B T ∧ Name_d M B w ∧ Name_d M B X ∧ Name_d M B C ∧
    Forces_d M B R z pr_name_body_m (pr_name_env_l A T w X C) b

def pr_name_m {n} (B R z b A T w X C : Term n) : Formula 1 n :=
  .conj (name_m B A) (.conj (name_m B T) (.conj (name_m B w) (.conj (name_m B X) (.conj (name_m B C)
    (force_at_m pr_name_body_m (Fin.cases C (Fin.cases X (Fin.cases w (Fin.cases A (fun _ => T))))) B R z b)))))

@[simp] theorem pr_name_closed_l {n} (B R z b A T w X C : Term n)
    (hB : B.freeSupport = []) (hR : R.freeSupport = []) (hz : z.freeSupport = []) (hb : b.freeSupport = [])
    (hA : A.freeSupport = []) (hT : T.freeSupport = []) (hw : w.freeSupport = [])
    (hX : X.freeSupport = []) (hC : C.freeSupport = []) : (pr_name_m B R z b A T w X C).FreeClosed := by
  simp only [pr_name_m, Definitional.Formula.FreeClosed]
  exact ⟨name_m_freeClosed _ _ hB hA, name_m_freeClosed _ _ hB hT, name_m_freeClosed _ _ hB hw,
    name_m_freeClosed _ _ hB hX, name_m_freeClosed _ _ hB hC,
    force_at_closed_l _ _ _ _ _ _ pr_name_body_closed_l
      (Fin.cases hC (Fin.cases hX (Fin.cases hw (Fin.cases hA (fun _ => hT))))) hB hR hz hb⟩

theorem pr_name_sat_l {M : SetTheory.Structure.{u}} (hE : Extensional M) {n} (ρ : Env M n)
    (B R z b A T w X C : Term n) : Formula.satisfies ρ (pr_name_m B R z b A T w X C) ↔
      Pr_name_d M (B.eval ρ) (R.eval ρ) (z.eval ρ) (b.eval ρ) (A.eval ρ) (T.eval ρ) (w.eval ρ) (X.eval ρ) (C.eval ρ) := by
  simp only [pr_name_m, Pr_name_d, Formula.satisfies_conj_iff, name_sat_l M hE, force_at_sat_l]
  apply and_congr_right; intro _
  apply and_congr_right; intro _
  apply and_congr_right; intro _
  apply and_congr_right; intro _
  apply and_congr_right; intro _
  exact forces_env_l hE pr_name_body_m pr_name_body_closed_l _ _
    (Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (fun _ => rfl))))) _

variable {M : SetTheory.Structure.{u}} {B R z : M.Domain}

/-- 一次选择在同一条件上成立的全部 proper club 名称。 -/
theorem pr_name_exists_l (O : Cond_order_d M B R z) (hZFC : M.Models ZFC) {b A T}
    (hA : Name_d M B A) (hT : Name_d M B T) (hb : M.mem b B) (hz : b ≠ z)
    (h : Forces_d M B R z (proper_exists_m .newest (.bound 1)) (ord_env_l M A T) b) :
    ∃ w X C, Pr_name_d M B R z b A T w X C := by
  have hZF := ZFC.models_zf_l hZFC
  let ψ : Formula 1 2 := .existsE (.existsE (.existsE pr_name_body_m))
  let φ : Formula 1 2 := .imp (proper_exists_m .newest (.bound 1)) ψ
  have hψ : ψ.FreeClosed := by simpa only [ψ, Definitional.Formula.FreeClosed] using pr_name_body_closed_l
  have hφ : φ.FreeClosed := by
    simp only [φ, Definitional.Formula.FreeClosed]
    exact ⟨proper_exists_m_freeClosed _ _ rfl rfl, hψ⟩
  have valid (N : SetTheory.Structure.{u}) (hN : N.Models ZF) (η : Env N 2) : Formula.satisfies η φ := by
    let I := kpair_interpretation_l N hN.1 (KP.exists_pair (ZF.modelsKP hN))
    apply (Formula.satisfies_imp_iff _ _ _).mpr
    intro hp
    obtain ⟨ω, hω, hProper⟩ := (proper_exists_sat_l I hN.1 η .newest (.bound 1)).mp hp
    obtain ⟨X, C, hC⟩ := pr_base_exists_l I hN hProper
    simp only [ψ, Formula.satisfies_exists_iff]
    refine ⟨ω, X, C, ?_⟩
    exact (Formula.satisfies_conj_iff _ _ _).mpr ⟨(Formula.satisfies_isOmega_iff _ _).mpr hω,
      (pr_base_sat_l I hN.1 _ _ _ _ _ _ _).mpr hC⟩
  let ρ := ord_env_l M A T
  have hρ : ∀ a : Term 2, Name_d M B (a.eval ρ) := by
    intro a
    cases a with
    | free _ => exact hT
    | bound i => exact Fin.cases hA (fun _ => hT) i
  have hImp := forces_zf_valid_l O hZF φ hφ valid ρ (fun i => hρ (.bound i)) hb hz
  have hEx := forces_mp_l hZF.1 (forces_regular_l O hZF _ ρ hρ).1 (forces_regular_l O hZF ψ ρ hρ) hb hz hImp h
  let θ : UnarySchema 2 := {
    body := .existsE (.existsE pr_name_body_m)
    freeClosed := by simpa only [Definitional.Formula.FreeClosed] using pr_name_body_closed_l }
  obtain ⟨w, hw, _, hwF⟩ := maximum_l O hZFC θ ρ (fun i => hρ (.bound i))
  have hwEx := (hwF b hb hz).mp hEx
  let θ' : UnarySchema 3 := {
    body := .existsE pr_name_body_m
    freeClosed := by simpa only [Definitional.Formula.FreeClosed] using pr_name_body_closed_l }
  obtain ⟨X, hX, _, hXF⟩ := maximum_l O hZFC θ' (ρ.push w) (Fin.cases hw (fun i => hρ (.bound i)))
  have hXEx := (hXF b hb hz).mp hwEx
  let θ'' : UnarySchema 4 := { body := pr_name_body_m, freeClosed := pr_name_body_closed_l }
  obtain ⟨C, hC, _, hCF⟩ := maximum_l O hZFC θ'' ((ρ.push w).push X)
    (Fin.cases hX (Fin.cases hw (fun i => hρ (.bound i))))
  exact ⟨w, X, C, hA, hT, hw, hX, hC, (hCF b hb hz).mp hXEx⟩

/-- club 名称证书在任意接受原条件的泛型中成为实际的 proper club 见证。 -/
theorem pr_name_value_l (O : Cond_order_d M B R z) (hZF : M.Models ZF) {U}
    (hU : Generic_d M B R z U) {b A T w X C} (h : Pr_name_d M B R z b A T w X C) (hb : U b)
    {a t v x c : (extension_l M hZF B R z U).Domain}
    (ha : Qval_d M B R z U A a) (ht : Qval_d M B R z U T t) (hv : Qval_d M B R z U w v)
    (hx : Qval_d M B R z U X x) (hc : Qval_d M B R z U C c) :
    (extension_l M hZF B R z U).IsOmega v ∧
      Pr_base_d (kpair_interpretation_l _ (extension_ext_l O hZF hU) (internal_pair_l O hZF hU)) v a t a x c := by
  have hval : Env_val_d hZF (pr_name_env_l A T w X C) (pr_name_env_l a t v x c) := by
    intro u
    cases u with
    | free _ => exact ht
    | bound i => exact Fin.cases hc (Fin.cases hx (Fin.cases hv (Fin.cases ha (fun _ => ht)))) i
  have hv' := (forcing_truth_l O hZF hU pr_name_body_m pr_name_body_closed_l _ _ hval).mp ⟨b, hb, h.2.2.2.2.2⟩
  have hE := extension_ext_l O hZF hU
  exact ⟨(Formula.satisfies_isOmega_iff _ _).mp ((Formula.satisfies_conj_iff _ _ _).mp hv').1,
    (pr_base_sat_l (kpair_interpretation_l _ hE (internal_pair_l O hZF hU)) hE _ _ _ _ _ _ _).mp
      ((Formula.satisfies_conj_iff _ _ _).mp hv').2⟩

/-- 实际 club 名称证书随条件加强保持；此步骤只使用 ZF。 -/
theorem pr_name_lower_l (O : Cond_order_d M B R z) (hZF : M.Models ZF) {b q A T w X C}
    (hb : M.mem b B) (h : Pr_name_d M B R z b A T w X C) (hq : Below_d M B R z q b) :
    Pr_name_d M B R z q A T w X C := by
  have hn : ∀ t : Term 5, Name_d M B (t.eval (pr_name_env_l A T w X C)) := by
    intro t
    cases t with
    | free _ => exact h.2.1
    | bound i => exact Fin.cases h.2.2.2.2.1 (Fin.cases h.2.2.2.1 (Fin.cases h.2.2.1 (Fin.cases h.1 (fun _ => h.2.1)))) i
  exact ⟨h.1, h.2.1, h.2.2.1, h.2.2.2.1, h.2.2.2.2.1,
    (forces_regular_l O hZF pr_name_body_m _ hn).1 b q hb hq h.2.2.2.2.2⟩

end YesMetaZFC.Model.Forcing.Internal
