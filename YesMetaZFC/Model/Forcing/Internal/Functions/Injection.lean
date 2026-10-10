import YesMetaZFC.Model.Forcing.Internal.Functions.Basic

/-! # 实际单射名称的原公式证书

证书保存实际名称以及“从该名称单射到指定目标名称”的原公式力迫。
CCC 的可数覆盖与 proper 的可数性反射共用此通用层。
-/

namespace YesMetaZFC.Model.Forcing.Internal
open SetTheory SetTheory.Definitional.Project
universe u

def inj_body_m : Formula 1 3 := Formula.isInjectionFromTo kpair_convention_l .newest (.bound 1) (.bound 2)
@[simp] theorem inj_body_closed_l : inj_body_m.FreeClosed := by
  unfold inj_body_m
  exact Formula.isInjectionFromTo_freeClosed _ _ _ _ rfl rfl rfl

def Inj_name_d (M : SetTheory.Structure.{u}) (B R z b t w f : M.Domain) : Prop :=
  Name_d M B t ∧ Name_d M B w ∧ Name_d M B f ∧ Forces_d M B R z inj_body_m (fn_env_l t w f) b

/-- 单射证书直接提供相同条件上的函数证书。 -/
theorem inj_name_function_l {M : SetTheory.Structure.{u}} {B R z b t w f}
    (h : Inj_name_d M B R z b t w f) : Fn_name_d M B R z b t w f :=
  ⟨h.1, h.2.1, h.2.2.1, ((forces_conj_l _ _ _ _).mp h.2.2.2).1⟩

def inj_name_m {n} (B R z b t w f : Term n) : Formula 1 n :=
  .conj (name_m B t) (.conj (name_m B w) (.conj (name_m B f)
    (force_at_m inj_body_m (Fin.cases f (Fin.cases t (fun _ => w))) B R z b)))
@[simp] theorem inj_name_closed_l {n} (B R z b t w f : Term n)
    (hB : B.freeSupport = []) (hR : R.freeSupport = []) (hz : z.freeSupport = [])
    (hb : b.freeSupport = []) (ht : t.freeSupport = []) (hw : w.freeSupport = []) (hf : f.freeSupport = []) :
    (inj_name_m B R z b t w f).FreeClosed := by
  simp only [inj_name_m, Definitional.Formula.FreeClosed]
  exact ⟨name_m_freeClosed _ _ hB ht, name_m_freeClosed _ _ hB hw, name_m_freeClosed _ _ hB hf,
    force_at_closed_l _ _ _ _ _ _ inj_body_closed_l (Fin.cases hf (Fin.cases ht (fun _ => hw))) hB hR hz hb⟩

theorem inj_name_sat_l {M : SetTheory.Structure.{u}} (hE : Extensional M) {n} (ρ : Env M n) (B R z b t w f : Term n) :
    Formula.satisfies ρ (inj_name_m B R z b t w f) ↔
      Inj_name_d M (B.eval ρ) (R.eval ρ) (z.eval ρ) (b.eval ρ) (t.eval ρ) (w.eval ρ) (f.eval ρ) := by
  simp only [inj_name_m, Inj_name_d, Formula.satisfies_conj_iff, name_sat_l M hE, force_at_sat_l]
  apply and_congr_right; intro _
  apply and_congr_right; intro _
  apply and_congr_right; intro _
  exact forces_env_l hE inj_body_m inj_body_closed_l _ _
    (Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (fun i => Fin.elim0 i)))) _

/-- 单射力迫证书在每个接受其条件的泛型中成为实际集合单射。 -/
theorem inj_name_val_l {M : SetTheory.Structure.{u}} {B R z b t w f}
    (O : Cond_order_d M B R z) (hZF : M.Models ZF) {U} (hU : Generic_d M B R z U)
    (h : Inj_name_d M B R z b t w f) (hb : U b)
    {T W F : (extension_l M hZF B R z U).Domain}
    (ht : Qval_d M B R z U t T) (hw : Qval_d M B R z U w W) (hf : Qval_d M B R z U f F) :
    (extension_l M hZF B R z U).IsSetInjectionFromTo
      (kpair_interpretation_l _ (extension_ext_l O hZF hU) (internal_pair_l O hZF hU)) F T W := by
  have hv : Env_val_d hZF (fn_env_l t w f) (fn_env_l (M := extension_l M hZF B R z U) T W F) := by
    intro v
    cases v with
    | free _ => exact hw
    | bound i => exact Fin.cases hf (Fin.cases ht (fun _ => hw)) i
  exact (Formula.satisfies_isInjectionFromTo_iff _ (extension_ext_l O hZF hU) _ _ _ _).mp
    ((forcing_truth_l O hZF hU inj_body_m inj_body_closed_l _ _ hv).mp ⟨b, hb, h.2.2.2⟩)

end YesMetaZFC.Model.Forcing.Internal
