import YesMetaZFC.Model.Forcing.Reflection.Criterion
import YesMetaZFC.Model.Forcing.Maximum.Bounded
import YesMetaZFC.Model.Forcing.Check.SupportBound
import YesMetaZFC.Model.Forcing.Ground.Collapse
import YesMetaZFC.Model.Forcing.TwoStep.Basic
import YesMetaZFC.Model.Forcing.Names.CheckPools
import YesMetaZFC.Model.Forcing.Embedding.Rank

/-! # 实际函数名称的原公式证书

证书保存实际名称以及“由指定源名称到目标名称的函数”的原公式力迫。
函数值决定、闭力迫的序列反射和单射层共用同一证书。
-/

namespace YesMetaZFC.Model.Forcing.Internal
open SetTheory SetTheory.Definitional.Project
universe u

def fn_body_m : Formula 1 3 := Formula.isFunctionFromTo kpair_convention_l .newest (.bound 1) (.bound 2)
@[simp] theorem fn_body_closed_l : fn_body_m.FreeClosed := by
  unfold fn_body_m
  exact Formula.isFunctionFromTo_freeClosed _ _ _ _ rfl rfl rfl

def fn_env_l {M : SetTheory.Structure.{u}} (t w f : M.Domain) : Env M 3 :=
  ((⟨fun _ => w, fun _ => w⟩ : Env M 1).push t).push f

/-- 函数环境的三个槽位均由实际名称填充。 -/
theorem fn_env_names_l {M : SetTheory.Structure.{u}} {B t w f : M.Domain}
    (ht : Name_d M B t) (hw : Name_d M B w) (hf : Name_d M B f) :
    ∀ v : Term 3, Name_d M B (v.eval (fn_env_l t w f)) := by
  intro v
  cases v with
  | free _ => exact hw
  | bound i => exact Fin.cases hf (Fin.cases ht (fun _ => hw)) i

def Fn_name_d (M : SetTheory.Structure.{u}) (B R z b t w f : M.Domain) : Prop :=
  Name_d M B t ∧ Name_d M B w ∧ Name_d M B f ∧ Forces_d M B R z fn_body_m (fn_env_l t w f) b

def fn_name_m {n} (B R z b t w f : Term n) : Formula 1 n :=
  .conj (name_m B t) (.conj (name_m B w) (.conj (name_m B f)
    (force_at_m fn_body_m (Fin.cases f (Fin.cases t (fun _ => w))) B R z b)))
@[simp] theorem fn_name_closed_l {n} (B R z b t w f : Term n)
    (hB : B.freeSupport = []) (hR : R.freeSupport = []) (hz : z.freeSupport = [])
    (hb : b.freeSupport = []) (ht : t.freeSupport = []) (hw : w.freeSupport = []) (hf : f.freeSupport = []) :
    (fn_name_m B R z b t w f).FreeClosed := by
  simp only [fn_name_m, Definitional.Formula.FreeClosed]
  exact ⟨name_m_freeClosed _ _ hB ht, name_m_freeClosed _ _ hB hw, name_m_freeClosed _ _ hB hf,
    force_at_closed_l _ _ _ _ _ _ fn_body_closed_l (Fin.cases hf (Fin.cases ht (fun _ => hw))) hB hR hz hb⟩

theorem fn_name_sat_l {M : SetTheory.Structure.{u}} (hE : Extensional M) {n} (ρ : Env M n) (B R z b t w f : Term n) :
    Formula.satisfies ρ (fn_name_m B R z b t w f) ↔
      Fn_name_d M (B.eval ρ) (R.eval ρ) (z.eval ρ) (b.eval ρ) (t.eval ρ) (w.eval ρ) (f.eval ρ) := by
  simp only [fn_name_m, Fn_name_d, Formula.satisfies_conj_iff, name_sat_l M hE, force_at_sat_l]
  apply and_congr_right; intro _
  apply and_congr_right; intro _
  apply and_congr_right; intro _
  exact forces_env_l hE fn_body_m fn_body_closed_l _ _
    (Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (fun i => Fin.elim0 i)))) _

/-- 函数力迫证书在每个接受其条件的泛型中成为实际集合函数。 -/
theorem fn_name_val_l {M : SetTheory.Structure.{u}} {B R z b t w f}
    (O : Cond_order_d M B R z) (hZF : M.Models ZF) {U} (hU : Generic_d M B R z U)
    (h : Fn_name_d M B R z b t w f) (hb : U b)
    {T W F : (extension_l M hZF B R z U).Domain}
    (ht : Qval_d M B R z U t T) (hw : Qval_d M B R z U w W) (hf : Qval_d M B R z U f F) :
    (extension_l M hZF B R z U).IsSetFunctionFromTo
      (kpair_interpretation_l _ (extension_ext_l O hZF hU) (internal_pair_l O hZF hU)) F T W := by
  have hv : Env_val_d hZF (fn_env_l t w f) (fn_env_l (M := extension_l M hZF B R z U) T W F) := by
    intro v
    cases v with
    | free _ => exact hw
    | bound i => exact Fin.cases hf (Fin.cases ht (fun _ => hw)) i
  exact (Formula.satisfies_isFunctionFromTo_iff _ (extension_ext_l O hZF hU) _ _ _ _).mp
    ((forcing_truth_l O hZF hU fn_body_m fn_body_closed_l _ _ hv).mp ⟨b, hb, h.2.2.2⟩)

end YesMetaZFC.Model.Forcing.Internal

/-! ## 实际单射名称的原公式证书

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

/-! ## 被迫函数、单射与传递容器的局部规则

直接消去原公式中的量词与蕴涵，取得同条件的单射消去和传递性。
名称在规范目标中的函数值可在任意给定条件以下决定为旧索引。
-/

namespace YesMetaZFC.Model.Forcing.Internal
open SetTheory SetTheory.Definitional.Project
universe u
variable {M : SetTheory.Structure.{u}} {B R z : M.Domain}

private theorem push_l {n} {ρ : Env M n} (hρ : ∀ t : Term n, Name_d M B (t.eval ρ))
    {s} (hs : Name_d M B s) : ∀ t : Term (n+1), Name_d M B (t.eval (ρ.push s)) := by
  intro t
  cases t with
  | free i => exact hρ (.free i)
  | bound i => exact Fin.cases hs (fun i => hρ (.bound i)) i

theorem force_entry_l (hE : Extensional M) {n} (ρ : Env M n) (p : M.Domain) (s t F : Term n) :
    Forces_d M B R z (entry_m s t F) ρ p ↔ Rel_force_d M B R z (F.eval ρ) p (s.eval ρ) (t.eval ρ) := by
  have h : rel_at_m s t F = entry_m s t F := by
    change (entry_m (.bound 1) .newest (.bound 2) : Formula 1 3).bind
      (Fin.cases t (Fin.cases s (fun _ => F))) = entry_m s t F
    simp [entry_m, Formula.orderedPairMem, kpair_convention_l, kpair_m, Formula.isSingleton,
      Formula.isUnorderedPair, Formula.extensionalEq, Definitional.Formula.bind,
      Definitional.Term.bind, Definitional.Term.liftSubstitution, Definitional.Term.newest,
      Definitional.Term.weaken, Definitional.Term.rename, Definitional.TermVector.bind,
      Formula.pairArguments, fin_cases, Fin.cases, Fin.induction, Fin.induction.go]
  rw [← h]
  exact force_rel_at_l M hE ρ p s t F

def Nvalue_d (M : SetTheory.Structure.{u}) (B R z b f p s i : M.Domain) : Prop :=
  ∃ c, Check_d M b i c ∧ Rel_force_d M B R z f p s c

def nvalue_m {n} (B R z b f p s i : Term n) : Formula 1 n :=
  .existsE (.conj (check_m b.weaken i.weaken .newest)
    (rel_force_m B.weaken R.weaken z.weaken f.weaken p.weaken s.weaken .newest))
derive_free_closed nvalue_m

theorem nvalue_sat_l (hE : Extensional M) {n} (ρ : Env M n) (B R z b f p s i : Term n) :
    Formula.satisfies ρ (nvalue_m B R z b f p s i) ↔ Nvalue_d M (B.eval ρ) (R.eval ρ)
      (z.eval ρ) (b.eval ρ) (f.eval ρ) (p.eval ρ) (s.eval ρ) (i.eval ρ) := by
  simp only [nvalue_m, Nvalue_d, Formula.satisfies_exists_iff, Formula.satisfies_conj_iff,
    check_sat_l M hE, rel_force_sat_l M hE, Definitional.Term.eval_weaken, Definitional.Term.eval_newest]

variable (O : Cond_order_d M B R z) (hZF : M.Models ZF)
include O hZF

theorem forced_transitive_l {A s t p} (hA : Name_d M B A) (hs : Name_d M B s) (ht : Name_d M B t)
    (hp : M.mem p B) (hz : p ≠ z)
    (h : Forces_d M B R z (Formula.isTransitive (.bound 0)) (⟨fun _ => A, fun _ => A⟩ : Env M 1) p)
    (hsA : Mem_force_d M B R z p s A) (hts : Mem_force_d M B R z p t s) : Mem_force_d M B R z p t A := by
  let ρ : Env M 1 := ⟨fun _ => A, fun _ => A⟩
  have hρ : ∀ v : Term 1, Name_d M B (v.eval ρ) := by intro v; cases v <;> exact hA
  have h₁ := (forces_all_l hZF.1 _ ρ p).mp h s hs
  have h₂ := forces_mp_l hZF.1 (forces_regular_l O hZF _ _ (push_l hρ hs)).1
    (forces_regular_l O hZF _ _ (push_l hρ hs)) hp hz h₁ ((forces_mem_l hZF.1 _ _ _ p).mpr hsA)
  have h₃ := (forces_all_l hZF.1 _ _ p).mp h₂ t ht
  exact (forces_mem_l hZF.1 _ _ _ p).mp (forces_mp_l hZF.1
    (forces_regular_l O hZF _ _ (push_l (push_l hρ hs) ht)).1
    (forces_regular_l O hZF _ _ (push_l (push_l hρ hs) ht)) hp hz h₃ ((forces_mem_l hZF.1 _ _ _ p).mpr hts))

/-- 被迫单射在同一条件上把相同值的两个名称判为相等。 -/
theorem inj_name_eq_l {b T w f p s t v} (h : Inj_name_d M B R z b T w f)
    (hb : M.mem b B) (hp : Below_d M B R z p b)
    (hs : Name_d M B s) (ht : Name_d M B t) (hv : Name_d M B v)
    (hsv : Rel_force_d M B R z f p s v) (htv : Rel_force_d M B R z f p t v) : Eq_force_d M B R z p s t := by
  let ρ := fn_env_l T w f
  have hρ := fn_env_names_l h.1 h.2.1 h.2.2.1
  have hf := (forces_regular_l O hZF inj_body_m ρ hρ).1 b p hb hp h.2.2.2
  have hinj := ((forces_conj_l _ _ ρ p).mp hf).2
  have h₁ := (forces_all_l hZF.1 _ _ p).mp ((forces_all_l hZF.1 _ _ p).mp
    ((forces_all_l hZF.1 _ _ p).mp hinj s hs) t ht) v hv
  have hn := push_l (push_l (push_l hρ hs) ht) hv
  have h₂ := forces_mp_l hZF.1 (forces_regular_l O hZF _ _ hn).1
    (forces_regular_l O hZF _ _ hn) hp.1 hp.2.1 h₁
      ((forces_conj_l _ _ _ p).mpr ⟨(force_entry_l hZF.1 _ p _ _ _).mpr hsv, (force_entry_l hZF.1 _ p _ _ _).mpr htv⟩)
  exact (code_eq_l M hZF.1 B R z _ _ _ p).mp h₂

/-- 函数证书在同一正条件上把同一输入的两个输出判为相等。 -/
theorem fn_name_eq_l {b T w f p s t v} (h : Fn_name_d M B R z b T w f)
    (hb : M.mem b B) (hp : Below_d M B R z p b)
    (hs : Name_d M B s) (ht : Name_d M B t) (hv : Name_d M B v)
    (hst : Rel_force_d M B R z f p s t) (hsv : Rel_force_d M B R z f p s v) :
    Eq_force_d M B R z p t v := by
  let ρ := fn_env_l T w f
  have hρ := fn_env_names_l h.1 h.2.1 h.2.2.1
  have hf := (forces_regular_l O hZF fn_body_m ρ hρ).1 b p hb hp h.2.2.2
  have hu := ((forces_conj_l _ _ ρ p).mp (((forces_conj_l _ _ ρ p).mp hf).1)).2
  have h₁ := (forces_all_l hZF.1 _ _ p).mp ((forces_all_l hZF.1 _ _ p).mp
    ((forces_all_l hZF.1 _ _ p).mp hu s hs) t ht) v hv
  have hn := push_l (push_l (push_l hρ hs) ht) hv
  have h₂ := forces_mp_l hZF.1 (forces_regular_l O hZF _ _ hn).1
    (forces_regular_l O hZF _ _ hn) hp.1 hp.2.1 h₁
      ((forces_conj_l _ _ _ p).mpr ⟨(force_entry_l hZF.1 _ p _ _ _).mpr hst,
        (force_entry_l hZF.1 _ p _ _ _).mpr hsv⟩)
  exact (code_eq_l M hZF.1 B R z _ _ _ p).mp h₂

/-- 给定条件下的名称成员，其函数值可在该条件以下决定为规范旧索引。 -/
theorem fn_name_index_l {b c T w f μ p s} (h : Fn_name_d M B R z b T w f)
    (hb : M.mem b B) (hc : M.mem c B) (hw : Check_d M c μ w) (hp : Below_d M B R z p b)
    (hs : Name_d M B s) (hsT : Mem_force_d M B R z p s T) :
    ∃ q i, Below_d M B R z q p ∧ M.mem i μ ∧ Nvalue_d M B R z c f q s i := by
  let ρ := fn_env_l T w f
  have hρ := fn_env_names_l h.1 h.2.1 h.2.2.1
  have hFn := (forces_regular_l O hZF fn_body_m ρ hρ).1 b p hb hp h.2.2.2
  have hTot : Forces_d M B R z (Formula.forallMem (.bound 1) (Formula.existsMem (.bound 3)
      (entry_m (.bound 1) .newest (.bound 2)))) ρ p :=
    ((forces_conj_l _ _ ρ p).mp (((forces_conj_l _ _ ρ p).mp hFn).2)).2
  have h₁ := (forces_all_l hZF.1 _ _ p).mp hTot s hs
  have h₂ := forces_mp_l hZF.1 (forces_regular_l O hZF _ _ (push_l hρ hs)).1
    (forces_regular_l O hZF _ _ (push_l hρ hs)) hp.1 hp.2.1 h₁ ((forces_mem_l hZF.1 _ _ _ p).mpr hsT)
  obtain ⟨q, hqp, v, hv, hq⟩ := forces_exists_dense_l hZF.1 h₂ p (below_refl_l O hp.1 hp.2.1)
  obtain ⟨hcm, hfc⟩ := (forces_conj_l _ _ _ q).mp hq
  have hcW : Mem_force_d M B R z q v w :=
    (forces_mem_l hZF.1 .newest (.bound 4) ((ρ.push s).push v) q).mp hcm
  obtain ⟨r, a, d, hrq, had, hrd, hca⟩ := hcW.2 q (below_refl_l O hqp.1 hqp.2.1)
  obtain ⟨_, i, hi, hia⟩ := (check_entry_l M hZF.1 (check_ind_l M hZF)
    (KP.exists_pair (ZF.modelsKP hZF)) hw a d).mp had
  have ha := check_name_l M (check_range_l M hZF) hc hia
  have hfc' : Rel_force_d M B R z f q s v :=
    (force_entry_l hZF.1 ((ρ.push s).push v) q (.bound 1) .newest (.bound 2)).mp hfc
  have hfr := (rel_force_regular_l O hZF h.2.2.1 hs hv).1 q r hqp.1 hrq hfc'
  let φ : UnarySchema 2 := { body := entry_m (.bound 1) .newest (.bound 2) }
  -- 先转成原 entry 公式，再沿名称相等运输。
  have hφ : Forces_d M B R z φ.body ((ord_env_l M s f).push v) r :=
    (force_entry_l hZF.1 ((ord_env_l M s f).push v) r (.bound 1) .newest (.bound 2)).mpr hfr
  have hφ' := (forces_name_congr_l O hZF φ (ord_env_l M s f)
    (Fin.cases hs (fun _ => h.2.2.1)) hv ha hrq.1 hrq.2.1 hca).mp hφ
  have hfa : Rel_force_d M B R z f r s a :=
    (force_entry_l hZF.1 ((ord_env_l M s f).push a) r (.bound 1) .newest (.bound 2)).mp hφ'
  exact ⟨r, i, below_trans_l O hp.1 hrq hqp, hi, a, hia, hfa⟩

/-- 将规范目标的标签移到当前条件；只替换目标名称，不改变单射或定义域。 -/
theorem inj_name_check_l {b c T μ w f} (h : Inj_name_d M B R z b T w f)
    (hb : M.mem b B) (hz : b ≠ z) (hc : M.mem c B) (hbc : Entry_d M b c R)
    (hw : Check_d M c μ w) : ∃ v, Check_d M b μ v ∧ Inj_name_d M B R z b T v f := by
  obtain ⟨v, hv, hvN, _⟩ := zf_check_l M hZF hb μ
  have hwv := check_force_bases_l O hZF hc hb hw hv hb hbc (O.refl b hb)
  have hρ := fn_env_names_l h.1 h.2.1 h.2.2.1
  have hη : ∀ a : Term 3, Name_d M B (a.eval (fn_env_l T v f)) := by
    intro a
    cases a with
    | free _ => exact hvN
    | bound i => exact Fin.cases h.2.2.1 (Fin.cases h.1 (fun _ => hvN)) i
  have he : ∀ a : Term 3, Eq_force_d M B R z b (a.eval (fn_env_l T w f)) (a.eval (fn_env_l T v f)) := by
    intro a
    cases a with
    | free _ => exact hwv
    | bound i =>
      exact Fin.cases (eq_force_refl_l O hZF hb h.2.2.1)
        (Fin.cases (eq_force_refl_l O hZF hb h.1) (fun _ => hwv)) i
  exact ⟨v, hv, h.1, hvN, h.2.2.1,
    (forces_congr_below_l O hZF inj_body_m _ _ hρ hη hb he b (below_refl_l O hb hz)).mp h.2.2.2⟩

end YesMetaZFC.Model.Forcing.Internal

/-! ## 完整函数解释的原模型名字证书

把扩张中的函数见证改写成原模型中的名字、检查名字及被泛型接受的力迫条件。
每条背景图边由原模型的关系力迫读取；反向解释恢复同一个完整函数图。
-/
namespace YesMetaZFC.Model.Forcing.Internal
open SetTheory SetTheory.Definitional.Project SetTheory.InnerModel SetTheory.Internal
universe u v
variable {N : Structure.{u}} {M : Structure.{v}}

def Nentry_d (B R z b τ a c p : N.Domain) : Prop := ∃ s t,
  Check_d N b a s ∧ Check_d N b c t ∧ Rel_force_d N B R z τ p s t

def nentry_m {d} (B R z b τ a c p : Term d) : Formula 1 d := set[d] ⟪∃ s t,
  ⌜check_m⌝ₚ(⌜b⌝ₛ,⌜a⌝ₛ,s) ∧ ⌜check_m⌝ₚ(⌜b⌝ₛ,⌜c⌝ₛ,t) ∧
    ⌜rel_force_m⌝ₚ(⌜B⌝ₛ,⌜R⌝ₛ,⌜z⌝ₛ,⌜τ⌝ₛ,⌜p⌝ₛ,s,t)⟫
derive_free_closed nentry_m

theorem nentry_sat_l (hE : Extensional N) {d} (ρ : Env N d) (B R z b τ a c p : Term d) :
    Formula.satisfies ρ (nentry_m B R z b τ a c p) ↔
      Nentry_d (B.eval ρ) (R.eval ρ) (z.eval ρ) (b.eval ρ) (τ.eval ρ) (a.eval ρ) (c.eval ρ) (p.eval ρ) := by
  simp only [nentry_m,Nentry_d,Formula.satisfies_exists_iff,Formula.satisfies_conj_iff,
    check_sat_l N hE,rel_force_sat_l N hE,Definitional.Term.eval_weaken]
  rfl

def Fn_code_d (k : N.Domain → M.Domain) (B R z D A : N.Domain) (G : N.Domain → Prop) (x : M.Domain) : Prop :=
  ∃ b p t w τ, G b ∧ G p ∧ Check_d N b D t ∧ Check_d N b A w ∧ Fn_name_d N B R z p t w τ ∧
    ∀ i y, Entry_d M i y x ↔ ∃ a c, k a = i ∧ k c = y ∧ ∃ q, G q ∧ Nentry_d B R z b τ a c q

variable (hN : N.Models ZF) {B R z : N.Domain} (O : Cond_order_d N B R z)
  {G : N.Domain → Prop} (generic : Generic_d N B R z G)
local notation "E" => extension_l N hN B R z G
include O generic

theorem nentry_truth_l {b τ : N.Domain} (hb : G b) {y : (E).Domain} (value : Qval_d N B R z G τ y)
    (j : N.Domain → (E).Domain) (checks : ∀ a t, Check_d N b a t → Qval_d N B R z G t (j a)) (a c : N.Domain) :
    (∃ p, G p ∧ Nentry_d B R z b τ a c p) ↔ Entry_d E (j a) (j c) y := by
  constructor
  · rintro ⟨p,hp,s,t,cs,ct,force⟩
    exact (rel_force_truth_l O hN generic (checks a s cs) (checks c t ct) value).mp ⟨p,hp,force⟩
  · intro edge
    obtain ⟨s,cs,_,_⟩ := zf_check_l N hN (generic.proper b hb).1 a
    obtain ⟨t,ct,_,_⟩ := zf_check_l N hN (generic.proper b hb).1 c
    obtain ⟨p,hp,force⟩ := (rel_force_truth_l O hN generic (checks a s cs) (checks c t ct) value).mpr edge
    exact ⟨p,hp,s,t,cs,ct,force⟩

/-- 固定原名字及任意已接受基准，真值定理给出该名字的函数性条件。 -/
theorem fn_name_of_value_l {D A b τ : N.Domain} (hb : G b)
    (j : N.Domain → (E).Domain) (ground : ∀ a, Gval_d N B R z G a (j a))
    {y : (E).Domain} (value : Qval_d N B R z G τ y) (fn : Fn0_d (j D) (j A) y) :
    ∃ p t w, G p ∧ Check_d N b D t ∧ Check_d N b A w ∧ Fn_name_d N B R z p t w τ := by
  have hE := preserves_zf_l O hN generic
  obtain ⟨j₀,checks,_,_⟩ := check_map_l O hN generic hb
  have eq : j₀ = j := funext fun a => (gval_check_map_l O hN generic hb j₀ checks a (j a)).mp (ground a)
  subst j₀
  obtain ⟨t,ct,_,_⟩ := zf_check_l N hN (generic.proper b hb).1 D
  obtain ⟨w,cw,_,_⟩ := zf_check_l N hN (generic.proper b hb).1 A
  have values : Env_val_d hN (fn_env_l t w τ) (fn_env_l (j D) (j A) y) := by
    intro t
    cases t with
    | free _ => exact checks A w cw
    | bound i => exact Fin.cases value (Fin.cases (checks D t ct) (fun _ => checks A w cw)) i
  have truth : Formula.satisfies (fn_env_l (j D) (j A) y) fn_body_m :=
    (Formula.satisfies_isFunctionFromTo_iff _ (extension_ext_l O hN generic) _ _ _ _).mpr
      (fn0_function_l (ZF.modelsKP hE) fn)
  obtain ⟨p,hp,force⟩ := (forcing_truth_l O hN generic fn_body_m fn_body_closed_l _ _ values).mpr truth
  exact ⟨p,t,w,hp,ct,cw,qval_name_l (checks D t ct),qval_name_l (checks A w cw),qval_name_l value,force⟩

/-- 任意已有的函数解释都实际产生原模型名字；不用指定名字覆盖库。 -/
theorem fn_code_of_value_l (k : N.Domain → M.Domain) {D A : N.Domain} {x : M.Domain}
    (j : N.Domain → (E).Domain) (ground : ∀ a, Gval_d N B R z G a (j a))
    {y : (E).Domain} (fn : Fn0_d (j D) (j A) y) (read : Fn_read_d k j y x) :
    Fn_code_d k B R z D A G x := by
  obtain ⟨b,hb⟩ := generic.inhabited
  obtain ⟨τ,_,value⟩ := value_name_l y
  obtain ⟨p,t,w,hp,ct,cw,typed⟩ := fn_name_of_value_l hN O generic hb j ground value fn
  obtain ⟨j₀,checks,_,_⟩ := check_map_l O hN generic hb
  have eq : j₀ = j := funext fun a => (gval_check_map_l O hN generic hb j₀ checks a (j a)).mp (ground a)
  subst j₀
  refine ⟨b,p,t,w,τ,hb,hp,ct,cw,typed,?_⟩
  intro i c
  exact (read i c).trans (exists_congr fun a => exists_congr fun b => and_congr_right fun _ =>
    and_congr_right fun _ => (nentry_truth_l hN O generic hb value j checks a b).symm)

/-- 名字证书在原泛型扩张中恢复实际函数及完整背景图解释。 -/
theorem Fn_code_d.value_l (k : N.Domain → M.Domain) {D A : N.Domain} {x : M.Domain}
    (code : Fn_code_d k B R z D A G x) :
    ∃ j : N.Domain → (E).Domain, Function.Injective j ∧
      (∀ a, Gval_d N B R z G a (j a)) ∧ ∃ y, Fn0_d (j D) (j A) y ∧ Fn_read_d k j y x := by
  obtain ⟨b,p,t,w,τ,hb,hp,ct,cw,fn,read⟩ := code
  obtain ⟨j,checks,_,inj⟩ := check_map_l O hN generic hb
  obtain ⟨y,value⟩ := name_value_l (R := R) (z := z) (U := G) fn.2.2.1
  have hE := preserves_zf_l O hN generic
  have function := fn_name_val_l O hN generic fn hp (checks D t ct) (checks A w cw) value
  refine ⟨j,inj,fun a => (gval_check_map_l O hN generic hb j checks a (j a)).mpr rfl,
    y,fn0_of_function_l (ZF.modelsKP hE) function,?_⟩
  intro i c
  exact (read i c).trans (exists_congr fun a => exists_congr fun b => and_congr_right fun _ =>
    and_congr_right fun _ => nentry_truth_l hN O generic hb value j checks a b)

end YesMetaZFC.Model.Forcing.Internal

/-! ## 全部实数的规范条件名字

在 ω² 的检查子集名字库中，按实际条件“该名字为 ω→ω 函数”分离。
名字无需全局被迫为实数；原接受条件保留解释，故规范库覆盖每个新实数。
-/
namespace YesMetaZFC.Model.Forcing.Internal
open SetTheory SetTheory.Definitional.Project SetTheory.InnerModel
universe u
variable {M : Structure.{u}} (I : kpair_convention_l.Interpretation M)

structure Rn_data_d (B R b ω D t W r : M.Domain) : Prop where
  product : M.IsCartesianProduct I D ω ω
  check : Check_d M b ω t
  pool : Ck_pool_d B b D W
  name : Name_d M B r
  entries : ∀ s p, Entry_d M s p r ↔ M.mem s W ∧ M.mem p B ∧ Fn_name_d M B R B p t t s

def Rn_d (B R b ω r : M.Domain) : Prop := ∃ D t W, Rn_data_d I B R b ω D t W r

variable (hZF : M.Models ZF)
local notation "J" => kpair_interpretation_l M (And.left hZF) (KP.exists_pair (ZF.modelsKP hZF))

theorem rn_exists_l {B R b ω : M.Domain} (hb : M.mem b B) : ∃ r, Rn_d J B R b ω r := by
  obtain ⟨D,product⟩ := ZF.exists_cartesianProduct hZF J ω ω
  obtain ⟨t,check,_,_⟩ := zf_check_l M hZF hb ω
  obtain ⟨W,pool⟩ := ck_pool_exists_l hZF hb D
  let ρ : Env M 3 := ⟨fun i => [B,R,t].get i,fun _ => t⟩
  let φ : BinarySchema 3 := {
    body := fn_name_m (.bound 2) (.bound 3) (.bound 2) .newest (.bound 4) (.bound 4) (.bound 1)
    freeClosed := fn_name_closed_l _ _ _ _ _ _ _ rfl rfl rfl rfl rfl rfl rfl }
  obtain ⟨r,nr,_,entries⟩ := name_comp_l M hZF φ ρ B W (fun s hs => pool.name_l hZF hb hs)
  exact ⟨r,D,t,W,product,check,pool,nr,fun s p => (entries s p).trans
    (and_congr_right fun _ => and_congr_right fun _ => fn_name_sat_l hZF.1 ((ρ.push s).push p) ..)⟩

theorem Rn_data_d.value_l {B R b ω D t W r : M.Domain} (h : Rn_data_d J B R b ω D t W r)
    (O : Cond_order_d M B R B) {G : M.Domain → Prop} (g : Generic_d M B R B G) (hb : G b) :
    let E := extension_l M hZF B R B G
    ∃ j : M.Domain → E.Domain, (∀ a, Gval_d M B R B G a (j a)) ∧
      ∃ Z, Qval_d M B R B G r Z ∧ ∀ x, E.mem x Z ↔ Fn0_d (j ω) (j ω) x := by
  let E := extension_l M hZF B R B G
  have hE := preserves_zf_l O hZF g
  obtain ⟨j,checks,full,inj⟩ := check_map_l O hZF g hb
  have jt := checks ω t h.check
  obtain ⟨Z,rz⟩ := name_value_l (R := R) (z := B) (U := G) h.name
  refine ⟨j,fun a => (gval_check_map_l O hZF g hb j checks a (j a)).mpr rfl,Z,rz,fun x => ?_⟩
  constructor
  · intro hx
    obtain ⟨s,p,sp,hp,sx⟩ := (qval_mem_l O hZF g rz).mp hx
    exact fn0_of_function_l (ZF.modelsKP hE) (fn_name_val_l O hZF g ((h.entries s p).mp sp).2.2 hp jt jt sx)
  · intro fx
    obtain ⟨a,ca,_,_⟩ := zf_check_l M hZF (g.proper b hb).1 D
    have product := image_product_l (hEN := hE.1) (hPN := KP.exists_pair (ZF.modelsKP hE)) j inj full h.product
    have fn := fn0_function_l (ZF.modelsKP hE) fx
    have sub : E.MemberSubset x (j D) := by
      intro v hv
      obtain ⟨i,y,pair⟩ := fn.1.1 v hv
      exact (product v).mpr ⟨i,fn.input_mem_of_pairMember ⟨v,pair,hv⟩,
        y,fn.output_mem_of_pairMember ⟨v,pair,hv⟩,pair⟩
    obtain ⟨s,hs,sx⟩ := h.pool.represent_l hZF O (g.proper b hb).1 ca g (checks D a ca) sub
    have env : Env_val_d hZF (fn_env_l t t s) (fn_env_l (j ω) (j ω) x) := by
      intro v
      cases v with
      | free _ => exact jt
      | bound i => exact Fin.cases sx (Fin.cases jt (fun _ => jt)) i
    have truth : Formula.satisfies (fn_env_l (j ω) (j ω) x) fn_body_m :=
      (Formula.satisfies_isFunctionFromTo_iff _ hE.1 _ _ _ _).mpr fn
    obtain ⟨p,hp,force⟩ := (forcing_truth_l O hZF g fn_body_m fn_body_closed_l _ _ env).mpr truth
    exact (qval_mem_l O hZF g rz).mpr ⟨s,p,(h.entries s p).mpr
      ⟨hs,(g.proper p hp).1,qval_name_l jt,qval_name_l jt,qval_name_l sx,force⟩,hp,sx⟩

end YesMetaZFC.Model.Forcing.Internal

/-! ## 规范实数名字的一阶规格及唯一性

条件域、顺序、检查基点和 ω 唯一决定名字。这个实际公式可用于对内部
全部有限前缀作替代，外部不选择一列名字。
-/
namespace YesMetaZFC.Model.Forcing.Internal
open SetTheory SetTheory.Definitional.Project
universe u
variable {M : Structure.{u}} (I : kpair_convention_l.Interpretation M)

def rn_data_m {n} (B R b ω D t W r : Term n) : Formula 1 n := set[n] ⟪
  ⌜Formula.isCartesianProduct kpair_convention_l⌝ₚ(⌜D⌝ₛ,⌜ω⌝ₛ,⌜ω⌝ₛ) ∧
  ⌜check_m⌝ₚ(⌜b⌝ₛ,⌜ω⌝ₛ,⌜t⌝ₛ) ∧ ⌜ck_pool_m⌝ₚ(⌜B⌝ₛ,⌜b⌝ₛ,⌜D⌝ₛ,⌜W⌝ₛ) ∧
  ⌜name_m⌝ₚ(⌜B⌝ₛ,⌜r⌝ₛ) ∧ (∀ s p, ⌜entry_m⌝ₚ(s,p,⌜r⌝ₛ) ↔ s ∈ ⌜W⌝ₛ ∧ p ∈ ⌜B⌝ₛ ∧
    ⌜fn_name_m⌝ₚ(⌜B⌝ₛ,⌜R⌝ₛ,⌜B⌝ₛ,p,⌜t⌝ₛ,⌜t⌝ₛ,s))⟫
derive_free_closed rn_data_m

def rn_m {n} (B R b ω r : Term n) : Formula 1 n := set[n] ⟪∃ D t W,
  ⌜rn_data_m⌝ₚ(⌜B⌝ₛ,⌜R⌝ₛ,⌜b⌝ₛ,⌜ω⌝ₛ,D,t,W,⌜r⌝ₛ)⟫
derive_free_closed rn_m

theorem rn_data_sat_l (hE : Extensional M) {n} (ρ : Env M n) (B R b ω D t W r : Term n) :
    Formula.satisfies ρ (rn_data_m B R b ω D t W r) ↔
      Rn_data_d I (B.eval ρ) (R.eval ρ) (b.eval ρ) (ω.eval ρ) (D.eval ρ) (t.eval ρ) (W.eval ρ) (r.eval ρ) := by
  simp only [rn_data_m,Formula.satisfies_conj_iff,Formula.satisfies_isCartesianProduct_iff I,
    check_sat_l M hE,ck_pool_sat_l hE,name_sat_l M hE,Formula.satisfies_forall_iff,
    Formula.satisfies_iff_iff,entry_sat_l M hE,Formula.satisfies_mem_iff,fn_name_sat_l hE,Definitional.Term.eval_weaken]
  exact ⟨fun ⟨a,b,c,d,e⟩ => ⟨a,b,c,d,e⟩,fun h => ⟨h.product,h.check,h.pool,h.name,h.entries⟩⟩

theorem rn_sat_l (hE : Extensional M) {n} (ρ : Env M n) (B R b ω r : Term n) :
    Formula.satisfies ρ (rn_m B R b ω r) ↔ Rn_d I (B.eval ρ) (R.eval ρ) (b.eval ρ) (ω.eval ρ) (r.eval ρ) := by
  simp only [rn_m,Rn_d,Formula.satisfies_exists_iff,rn_data_sat_l I hE,Definitional.Term.eval_weaken]
  rfl

theorem Rn_d.unique_l (hZF : M.Models ZF) {B R b ω r s : M.Domain}
    (h : Rn_d I B R b ω r) (k : Rn_d I B R b ω s) : r = s := by
  obtain ⟨D,t,W,h⟩ := h
  obtain ⟨D',t',W',k⟩ := k
  have dEq := hZF.1.eq_of_same_members D D' (fun v => (h.product v).trans (k.product v).symm)
  subst D'
  have tEq := check_unique_l M hZF.1 (check_ind_l M hZF) b ω t t' h.check k.check
  subst t'
  have wEq := h.pool.unique_l hZF.1 k.pool
  subst W'
  have graph {r : M.Domain} (nr : Name_d M B r) : ∀ v, M.mem v r → ∃ a p, KPair_d M v a p := by
    intro v hv
    obtain ⟨a,p,pair,_⟩ := (name_unfold_l M (name_ops_l M hZF) B r).mp nr v hv
    exact ⟨a,p,pair⟩
  exact entry_ext_l M hZF.1 (graph h.name) (graph k.name) (fun a p => (h.entries a p).trans (k.entries a p).symm)

end YesMetaZFC.Model.Forcing.Internal

/-! ## 指定名字的实际函数值及完整背景图

名字本身保留在证书参数中。任意被接受的检查基准都能逐边读取同一商值，
需要纯存在式名字证书时再由已有真值定理导出。
-/
namespace YesMetaZFC.Model.Forcing.Internal
open SetTheory SetTheory.Definitional.Project SetTheory.InnerModel
universe u v
variable {N : Structure.{u}} {M : Structure.{v}}

def Fn_value_d (hN : N.Models ZF) (k : N.Domain → M.Domain) (B R z ω τ : N.Domain) (G : N.Domain → Prop) (x : M.Domain) : Prop :=
  let E := extension_l N hN B R z G
  ∃ j : N.Domain → E.Domain, ∃ y : E.Domain, Qval_d N B R z G τ y ∧
    (∀ a, Gval_d N B R z G a (j a)) ∧ Fn0_d (j ω) (j ω) y ∧ Fn_read_d k j y x

theorem Fn_value_d.code_l (hN : N.Models ZF) {k : N.Domain → M.Domain} {B R z ω τ : N.Domain} {G : N.Domain → Prop} {x : M.Domain}
    (O : Cond_order_d N B R z) (generic : Generic_d N B R z G) (h : Fn_value_d hN k B R z ω τ G x) :
    Fn_code_d k B R z ω ω G x := by
  obtain ⟨j,y,_,ground,fn,read⟩ := h
  exact fn_code_of_value_l hN O generic k j ground fn read

theorem Fn_value_d.entry_l (hN : N.Models ZF) {k : N.Domain → M.Domain} {B R z ω τ b : N.Domain} {G : N.Domain → Prop} {x : M.Domain}
    (O : Cond_order_d N B R z) (generic : Generic_d N B R z G) (ki : Function.Injective k)
    (h : Fn_value_d hN k B R z ω τ G x) (hb : G b) (a c : N.Domain) :
    Entry_d M (k a) (k c) x ↔ ∃ p, G p ∧ Nentry_d B R z b τ a c p := by
  obtain ⟨j,y,value,ground,_,read⟩ := h
  have checks a t (check : Check_d N b a t) : Qval_d N B R z G t (j a) := by
    obtain ⟨v,vt⟩ := name_value_l (R := R) (z := z) (U := G)
      (check_name_l N (check_range_l N hN) (generic.proper b hb).1 check)
    exact (ground a).unique_l O hN generic ⟨b,t,hb,check,vt⟩ ▸ vt
  exact (read.entry_l ki a c).trans (nentry_truth_l hN O generic hb value j checks a c).symm

end YesMetaZFC.Model.Forcing.Internal

/-! ## 保留全部原自然数的初等提升保持指定实数图

只覆盖目标 ω 中的自然数，无须地模型映射整体满射。检查名字的交换方块
运输原函数性及每条边；目标坐标先由函数界收回 ω，再回拉为原自然数。
-/
namespace YesMetaZFC.Model.Forcing.Internal
open SetTheory SetTheory.Definitional.Project SetTheory.InnerModel
universe u v w
variable {M : Structure.{u}} {N : Structure.{v}} {V : Structure.{w}}

theorem Fn_value_d.elementary_l (hM : M.Models ZF) (hN : N.Models ZF)
    (e : M.Domain → N.Domain) (elem : Pe_d e)
    {B R z ω τ : M.Domain}
    (cover : ∀ a, N.mem a (e ω) → ∃ b, M.mem b ω ∧ e b = a)
    (O : Cond_order_d M B R z)
    {G : M.Domain → Prop} {H : N.Domain → Prop}
    (g : Generic_d M B R z G) (h : Generic_d N (e B) (e R) (e z) H) (accepted : ∀ p, G p → H (e p))
    {k : M.Domain → V.Domain} {l : N.Domain → V.Domain} (fixed : ∀ a, M.mem a ω → l (e a) = k a)
    {x : V.Domain} (named : Fn_value_d hM k B R z ω τ G x) :
    Fn_value_d hN l (e B) (e R) (e z) (e ω) (e τ) H x := by
  let E := extension_l M hM B R z G
  let F := extension_l N hN (e B) (e R) (e z) H
  have O' := em_order_l hM.1 hN.1 e elem O
  have hE := preserves_zf_l O hM g
  have hF := preserves_zf_l O' hN h
  let f : E.Domain → F.Domain := em_lift_l hM.1 hN.1 e elem accepted
  have ef : Pe_d f := em_lift_elementary_l hM hN e elem accepted O g h
  obtain ⟨j,y,value,base,fy,read⟩ := named
  obtain ⟨b,hb⟩ := g.inhabited
  obtain ⟨j₀,checked,jf,ji⟩ := check_map_l O hM g hb
  have same : j₀ = j := funext fun a =>
    ((gval_check_map_l O hM g hb j₀ checked a (j₀ a)).mpr rfl).unique_l O hM g (base a)
  subst j₀
  obtain ⟨t,checks,tf,ti⟩ := check_map_l O' hN h (accepted b hb)
  have ground a := (gval_check_map_l O' hN h (accepted b hb) t checks a (t a)).mpr rfl
  have commute a : f (j a) = t (e a) := by
    obtain ⟨p,s,hp,cs,vs⟩ := base a
    exact (show Gval_d N (e B) (e R) (e z) H (e a) (f (j a)) from
      ⟨e p,e s,accepted p hp,(em_check_l hM.1 hN.1 e elem).mp cs,em_lift_value_l hM.1 hN.1 e elem accepted vs⟩).unique_l O' hN h (ground (e a))
  have real : Fn0_d (t (e ω)) (t (e ω)) (f y) := by
    let ρ : Env E 3 := ⟨fun i => [j ω,j ω,y].get i,fun _ => y⟩
    let φ := fn0_m (.bound 0 : Term 3) (.bound 1) (.bound 2)
    have moved := (fn0_sat_l hF.1 (image_env_l f ρ) (.bound 0) (.bound 1) (.bound 2)).mp
      ((ef φ (by simp -implicitDefEqProofs [φ]) ρ).mp ((fn0_sat_l hE.1 ρ (.bound 0) (.bound 1) (.bound 2)).mpr fy))
    change Fn0_d (f (j ω)) (f (j ω)) (f y) at moved
    simpa only [commute] using moved
  have edge a b : Entry_d E (j a) (j b) y ↔ Entry_d F (t (e a)) (t (e b)) (f y) := by
    simpa only [commute] using em_entry_l hE.1 hF.1 f ef (j a) (j b) y
  refine ⟨t,f y,em_lift_value_l hM.1 hN.1 e elem accepted value,ground,real,fun a b => ⟨?_,?_⟩⟩
  · intro ab
    obtain ⟨a₀,b₀,ea,eb,old⟩ := (read a b).mp ab
    have ha := (image_member_l j ji jf).mp (fy.bound_l old).1
    have hb := (image_member_l j ji jf).mp (fy.bound_l old).2
    exact ⟨e a₀,e b₀,(fixed a₀ ha).trans ea,(fixed b₀ hb).trans eb,(edge a₀ b₀).mp old⟩
  · rintro ⟨a₀,b₀,ea,eb,old⟩
    obtain ⟨a₁,ha,rfl⟩ := cover a₀ ((image_member_l t ti tf).mp (real.bound_l old).1)
    obtain ⟨b₁,hb,rfl⟩ := cover b₀ ((image_member_l t ti tf).mp (real.bound_l old).2)
    exact (read a b).mpr ⟨a₁,b₁,(fixed a₁ ha).symm.trans ea,(fixed b₁ hb).symm.trans eb,(edge a₁ b₁).mpr old⟩

end YesMetaZFC.Model.Forcing.Internal

/-! ## 同一原名字沿集合模型同构保持完整背景实数图

直接提升原名字商，而非重新选择实数名字。同构满射性给出全部自然数的原像，
统一初等提升定理据此保留原背景图的双向读取。
-/
namespace YesMetaZFC.Model.Forcing.Internal
open SetTheory SetTheory.Definitional.Project SetTheory.InnerModel
universe u v w
variable {M : Structure.{u}} {N : Structure.{v}} {V : Structure.{w}}

theorem Fn_value_d.iso_l (hM : M.Models ZF) (hN : N.Models ZF)
    (e : M.Domain → N.Domain) (onto : Function.Surjective e)
    (mem : ∀ a b, M.mem a b ↔ N.mem (e a) (e b))
    {B R z ω τ : M.Domain} (O : Cond_order_d M B R z)
    {G : M.Domain → Prop} {H : N.Domain → Prop}
    (g : Generic_d M B R z G) (h : Generic_d N (e B) (e R) (e z) H) (accepted : ∀ p, G p → H (e p))
    {k : M.Domain → V.Domain} {l : N.Domain → V.Domain} (fixed : ∀ a, l (e a) = k a)
    {x : V.Domain} (named : Fn_value_d hM k B R z ω τ G x) :
    Fn_value_d hN l (e B) (e R) (e z) (e ω) (e τ) H x := by
  have elem : Pe_d e := fun φ _ ρ => formula_image_l e onto mem φ ρ
  exact named.elementary_l hM hN e elem (fun a ha => by
    obtain ⟨b,rfl⟩ := onto a
    exact ⟨b,(mem b ω).mpr ha,rfl⟩) O g h accepted (fun a _ => fixed a)

end YesMetaZFC.Model.Forcing.Internal
