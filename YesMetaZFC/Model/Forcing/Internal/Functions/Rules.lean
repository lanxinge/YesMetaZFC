import YesMetaZFC.Model.Forcing.Internal.Functions.Injection
import YesMetaZFC.Model.Forcing.Internal.Maximum.Basic
import YesMetaZFC.Model.Forcing.Internal.Check.Forcing

/-! # 被迫函数、单射与传递容器的局部规则

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
      Formula.pairArguments, Fin.cases, Fin.induction, Fin.induction.go]
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

set_option maxHeartbeats 600000 in
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
  have hcW := (forces_mem_l hZF.1 _ _ _ q).mp hcm
  obtain ⟨r, a, d, hrq, had, hrd, hca⟩ := hcW.2 q (below_refl_l O hqp.1 hqp.2.1)
  obtain ⟨_, i, hi, hia⟩ := (check_entry_l M hZF.1 (check_ind_l M hZF)
    (KP.exists_pair (ZF.modelsKP hZF)) hw a d).mp had
  have ha := check_name_l M (check_range_l M hZF) hc hia
  have hfc' : Rel_force_d M B R z f q s v := (force_entry_l hZF.1 _ q _ _ _).mp hfc
  have hfr := (rel_force_regular_l O hZF h.2.2.1 hs hv).1 q r hqp.1 hrq hfc'
  let φ : UnarySchema 2 := { body := entry_m (.bound 1) .newest (.bound 2) }
  have hfa : Rel_force_d M B R z f r s a := (forces_name_congr_l O hZF φ (ord_env_l M s f)
    (Fin.cases hs (fun _ => h.2.2.1)) hv ha hrq.1 hrq.2.1 hca).mp hfr
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
