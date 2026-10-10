import YesMetaZFC.Model.Forcing.Internal.Functions.Rules
import YesMetaZFC.Model.Forcing.Internal.Check.Relation

/-! # 函数名称的旧值判定

输入和输出都用同一基点的规范名称表示。函数性与规范名称的忠实性给出
旧输出的唯一性；此判定由原集合论公式定义，可直接用于内部替换。
-/

namespace YesMetaZFC.Model.Forcing.Internal
open SetTheory SetTheory.Definitional.Project
universe u
variable {M : SetTheory.Structure.{u}} {B R z : M.Domain}

def Old_value_d (M : SetTheory.Structure.{u}) (B R z b f p i x : M.Domain) : Prop :=
  ∃ s, Check_d M b i s ∧ Nvalue_d M B R z b f p s x

def old_value_m {n} (B R z b f p i x : Term n) : Formula 1 n :=
  .existsE (.conj (check_m b.weaken i.weaken .newest)
    (nvalue_m B.weaken R.weaken z.weaken b.weaken f.weaken p.weaken .newest x.weaken))
derive_free_closed old_value_m

theorem old_value_sat_l (hE : Extensional M) {n} (ρ : Env M n) (B R z b f p i x : Term n) :
    Formula.satisfies ρ (old_value_m B R z b f p i x) ↔
      Old_value_d M (B.eval ρ) (R.eval ρ) (z.eval ρ) (b.eval ρ) (f.eval ρ) (p.eval ρ) (i.eval ρ) (x.eval ρ) := by
  simp only [old_value_m, Old_value_d, Formula.satisfies_exists_iff, Formula.satisfies_conj_iff,
    check_sat_l M hE, nvalue_sat_l hE, Definitional.Term.eval_weaken, Definitional.Term.eval_newest]

variable (O : Cond_order_d M B R z) (hZF : M.Models ZF)
include O hZF

theorem old_value_lower_l {b f i x} (hb : M.mem b B) (hf : Name_d M B f) :
    Lower_d M B R z (fun p => Old_value_d M B R z b f p i x) := by
  rintro p q hp hq ⟨s, hs, t, ht, h⟩
  exact ⟨s, hs, t, ht, (rel_force_regular_l O hZF hf
    (check_name_l M (check_range_l M hZF) hb hs)
    (check_name_l M (check_range_l M hZF) hb ht)).1 p q hp hq h⟩

/-- 正条件下函数的同一旧输入，不能判为两个不同旧输出。 -/
theorem old_value_unique_l {a b T w f p i x y} (h : Fn_name_d M B R z a T w f)
    (ha : M.mem a B) (hb : M.mem b B) (hpa : Below_d M B R z p a) (hpb : Below_d M B R z p b)
    (hx : Old_value_d M B R z b f p i x) (hy : Old_value_d M B R z b f p i y) : x = y := by
  obtain ⟨s, hs, t, ht, hst⟩ := hx
  obtain ⟨s', hs', v, hv, hsv⟩ := hy
  have he := check_unique_l M hZF.1 (check_ind_l M hZF) b i s' s hs' hs
  subst s'
  exact check_force_reflect_l O hZF hb ht hv hpb (fn_name_eq_l O hZF h ha hpa
    (check_name_l M (check_range_l M hZF) hb hs)
    (check_name_l M (check_range_l M hZF) hb ht)
    (check_name_l M (check_range_l M hZF) hb hv) hst hsv)

/-- 取值于旧集合的函数名称，在每个旧输入处都能加强到决定旧输出。 -/
theorem old_value_dense_l {a b T w f D X i} (h : Fn_name_d M B R z a T w f)
    (hb : M.mem b B) (ha : Below_d M B R z a b) (hT : Check_d M b D T)
    (hw : Check_d M b X w) (hi : M.mem i D) :
    Dense_d M B R z (fun p => ∃ x, M.mem x X ∧ Old_value_d M B R z b f p i x) a := by
  intro p hp
  obtain ⟨s, hs, hsN, _⟩ := zf_check_l M hZF hb i
  have hpb := below_trans_l O hb hp ha
  have hsT := check_mem_force_l O hZF hb hs hT hp.1 hpb.2.2 hi
  obtain ⟨q, x, hq, hx, hv⟩ := fn_name_index_l O hZF h ha.1 hb hw hp hsN hsT
  exact ⟨q, hq, x, hx, s, hs, hv⟩

end YesMetaZFC.Model.Forcing.Internal
