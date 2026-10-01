import YesMetaZFC.Model.Forcing.TwoStep.Order
import YesMetaZFC.Model.Forcing.Internal.Maximum.Bounded

/-! # 首坐标不变的二步见证

已给定第二坐标名称时，ZF 的等值代表定理把它放回实际二步条件域；任意有界
存在式则由 ZFC 的库内最大值原理选择。两种构造均精确保留指定首坐标。
-/

namespace YesMetaZFC.Model.Forcing.Internal
open SetTheory SetTheory.Definitional.Project
universe u
variable {M : SetTheory.Structure.{u}} {B R z b A T t W C S : M.Domain}

/-- 将任意被迫属于第二条件集的名称装入二步序，保留给定第一条件。 -/
theorem two_step_represent_l (O : Cond_order_d M B R z) (hZF : M.Models ZF)
    (h : Two_step_d M B R z b A T W C S) (hW : Name_pool_d M B A t W) {p v}
    (hv : Name_d M B v) (hp : Below_d M B R z p b) (hm : Mem_force_d M B R z p v A) :
    ∃ s x, M.mem s W ∧ KPair_d M x p s ∧ M.mem x C ∧ Eq_force_d M B R z p s v := by
  obtain ⟨s, hs, he⟩ := name_pool_represent_l O hZF hW hv
  have hsN : Name_d M B s := ⟨W, hs, h.closed⟩
  have hsm := mem_force_left_l O hZF hv hsN ⟨W, h.root, h.closed⟩
    (eq_force_symm_l hZF hsN hv (he p hm)) hm
  obtain ⟨x, hx⟩ := (kpair_interpretation_l M hZF.1 (KP.exists_pair (ZF.modelsKP hZF))).total p s
  exact ⟨s, x, hs, hx, (two_step_mem_l h hx).mpr ⟨hs, hp, hsm⟩, he p hm⟩

/-- 有界存在式直接产生实际二步条件及正文力迫，第一条件不作加强。 -/
theorem two_step_witness_l (O : Cond_order_d M B R z) (hZFC : M.Models ZFC) {n}
    (φ : UnarySchema n) (ρ : Env M n) (i : Fin n) (hρ : ∀ j, Name_d M B (ρ.bound j))
    (h : Two_step_d M B R z b (ρ.bound i) T W C S) (hW : Name_pool_d M B (ρ.bound i) t W)
    {p} (hp : Below_d M B R z p b)
    (hex : Forces_d M B R z (.existsE (.conj (.mem .newest (Term.bound i).weaken) φ.body)) ρ p) :
    ∃ s x, M.mem s W ∧ KPair_d M x p s ∧ M.mem x C ∧ Forces_d M B R z φ.body (ρ.push s) p := by
  obtain ⟨s, hs, hMax⟩ := name_pool_maximum_l O hZFC φ ρ i hρ hW
  obtain ⟨hm, hφ⟩ := (hMax p hp.1 hp.2.1).mp hex
  obtain ⟨x, hx⟩ := (kpair_interpretation_l M hZFC.1
    (KP.exists_pair (ZF.modelsKP (ZFC.models_zf_l hZFC)))).total p s
  exact ⟨s, x, hs, hx, (two_step_mem_l h hx).mpr ⟨hs, hp, hm⟩, hφ⟩

/-- 指定更强第二坐标名称时，ZF 已能装配低于旧二步条件且首坐标精确为 p 的条件。 -/
theorem two_step_lower_name_l (O : Cond_order_d M B R z) (hZF : M.Models ZF)
    (h : Two_step_d M B R z b A T W C S) (hW : Name_pool_d M B A t W)
    (hT : Name_d M B T) {x q s p v} (hx : M.mem x C) (hxq : KPair_d M x q s)
    (hp : Below_d M B R z p q) (hv : Name_d M B v)
    (hm : Mem_force_d M B R z p v A) (hr : Rel_force_d M B R z T p v s) :
    ∃ a y, M.mem a W ∧ KPair_d M y p a ∧ M.mem y C ∧ Entry_d M y x S ∧ Eq_force_d M B R z p a v := by
  obtain ⟨hs, hq, _⟩ := (two_step_mem_l h hxq).mp hx
  have hsN : Name_d M B s := ⟨W, hs, h.closed⟩
  obtain ⟨a, y, ha, hyp, hy, he⟩ := two_step_represent_l O hZF h hW hv
    (below_trans_l O h.base hp hq) hm
  have haN : Name_d M B a := ⟨W, ha, h.closed⟩
  let ρ := ord_env_l M s T
  let φ : UnarySchema 2 := { body := rel_at_m .newest (.bound 1) (.bound 2) }
  have hρ : ∀ i, Name_d M B (ρ.bound i) := Fin.cases hsN (fun _ => hT)
  have hφ := (forces_name_congr_l O hZF φ ρ hρ hv haN hp.1 hp.2.1
    (eq_force_symm_l hZF haN hv he)).mp
      ((force_rel_at_l M hZF.1 (ρ.push v) p .newest (.bound 1) (.bound 2)).mpr hr)
  have hr' := (force_rel_at_l M hZF.1 (ρ.push a) p .newest (.bound 1) (.bound 2)).mp hφ
  exact ⟨a, y, ha, hyp, hy, (two_step_le_l h hy hx hyp hxq).mpr ⟨hp, hr'⟩, he⟩

end YesMetaZFC.Model.Forcing.Internal
