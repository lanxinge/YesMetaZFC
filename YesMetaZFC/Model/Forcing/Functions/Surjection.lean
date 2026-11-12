import YesMetaZFC.Model.Forcing.Functions.ValueIsomorphism
import YesMetaZFC.Model.Forcing.Check.Order

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

/-! ## 满射名字的旧输出见证

直接消去满射公式，再把输入名称见证拉回规范源集的真实旧元素。
因此每个旧目标值在任意加强条件下都有某个旧输入作为见证。
-/
namespace YesMetaZFC.Model.Forcing.Internal
open SetTheory SetTheory.Definitional.Project
universe u
variable {M : Structure.{u}} {B R z : M.Domain}

def onto_body_m : Formula 1 3 := Formula.isSurjectiveOnto kpair_convention_l .newest (.bound 1) (.bound 2)
theorem onto_body_closed_l : onto_body_m.FreeClosed := Formula.isSurjectiveOnto_freeClosed _ _ _ _ rfl rfl rfl

def Onto_name_d (B R z a T w f : M.Domain) : Prop := Fn_name_d M B R z a T w f ∧
  Forces_d M B R z onto_body_m (fn_env_l T w f) a

variable (O : Cond_order_d M B R z) (hZF : M.Models ZF)
include O hZF

theorem onto_old_dense_l {a b T w f D X x : M.Domain} (name : Onto_name_d B R z a T w f)
    (hb : M.mem b B) (ha : Below_d M B R z a b) (hT : Check_d M b D T) (hw : Check_d M b X w)
    (hx : M.mem x X) : Dense_d M B R z (fun p => ∃ i, M.mem i D ∧ Old_value_d M B R z b f p i x) a := by
  let ρ := fn_env_l T w f
  have names := fn_env_names_l name.1.1 name.1.2.1 name.1.2.2.1
  obtain ⟨v,hv,nv,_⟩ := zf_check_l M hZF hb x
  have pushed : ∀ t : Term 4, Name_d M B (t.eval (ρ.push v)) := by
    intro t; cases t with
    | free i => exact names (.free i)
    | bound i => exact Fin.cases nv (fun i => names (.bound i)) i
  intro p hp
  have forced := (forces_regular_l O hZF onto_body_m ρ names).1 a p ha.1 hp name.2
  let ψ : Formula 1 4 := .existsE (.conj (.mem .newest (.bound 3)) (entry_m .newest (.bound 1) (.bound 2)))
  have total : Forces_d M B R z (.imp (.mem .newest (.bound 3)) ψ) (ρ.push v) p :=
    (forces_all_l hZF.1 (.imp (.mem .newest (.bound 3)) ψ) ρ p).mp forced v nv
  have member := check_mem_force_l O hZF hb hv hw hp.1 (below_trans_l O hb hp ha).2.2 hx
  have existsInput : Forces_d M B R z ψ (ρ.push v) p := forces_mp_l hZF.1
    (forces_regular_l O hZF (.mem .newest (.bound 3)) (ρ.push v) pushed).1
    (forces_regular_l O hZF ψ (ρ.push v) pushed) hp.1 hp.2.1 total
      ((forces_mem_l hZF.1 .newest (.bound 3) (ρ.push v) p).mpr member)
  obtain ⟨q,hq,s,ns,hit⟩ := forces_exists_dense_l hZF.1 existsInput p (below_refl_l O hp.1 hp.2.1)
  obtain ⟨source,edge⟩ := (forces_conj_l _ _ _ q).mp hit
  have source : Mem_force_d M B R z q s T := (forces_mem_l hZF.1 .newest (.bound 3) ((ρ.push v).push s) q).mp source
  have edge : Rel_force_d M B R z f q s v :=
    (force_entry_l hZF.1 ((ρ.push v).push s) q .newest (.bound 1) (.bound 2)).mp edge
  obtain ⟨r,t,c,hr,tc,_,st⟩ := source.2 q (below_refl_l O hq.1 hq.2.1)
  obtain ⟨_,i,hi,check⟩ := (check_entry_l M hZF.1 (check_ind_l M hZF)
    (KP.exists_pair (ZF.modelsKP hZF)) hT t c).mp tc
  have nt := check_name_l M (check_range_l M hZF) hb check
  have edge := (rel_force_regular_l O hZF name.1.2.2.1 ns nv).1 q r hq.1 hr edge
  let η : Env M 2 := ⟨Fin.cases v (fun _ => f),fun _ => f⟩
  let φ : UnarySchema 2 := { body := entry_m .newest (.bound 1) (.bound 2) }
  have encoded : Forces_d M B R z φ.body (η.push s) r :=
    (force_entry_l hZF.1 (η.push s) r .newest (.bound 1) (.bound 2)).mpr edge
  have replaced := (forces_name_congr_l O hZF φ η (Fin.cases nv (fun _ => name.1.2.2.1))
    ns nt hr.1 hr.2.1 st).mp encoded
  exact ⟨r,below_trans_l O hp.1 hr hq,i,hi,t,check,v,hv,
    (force_entry_l hZF.1 (η.push t) r .newest (.bound 1) (.bound 2)).mp replaced⟩

/-- 每个真实满射名字值给出原泛型中的满射力迫证书。 -/
theorem onto_name_of_value_l {b T w f : M.Domain} {G : M.Domain → Prop}
    (generic : Generic_d M B R z G) (hb : G b)
    {D X F : (extension_l M hZF B R z G).Domain}
    (vt : Qval_d M B R z G T D) (vw : Qval_d M B R z G w X) (vf : Qval_d M B R z G f F)
    (fn : (extension_l M hZF B R z G).IsSetFunctionFromTo
      (kpair_interpretation_l _ (extension_ext_l O hZF generic) (internal_pair_l O hZF generic)) F D X)
    (onto : (extension_l M hZF B R z G).IsSetSurjectiveOnto
      (kpair_interpretation_l _ (extension_ext_l O hZF generic) (internal_pair_l O hZF generic)) F D X) :
    ∃ a, G a ∧ Below_d M B R z a b ∧ Onto_name_d B R z a T w f := by
  let ρ := fn_env_l T w f
  let η := fn_env_l (M := extension_l M hZF B R z G) D X F
  have values : Env_val_d hZF ρ η := by
    intro t; cases t with
    | free _ => exact vw
    | bound i => exact Fin.cases vf (Fin.cases vt (fun _ => vw)) i
  have closed : (Definitional.Formula.conj fn_body_m onto_body_m).FreeClosed := ⟨fn_body_closed_l,onto_body_closed_l⟩
  have truth : Formula.satisfies η (.conj fn_body_m onto_body_m) :=
    (Formula.satisfies_conj_iff η _ _).mpr
      ⟨(Formula.satisfies_isFunctionFromTo_iff _ (extension_ext_l O hZF generic) η _ _ _).mpr fn,
       (Formula.satisfies_isSurjectiveOnto_iff _ η _ _ _).mpr onto⟩
  obtain ⟨p,hp,force⟩ := (forcing_truth_l O hZF generic _ closed ρ η values).mpr truth
  obtain ⟨a,ha,ap,ab⟩ := generic.directed p b hp hb
  have pos := generic.proper a ha
  have force := (formula_eval_l O hZF generic _ closed ρ η values).1.1 p a (generic.proper p hp).1 ⟨pos.1,pos.2,ap⟩ force
  obtain ⟨func,surj⟩ := (forces_conj_l _ _ _ a).mp force
  exact ⟨a,ha,⟨pos.1,pos.2,ab⟩,⟨qval_name_l vt,qval_name_l vw,qval_name_l vf,func⟩,surj⟩

end YesMetaZFC.Model.Forcing.Internal
