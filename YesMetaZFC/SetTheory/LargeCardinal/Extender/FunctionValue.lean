import YesMetaZFC.SetTheory.LargeCardinal.Extender.Ultrapower
import YesMetaZFC.Model.SetTheory.Relations.Constant
import YesMetaZFC.SetTheory.LargeCardinal.Extender.Value
import YesMetaZFC.Model.SetTheory.Source.Relation
import YesMetaZFC.Model.SetTheory.Relations.CollectCode

/-! # 原始商中任意有限组对象的共同支撑代表

逐个合并实际支撑，再把全部旧代表拉回同一分量。代表只从源中取得，
有限组装不用全局选择；随后函数求值可以直接接受商对象而不索要代表参数。
-/
namespace YesMetaZFC.SetTheory.LargeCardinal
open Definitional.Project InnerModel Internal
universe u
variable {M : Structure.{u}} (hZF : M.Models ZF)
local notation "I" => kp_pair_l (ZF.modelsKP hZF)

theorem ep_finite_representatives_l {ω κ K L X R F J O Z A p T S q C W : M.Domain}
    (source : Ep_source_d (kp_pair_l (ZF.modelsKP hZF)) ω κ K X R) (family : Em_source_d ω κ L X F)
    (system : Ep_system_d I ω κ L X R F J O Z A p T S) (limit : Di_limit_d A p T S q C W)
    {k : Nat} (v : Fin k → M.Domain) (members : ∀ i, M.mem (v i) C) :
    ∃ n a D, M.mem n ω ∧ M.mem a J ∧ Fn0_d n L a ∧ Ep_space_d κ n D ∧
      ∃ f : Fin k → M.Domain, ∀ i, M.mem (f i) X ∧ Fn0_d D X (f i) ∧ Ep_repr_d q a (f i) (v i) := by
  have collect : ∀ k (P : Fin k → M.Domain → Prop), (∀ i, ∃ x, P i x) → ∃ f : Fin k → M.Domain, ∀ i, P i (f i) := by
    intro k
    induction k with
    | zero => exact fun _ _ => ⟨Fin.elim0, fun i => Fin.elim0 i⟩
    | succ k ih =>
      intro P total
      obtain ⟨x, hx⟩ := total 0
      obtain ⟨f, hf⟩ := ih (fun i => P i.succ) (fun i => total i.succ)
      exact ⟨Fin.cases x f, Fin.cases hx hf⟩
  induction k with
  | zero =>
    obtain ⟨z, hz, hzw⟩ := source.omega.1.1
    have empty : Fn0_d z L z := ⟨fun p hp => (hz p hp).elim, fun i hi => (hz i hi).elim, fun i hi => (hz i hi).elim⟩
    obtain ⟨D, _, space⟩ := source.space_l hZF hzw
    exact ⟨z, z, D, hzw, (system.indices z).mpr ⟨z, hzw, empty, fun i j x hi _ =>
      (hz i (empty.bound_l hi).1).elim⟩, empty, space, Fin.elim0, fun i => Fin.elim0 i⟩
  | succ k ih =>
    obtain ⟨n, a, D, f, hn, haJ, ha, space, hf, ff, value⟩ := ep_repr_surjective_l hZF family system limit (members 0)
    obtain ⟨m, b, E, hm, hbJ, hb, space', g, gs⟩ := ih (fun i => v i.succ) (fun i => members i.succ)
    obtain ⟨c, hcJ, hac, hbc⟩ := system.order.directed a b haJ hbJ
    obtain ⟨l, hl, hc, _⟩ := (system.indices c).mp hcJ
    obtain ⟨Q, _, sq⟩ := source.space_l hZF hl
    have move {n a D f H} (hn : M.mem n ω) (ha : Fn0_d n L a) (space : Ep_space_d κ n D)
        (hf : M.mem f X) (ff : Fn0_d D X f) (value : Ep_repr_d q a f H) (edge : Rd_entry_d a c O) :
        ∃ g, M.mem g X ∧ Fn0_d Q X g ∧ Ep_repr_d q c g H := by
      obtain ⟨_, _, r, n', l', _, _, fr, hc', comp⟩ := (system.order_spec a c).mp edge
      have en := comp.1.domain_eq_l hZF.1 ha
      have el := hc'.domain_eq_l hZF.1 hc
      subst n' l'
      obtain ⟨g, hg, fg, _, gv⟩ := ep_repr_reindex_l hZF source family system limit hn hl fr hcJ hc comp space sq hf ff value
      exact ⟨g, hg, fg, gv⟩
    obtain ⟨f', hf'⟩ := move hn ha space hf ff value hac
    obtain ⟨g', hg'⟩ := collect k (fun i g => M.mem g X ∧ Fn0_d Q X g ∧ Ep_repr_d q c g (v i.succ))
      (fun i => move hm hb space' (gs i).1 (gs i).2.1 (gs i).2.2 hbc)
    exact ⟨l, c, Q, hl, hcJ, hc, sq, Fin.cases f' g', Fin.cases hf' hg'⟩

end YesMetaZFC.SetTheory.LargeCardinal

/-! ## 未坍塌商中函数求值的源内代表

先由完整关系 Łoś 取得函数性和定义域成员关系的同一个好集合，再在源中
逐点求值。新代表进入原来的商及原来的关系实现，不使用目标坍塌或可数闭性。
-/
namespace YesMetaZFC.SetTheory.LargeCardinal
open Definitional.Project InnerModel Internal
universe u
variable {M : Structure.{u}} (hZFC : M.Models ZFC)
local notation "hZF" => ZFC.models_zf_l hZFC
local notation "I" => kp_pair_l (ZF.modelsKP hZF)

theorem ep_function_value_l {ω κ K L X R F J O Z A p T V q c C W d N S e n D a U : M.Domain}
    (source : Ep_source_d (kp_pair_l (ZF.modelsKP hZF)) ω κ K X R) (family : Em_source_d ω κ L X F)
    (coherent : Ec_source_d I ω κ L X F)
    (system : Ep_system_d I ω κ L X R F J O Z A p T V) (limit : Di_limit_d A p T V q C W)
    (model : Smdl_d I c C W) (target : Smdl_d I d N S) (he : Smap_d I ω c d C N e)
    (haJ : M.mem a J) (ha : Fn0_d n L a) (space : Ep_space_d κ n D) (haU : Rd_entry_d a U F)
    (v : Fin 4 → M.Domain) (ρ : Env (smdl_structure_l I (R := S) target.2.1) 4)
    (values : ∀ i, Ep_value_d q e a (v i) (ρ.bound i).val)
    (function : Formula.satisfies ρ (fn0_m (.bound 2) (.bound 3) (.bound 0)))
    (argument : Formula.satisfies ρ (.mem (.bound 1) (.bound 2))) :
    ∃ g y, ∃ hy : M.mem y N, M.mem g X ∧ Fn0_d D X g ∧ Ep_value_d q e a g y ∧
      Formula.satisfies (ρ.push ⟨y, hy⟩) (rd_entry0_m (.bound 2) .newest (.bound 1)) := by
  have functions i : M.mem (v i) X ∧ Fn0_d D X (v i) := by
    obtain ⟨E, rep, _⟩ := values i
    obtain ⟨hf, m, _, ha', D', sp, ff⟩ := rep.source_l hZF family system limit
    have en := ha'.domain_eq_l hZF.1 ha
    subst m
    have eq := hZF.1.eq_of_same_members D' D (fun s => (sp s).trans (space s).symm)
    exact ⟨hf, eq ▸ ff⟩
  have hn : M.mem n ω := by
    obtain ⟨E, rep, _⟩ := values 0
    obtain ⟨_, m, hm, ha', _⟩ := rep.source_l hZF family system limit
    exact ha'.domain_eq_l hZF.1 ha ▸ hm
  let φ : Formula 1 4 := .conj (fn0_m (.bound 2) (.bound 3) (.bound 0)) (.mem (.bound 1) (.bound 2))
  have closed : φ.FreeClosed := by simp -implicitDefEqProofs [φ, Definitional.Formula.FreeClosed]
  have delta : φ.IsDelta0 := .conj (fn0_delta_l ..) (.mem _ _)
  obtain ⟨B, hB, hBU, sub, good⟩ := (ep_formula_value_l hZFC source family coherent system limit model
    target he haJ ha space haU φ closed v ρ values).mp ((Formula.satisfies_conj_iff ..).mpr ⟨function, argument⟩)
  obtain ⟨b, code⟩ := source.code
  obtain ⟨g, hg, fg, ev⟩ := sc_apply_on_l hZF source.omega source.transitive code source.theory
    (source.space_mem_l hZF hn space)
    hB (functions 0).1 (functions 0).2 (functions 1).1 (functions 1).2 (fun s hs => by
      obtain ⟨t, ht, hst⟩ := (functions 0).2.2.1 s (sub s hs)
      obtain ⟨z, hz, hsz⟩ := (functions 1).2.2.1 s (sub s hs)
      obtain ⟨D₀, hD₀, hsd⟩ := (functions 2).2.2.1 s (sub s hs)
      obtain ⟨B₀, hB₀, hsb⟩ := (functions 3).2.2.1 s (sub s hs)
      let η : Env (rt_model_l X ⟨⟨ω, source.omega_mem⟩⟩) 4 :=
        ⟨fun i => [⟨t, ht⟩, ⟨z, hz⟩, ⟨D₀, hD₀⟩, ⟨B₀, hB₀⟩].get i, fun _ => ⟨ω, source.omega_mem⟩⟩
      have entries : ∀ i, Rd_entry_d s (η.bound i).val (v i) :=
        Fin.cases hst (Fin.cases hsz (Fin.cases hsd (Fin.cases hsb (fun i => Fin.elim0 i))))
      have point : Formula.satisfies (⟨fun i => (η.bound i).val, fun i => (η.free i).val⟩ : Env M 4) φ :=
        (rt_model_delta_l source.transitive _ delta η).mp (good s hs η entries)
      simp only [φ, Formula.satisfies_conj_iff, fn0_sat_l hZF.1, Formula.satisfies_mem_iff] at point
      change Fn0_d D₀ B₀ t ∧ M.mem z D₀ at point
      obtain ⟨y, _, hzy⟩ := point.1.2.1 z point.2
      exact ⟨t, z, y, hst, hsz, hzy⟩)
  obtain ⟨H, hH, rep⟩ := ep_repr_exists_l hZF family system limit haJ ha space hg fg
  obtain ⟨y, hy, hHy⟩ := he.1.1.2.2 H hH
  have value : Ep_value_d q e a g y := ⟨H, rep, hHy⟩
  refine ⟨g, y, hy, hg, fg, value, ?_⟩
  apply (ep_formula_value_l hZFC source family coherent system limit model target he haJ ha space haU
    (rd_entry0_m (.bound 2) .newest (.bound 1)) (by simp -implicitDefEqProofs)
    (Fin.cases g v) (ρ.push ⟨y, hy⟩) (Fin.cases value values)).mpr
  refine ⟨B, hB, hBU, sub, fun s hs η entries => ?_⟩
  apply (rt_model_delta_l source.transitive _ (rd_entry0_delta_l ..) η).mpr
  apply (rd_entry0_sat_l hZF.1 ..).mpr
  exact ev s (η.bound 1).val (η.bound 2).val (η.bound 0).val hs (entries 1) (entries 2) (entries 0)

/-- 直接输入原始商中的函数和自变量；共同支撑及源内求值代表均由构造取得。 -/
theorem ep_function_raw_l {ω κ K L X R F J O Z A p T V q c C W : M.Domain}
    (source : Ep_source_d (kp_pair_l (ZF.modelsKP hZF)) ω κ K X R) (family : Em_source_d ω κ L X F)
    (coherent : Ec_source_d I ω κ L X F)
    (system : Ep_system_d I ω κ L X R F J O Z A p T V) (limit : Di_limit_d A p T V q C W)
    (model : Smdl_d I c C W) (ρ : Env (smdl_structure_l I (R := W) model.2.1) 4)
    (function : Formula.satisfies ρ (fn0_m (.bound 2) (.bound 3) (.bound 0)))
    (argument : Formula.satisfies ρ (.mem (.bound 1) (.bound 2))) :
    ∃ n a D g y, ∃ hy : M.mem y C,
      M.mem n ω ∧ M.mem a J ∧ Fn0_d n L a ∧ Ep_space_d κ n D ∧
      M.mem g X ∧ Fn0_d D X g ∧ Ep_repr_d q a g y ∧
      Formula.satisfies (ρ.push ⟨y, hy⟩) (rd_entry0_m (.bound 2) .newest (.bound 1)) := by
  obtain ⟨n, a, D, hn, haJ, ha, space, f, reps⟩ :=
    ep_finite_representatives_l hZF source family system limit (fun i => (ρ.bound i).val) (fun i => (ρ.bound i).property)
  obtain ⟨e, he, es⟩ := smap_identity_l I hZF (X := C) (c := c) source.omega
  obtain ⟨U, haU⟩ := family.total n a hn ha
  have values i : Ep_value_d q e a (f i) (ρ.bound i).val :=
    ⟨(ρ.bound i).val, (reps i).2.2, (es _ _).mpr ⟨(ρ.bound i).property, rfl⟩⟩
  obtain ⟨g, y, hy, hg, fg, value, eval⟩ := ep_function_value_l hZFC source family coherent system limit
    model model he haJ ha space haU f ρ values function argument
  obtain ⟨H, rep, hHy⟩ := value
  exact ⟨n, a, D, g, y, hy, hn, haJ, ha, space, hg, fg, ((es H y).mp hHy).2 ▸ rep, eval⟩

/-- 原始商对自己的每个定义域、每个常值都有内部函数，参数不必在旧常值图的像中。 -/
theorem ep_constant_function_raw_l {ω κ K L X R F J O Z A p T V q c C W : M.Domain}
    (source : Ep_source_d (kp_pair_l (ZF.modelsKP hZF)) ω κ K X R) (family : Em_source_d ω κ L X F)
    (coherent : Ec_source_d I ω κ L X F)
    (system : Ep_system_d I ω κ L X R F J O Z A p T V) (limit : Di_limit_d A p T V q C W)
    (model : Smdl_d I c C W) (d x : (smdl_structure_l I (R := W) model.2.1).Domain) :
    ∃ B f : (smdl_structure_l I (R := W) model.2.1).Domain,
      Fn0_d d B f ∧ ∀ s, Rd_entry_d s.val d.val W → Rd_entry_d s x f := by
  obtain ⟨b, i, mx, hi, _, ext⟩ := ep_constant_l hZF source family system limit model
    (system.toEp_graph_d.elementary_l hZF source family coherent)
  let ρ : Env (smdl_structure_l I (R := W) model.2.1) 0 := ⟨Fin.elim0, fun _ => d⟩
  exact sc_constant_raw_l (smdl_extensional_l hZF model ext) ρ
    ((source.theory.map_l I hZF source.omega mx.1 model hi).algebra model.2.1 ρ) d x

end YesMetaZFC.SetTheory.LargeCardinal
