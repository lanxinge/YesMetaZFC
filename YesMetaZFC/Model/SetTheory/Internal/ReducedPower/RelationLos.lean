import YesMetaZFC.Model.SetTheory.Internal.ReducedPower.RelationSyntax
import YesMetaZFC.Model.SetTheory.Internal.RelationPointwiseWitness

/-! # 原始关系源的完整内部 Łoś

归纳遍历全部内部程序行。布尔步只对原模型集合码的实际坐标逆像使用超滤二择；
存在步使用源内收集得到的同一函数码及其实际代表图。整个源无需坍塌。
-/
namespace YesMetaZFC.SetTheory.Internal
open Definitional.Project InnerModel
universe u
variable {M : Structure.{u}} (hZF : M.Models ZF)
local notation "I" => kp_pair_l (ZF.modelsKP hZF)

theorem rc_los_l {ω c X R c' Y S q D t P U o G p C T E K F n b r}
    (hω : M.IsOmega ω) (hX : M.TransitiveSet X) (hm : Smem_d I c X R)
    (theory : Sc_theory_d I ω X R) (collection : Sc_collection_d I ω X R)
    (source : Smdl_d I c' Y S) (hq : Smap_d I ω c c' X Y q)
    (d μ e : (smdl_structure_l I (R := S) source.2.1).Domain)
    (small : Formula.satisfies (⟨Fin.cases μ (Fin.cases d (fun _ => e)), fun _ => d⟩ :
      Env (smdl_structure_l I (R := S) source.2.1) 3) (sc_index_m .newest (.bound 1) (.bound 2)))
    (ft : Fn0_d D Y t) (domain : ∀ s x, Rd_entry_d s x t → Rd_entry_d x d.val S)
    (hP : Rt_source_d I Y S D t P) (hU : FilterZF.Rel_ultra_d D P U)
    (hG : ∀ g, M.mem g G ↔ Fn0_d D Y g ∧
      ∃ B f : (smdl_structure_l I (R := S) source.2.1).Domain, Fn0_d d B f ∧
        ∀ s (x y : (smdl_structure_l I (R := S) source.2.1).Domain), Rd_entry_d s x.val t →
          (Rd_entry_d s y.val g ↔ Rd_entry_d x y f))
    (model : Rp_model_d I D Y U S o G p C T) (hE : M.IsFunctionSpace I E ω Y)
    (hK : M.IsFunctionSpace I K ω C) (hF : Sfm_d I ω n F)
    (hb : M.mem b ω) (hB : Sbound_d I F b) (hr : M.mem r n) :
    Rc_los_d I b d.val Y S E F n t U p C T K r := by
  have context := hq.pe_context_l hZF hω hX hm theory source d.property hE
  have ext := context.1
  have en := ext.native_l I source.2.1
  obtain ⟨V, hV⟩ := seval_exists_l I hZF Y S E F hF.2.1.1
  obtain ⟨J, hJ⟩ := seval_exists_l I hZF C T K F hF.2.1.1
  let ρ : Env M 13 := ⟨Fin.cases K (Fin.cases T (Fin.cases C (Fin.cases p (Fin.cases U (Fin.cases t
    (Fin.cases n (Fin.cases F (Fin.cases E (Fin.cases S (Fin.cases Y (Fin.cases d.val (fun _ => b)))))))))))), fun _ => b⟩
  let φ : UnarySchema 13 := {
    body := rc_los_m (𝒞 := kpair_convention_l) (.bound 13) (.bound 12) (.bound 11)
      (.bound 10) (.bound 9) (.bound 8) (.bound 7) (.bound 6) (.bound 5) (.bound 4) (.bound 3) (.bound 2) (.bound 1) .newest }
  have sat s : φ.denote ρ s ↔ Rc_los_d I b d.val Y S E F n t U p C T K s := rc_los_sat_l I hZF.1 ..
  suffices h : φ.denote ρ r from (sat r).mp h
  apply sfm_induction_l I hZF hF φ ρ ?_ hr
  intro r hr ih
  apply (sat r).mpr
  intro a v ha hv eval
  have repr := eval.repr_l I ((hE a).mp ha).1
  have bω := hω.transitive hZF b hb
  have trace s (hs : M.mem s n) : ∃ B A, M.mem B Y ∧
      (∀ x, M.mem x Y → (Rd_entry_d x B S ↔ Rd_entry_d x d.val S ∧ Pe_sat_d I b d.val Y S E F n s a x)) ∧
      M.mem A P ∧ ∀ w x, Rd_entry_d w x t → (M.mem w A ↔ Pe_sat_d I b d.val Y S E F n s a x) := by
    obtain ⟨B, hBY, truth⟩ := hq.pe_trace_raw_l hZF hω hX hm theory source d.property hE hF hs hb hB ha repr
    obtain ⟨A, tr⟩ := rt_trace_exists_l I hZF D t S B
    exact ⟨B, A, hBY, truth, hP.pointwise_l I (fn0_function_l (ZF.modelsKP hZF) ft) domain hBY tr truth⟩
  obtain ⟨z, hz⟩ := (hF.2.1.2.2 r).mp hr
  rcases hF.2.2 r z hz with ⟨i, j, hs, _, _⟩ | ⟨i, j, hs, _, _⟩ |
    ⟨i, j, hs, hi, hj⟩ | ⟨i, j, hs, hi, hj⟩
  · obtain ⟨fi, gi, B, hif, _, fgi, gip, hiB⟩ := eval i (hB.operands_l I hz hs).1
    obtain ⟨fj, gj, A, hjf, _, fgj, gjp, hjA⟩ := eval j (hB.operands_l I hz hs).2
    have fgi' := model.map.functions gi (model.map.projection.input_mem_of_pairMember gip)
    have fgj' := model.map.functions gj (model.map.projection.input_mem_of_pairMember gjp)
    have read s x y z (hsx : Rd_entry_d s x t) (hy : Rd_entry_d s y gi) (hz' : Rd_entry_d s z gj) :=
      pe_sat_atom_l I hZF ext hE hF hV hB bω ha repr (ft.bound_l hsx).2 (domain s x hsx) hz false hs hif hjf
        ((fgi s x y hsx).mp hy) ((fgj s x z hsx).mp hz')
    have atom : Rc_holds_d I b d.val Y S E F n r t U a ↔ Rp_rel_d I Y U S gi gj := by
      apply exists_congr
      intro W
      apply and_congr_right
      intro hW
      constructor
      · intro holds s hsW
        obtain ⟨x, _, hsx⟩ := ft.2.1 s (hU.base.bounds W hW s hsW)
        obtain ⟨y, hy, hsy⟩ := fgi'.2.1 s (hU.base.bounds W hW s hsW)
        obtain ⟨z, hz', hsz⟩ := fgj'.2.1 s (hU.base.bounds W hW s hsW)
        exact ⟨y, hy, z, hz', hsy, hsz, (read s x y z hsx hsy hsz).mp (holds s x hsW hsx)⟩
      · intro holds s x hsW hsx
        obtain ⟨y, _, z, _, hsy, hsz, hyz⟩ := holds s hsW
        exact (read s x y z hsx hsy hsz).mpr hyz
    exact atom.trans ((model.relation gi gj B A gip gjp).symm.trans (ssat_rel_l I hZF hF hJ hz hs hK hv hiB hjA).symm)
  · obtain ⟨fi, gi, B, hif, _, fgi, gip, hiB⟩ := eval i (hB.operands_l I hz hs).1
    obtain ⟨fj, gj, A, hjf, _, fgj, gjp, hjA⟩ := eval j (hB.operands_l I hz hs).2
    have fgi' := model.map.functions gi (model.map.projection.input_mem_of_pairMember gip)
    have fgj' := model.map.functions gj (model.map.projection.input_mem_of_pairMember gjp)
    have read s x y z (hsx : Rd_entry_d s x t) (hy : Rd_entry_d s y gi) (hz' : Rd_entry_d s z gj) :=
      pe_sat_atom_l I hZF ext hE hF hV hB bω ha repr (ft.bound_l hsx).2 (domain s x hsx) hz true hs hif hjf
        ((fgi s x y hsx).mp hy) ((fgj s x z hsx).mp hz')
    have atom : Rc_holds_d I b d.val Y S E F n r t U a ↔ Rp_eq_d Y U gi gj := by
      apply exists_congr
      intro W
      apply and_congr_right
      intro hW
      constructor
      · intro holds s hsW
        obtain ⟨x, _, hsx⟩ := ft.2.1 s (hU.base.bounds W hW s hsW)
        obtain ⟨y, hy, hsy⟩ := fgi'.2.1 s (hU.base.bounds W hW s hsW)
        obtain ⟨z, _, hsz⟩ := fgj'.2.1 s (hU.base.bounds W hW s hsW)
        exact ⟨y, hy, hsy, ((read s x y z hsx hsy hsz).mp (holds s x hsW hsx)).symm ▸ hsz⟩
      · intro holds s x hsW hsx
        obtain ⟨y, _, hsy, hsz⟩ := holds s hsW
        exact (read s x y y hsx hsy hsz).mpr rfl
    exact atom.trans ((rp_kernel_l I hZF.1 hU.base model.map gip gjp).symm.trans (ssat_eq_l I hZF hF hJ hz hs hK hv hiB hjA).symm)
  · have hin := hF.2.1.1.transitive r hr i hi
    have hjn := hF.2.1.1.transitive r hr j hj
    obtain ⟨_, A, _, _, hA, pa⟩ := trace i hin
    obtain ⟨_, B, _, _, hB', pb⟩ := trace j hjn
    obtain ⟨_, W, _, _, hW, pw⟩ := trace r hr
    have spec s : M.mem s W ↔ M.mem s D ∧ ¬ (M.mem s A ∨ M.mem s B) := by
      by_cases hsD : M.mem s D
      · obtain ⟨x, hx, hsx⟩ := ft.2.1 s hsD
        exact (pw s x hsx).trans ((pe_sat_nor_l I hZF ext hE hF hV hB bω ha repr hx (domain s x hsx) hz hs hin hjn).trans
          ((not_congr (or_congr (pa s x hsx).symm (pb s x hsx).symm)).trans (and_iff_right hsD).symm))
      · exact iff_of_false (fun h => hsD (hU.field.bounds W hW s h)) (fun h => hsD h.1)
    have bool := (rc_holds_member_l I hU hW ft pw).symm.trans ((hU.nor_l hA hB' hW spec).trans
      (not_congr (or_congr (rc_holds_member_l I hU hA ft pa) (rc_holds_member_l I hU hB' ft pb))))
    exact bool.trans ((not_congr (or_congr ((sat i).mp (ih i hi) a v ha hv eval)
      ((sat j).mp (ih j hj) a v ha hv eval))).trans (ssat_nor_l I hZF hF hJ hz hs hv).symm)
  · have hjn := hF.2.1.1.transitive r hr j hj
    rw [ssat_exists_l I hZF hF hJ hz hs hv]
    constructor
    · rintro ⟨W, hW, holds⟩
      obtain ⟨B, _, hBY, truth, _, _⟩ := trace r hr
      obtain ⟨f, Q, fn, a', update, witness⟩ := sc_pe_witness_raw_l hZF hω hX hm theory collection source hq
        d ⟨B, hBY⟩ μ e small hE hF hz hs hjn hb hB ha (fun x _ hx => ((truth x.val x.property).mp hx).2)
      obtain ⟨g, fg, decode⟩ := smdl_function_l hZF source ext d Q f fn ft domain
      have hg := (hG g).mpr ⟨fg, Q, f, fn, decode⟩
      obtain ⟨B', hBC, gp⟩ := model.map.projection.2.2 g hg
      obtain ⟨v', uv, hv'⟩ := senv_update_exists_l I hZF ((hK v).mp hv) hi hBC
      have ff := (rf_fun_native_l I source.2.1 en d f).mpr ⟨Q, fn⟩
      have gr := (rc_graph_native_l I source.2.1 en ft fg f).mpr decode
      refine ⟨B', v', hBC, uv, ((sat j).mp (ih j hj) a' v'
        ((hE a').mpr (update.function_l I ((hE a).mp ha) hi f.property)) ((hK v').mpr hv')
        (eval.update_l I ff gr gp update uv)).mp ⟨W, hW, ?_⟩⟩
      intro s x hsW hsx
      exact witness ⟨x, (ft.bound_l hsx).2⟩ (domain s x hsx)
        ((truth x (ft.bound_l hsx).2).mpr ⟨domain s x hsx, holds s x hsW hsx⟩)
    · rintro ⟨B, v', hBC, uv, truth⟩
      obtain ⟨g, gp⟩ := (model.map.range B).mp hBC
      obtain ⟨fg, Q, f, fn, decode⟩ := (hG g).mp (model.map.projection.input_mem_of_pairMember gp)
      have ff := (rf_fun_native_l I source.2.1 en d f).mpr ⟨Q, fn⟩
      have gr := (rc_graph_native_l I source.2.1 en ft fg f).mpr decode
      obtain ⟨a', update, ha'⟩ := senv_update_exists_l I hZF ((hE a).mp ha) hi f.property
      obtain ⟨W, hW, holds⟩ := ((sat j).mp (ih j hj) a' v' ((hE a').mpr ha')
        ((hK v').mpr (uv.function_l I ((hK v).mp hv) hi hBC)) (eval.update_l I ff gr gp update uv)).mpr truth
      exact ⟨W, hW, fun s x hsW hsx => pe_sat_ex_intro_l I hZF ext hE hF hV hB bω ha repr
        (ft.bound_l hsx).2 (domain s x hsx) hz hs hi hjn ff update (holds s x hsW hsx)⟩

/-- 同一代表赋值上全部内部公式码的统一满足关系。 -/
theorem rc_satisfies_l {ω c X R c' Y S q D t P U o G p C T E}
    (hω : M.IsOmega ω) (hX : M.TransitiveSet X) (hm : Smem_d I c X R)
    (theory : Sc_theory_d I ω X R) (collection : Sc_collection_d I ω X R)
    (source : Smdl_d I c' Y S) (hq : Smap_d I ω c c' X Y q)
    (d μ e : (smdl_structure_l I (R := S) source.2.1).Domain)
    (small : Formula.satisfies (⟨Fin.cases μ (Fin.cases d (fun _ => e)), fun _ => d⟩ :
      Env (smdl_structure_l I (R := S) source.2.1) 3) (sc_index_m .newest (.bound 1) (.bound 2)))
    (ft : Fn0_d D Y t) (domain : ∀ s x, Rd_entry_d s x t → Rd_entry_d x d.val S)
    (hP : Rt_source_d I Y S D t P) (hU : FilterZF.Rel_ultra_d D P U)
    (hG : ∀ g, M.mem g G ↔ Fn0_d D Y g ∧
      ∃ B f : (smdl_structure_l I (R := S) source.2.1).Domain, Fn0_d d B f ∧
        ∀ s (x y : (smdl_structure_l I (R := S) source.2.1).Domain), Rd_entry_d s x.val t →
          (Rd_entry_d s y.val g ↔ Rd_entry_d x y f))
    (model : Rp_model_d I D Y U S o G p C T) (hE : M.IsFunctionSpace I E ω Y)
    {Z a v z} (codes : Scode_d I ω Z) (ha : M.mem a E) (hv : M.IsSetFunctionFromTo I v ω C)
    (eval : Rc_eval_d I ω d.val Y S t p a v) (hz : M.mem z Z) :
    Satisfies_d I ω o z v ↔ ∃ A, M.mem A U ∧ ∀ s x, M.mem s A → Rd_entry_d s x t →
      ∃ f, M.mem f E ∧ Pe_assign_d I ω d.val Y S a f x ∧ Satisfies_d I ω c' z f := by
  obtain ⟨n, F, r, code⟩ := (codes z).mp hz
  obtain ⟨b, hb, bound⟩ := sbound_exists_l I hZF hω code.2.1
  obtain ⟨K, hK⟩ := ZF.exists_functionSpace hZF I ω C
  have ext := (hq.pe_context_l hZF hω hX hm theory source d.property hE).1
  have repr := eval.repr_l I ((hE a).mp ha).1
  have bω := hω.transitive hZF b hb
  have los := rc_los_l hZF hω hX hm theory collection source hq d μ e small ft domain hP hU hG model
    hE hK code.2.1 hb bound code.2.2 a v ha ((hK v).mpr hv) (fun i hi => eval i (bω i hi))
  apply (satisfies_decode_l I hZF.1 model.code code hK).trans (los.symm.trans ?_)
  apply exists_congr
  intro A
  apply and_congr_right
  intro _
  apply forall_congr'
  intro s
  apply forall_congr'
  intro x
  apply imp_congr_right
  intro _
  apply imp_congr_right
  intro hsx
  apply (pe_sat_full_l I hZF ext hE code.2.1 bound bω code.2.2 ha repr (ft.bound_l hsx).2 (domain s x hsx)).trans
  exact exists_congr fun f => and_congr_right fun _ => and_congr_right fun _ =>
    (satisfies_decode_l I hZF.1 source code hE).symm

end YesMetaZFC.SetTheory.Internal
