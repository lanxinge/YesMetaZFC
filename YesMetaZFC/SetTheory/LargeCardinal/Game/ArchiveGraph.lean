import YesMetaZFC.SetTheory.LargeCardinal.Game.IterationStep
import YesMetaZFC.SetTheory.LargeCardinal.Iteration.CopyAnchor
import YesMetaZFC.Model.SetTheory.Reflection.ZfcTransfer
import YesMetaZFC.SetTheory.LargeCardinal.Game.ArchivePlayNative

/-! # 当前低层对象沿实际共同图回到原档案

旧回答域的真实 γ 下界使整个原基底属于共同秩段。两侧完整低层解释沿共同图
交换，当前根图和共同图的函数性于是把同一背景字母识别回保存时的原对象码。
-/
namespace YesMetaZFC.SetTheory.LargeCardinal
open Definitional.Project InnerModel Internal
universe u
variable {M : Structure.{u}} (hZF : M.Models ZF)
local notation "I" => kp_pair_l (ZF.modelsKP hZF)

/-- 给定真实共同图的每一条边，都与两侧根图在低层上交换。 -/
theorem Tg_iteration_d.archive_low_l
    {ω c₀ o C₀ S₀ γ Bγ A X₀ R₀ m r l φ V Γ j : M.Domain}
    {v : Fin 29 → M.Domain} {a : Fin 46 → M.Domain}
    (state : Tg_iteration_d hZF ω c₀ o C₀ S₀ γ Bγ A v a)
    (root : Zc_model_d I ω c₀ X₀ R₀) (row : Tg_archive_row_d M.Domain)
    (entry : Rd_entry_d m r (v 13)) (tuple : Rt_tuple_d row.values_d r)
    (common : Ic_agree_d I row.X row.R row.A row.π (v 0) (v 1) (v 18) (v 19)
      row.L l φ row.U V Γ j) :
    Zc_model_d I ω row.c row.X row.R ∧ Zc_model_d I ω (v 15) (v 0) (v 1) ∧
      Rd_entry_d row.w (v 2) j ∧
      ∀ g x y, M.mem g Bγ → Rd_entry_d x y j → Rd_entry_d g y (v 16) → Rd_entry_d g x row.p := by
  obtain ⟨old,pack,mx,saved,numbers,basis,_,_,_,_,_,_,view⟩ := state.request.views m r entry
  have eq := Tg_archive_row_d.eq_l (rt_tuple_inj_l pack tuple)
  subst old
  have links := state.request.links m r row entry tuple
  have left := state.tree.diagram.elementary o row.i row.p c₀ X₀ R₀ row.c row.X row.R
    links.2.2.1 state.root_node links.2.1 root.model mx
  have right := state.tree.diagram.elementary o (v 7) (v 16) c₀ X₀ R₀ (v 15) (v 0) (v 1)
    state.root_map state.root_node state.node root.model state.model
  have source := root.map_l hZF state.tree.omega mx left
  have target := root.map_l hZF state.tree.omega state.model right
  have hx := ZFC.models_zf_l (source.native_l I hZF state.tree.omega)
  let N := smdl_structure_l I (R := row.R) mx.2.1
  obtain ⟨z₀,numbers⟩ := numbers
  obtain ⟨w,code,lower,_⟩ := view
  obtain ⟨_,α,B,z,t,height,layer,rank,limit,omega,fixed⟩ := basis
  let αn : N.Domain := ⟨α,height.member⟩
  let Bn : N.Domain := ⟨B,layer.member⟩
  let Ln : N.Domain := ⟨row.L,common.common.left_rank.1⟩
  let Un : N.Domain := ⟨row.U,common.common.left_rank.2.1⟩
  have rankB := (rr_rank_native_l I mx.2.1 (ZF.modelsKP hx) αn Bn).mp rank
  have rankU := (rr_rank_native_l I mx.2.1 (ZF.modelsKP hx) Ln Un).mp common.common.left_rank
  have limit : N.IsLimitOrdinal αn := (Formula.satisfies_isLimitOrdinal_iff ..).mp
    ((rr_truth_native_l I mx.2.1 (Formula.isLimitOrdinal .newest) (by simp -implicitDefEqProofs)
      (fun _ : Fin 1 => αn)).mp limit)
  -- 原回答中保存的域属于共同秩段，且其原生极限高度至少为 γ。
  obtain ⟨nc,ρ,pack,round,_,member,_,_,_⟩ := saved.read_l I hZF.1
  have same : w 15 = (ρ.bound 15).val.val := congrFun (code.inj_l I hZF.1 pack) 17
  have lower : It_lower_d I γ row.X row.R (ρ.bound 15).val.val := same ▸ lower
  obtain ⟨α',z',height',below⟩ := lower
  have eq := (height'.unique_l (ZF.modelsKP hZF) height saved.ext).1
  subst α'
  have answer := ((Formula.satisfies_conj_iff ..).mp round).2
  simp only [tg_witness0_m,tg_round_m,Formula.satisfies_conj_iff] at answer
  obtain ⟨_,_,_,_,_,_,language,_⟩ := answer
  simp only [ee_language_m,Formula.satisfies_bind,ee_language0_m,Formula.satisfies_conj_iff] at language
  have fs := saved.context.finite_l mx.2.1 hx.1
  have limit' := (rt_limit_l fs.transitive nc (ZF.modelsKP hx) (ρ.bound 15)).mp
    ((Formula.satisfies_isLimitOrdinal_iff ..).mp language.2.1)
  have bound := ZF.v_ordinal_height_l hx rankU limit'.1 member
  have bound : N.mem αn Ln := ordinal_down_l (ZF.modelsKP hx) limit.1
    (v_ordinal_l (kp_pair_l (ZF.modelsKP hx)) rankU) (fun x hx => below x.val hx) bound
  have inside : N.mem Bn Un := (KP.v_compare_l (ZF.modelsKP hx) rankB rankU
    ((v_ordinal_l (kp_pair_l (ZF.modelsKP hx)) rankU).transitive αn bound)).2 bound
  -- 同一背景基底沿共同图交换；无需假定任一原对象码字面固定。
  obtain ⟨_,_,_,t',_,layer',_,fixed'⟩ := state.basis.anchor_l I
  have graph := (common.common.layer_image_l (ZF.modelsKP hZF) mx.2.1 target.ext
    layer layer' (v_transitive_l (kp_pair_l (ZF.modelsKP hx)) rankU) inside).2
  have omegaU : N.mem ⟨row.w,numbers.member⟩ Un :=
    v_transitive_l (kp_pair_l (ZF.modelsKP hx)) rankU Bn inside _ omega
  have omegaImage := (common.common.layer_image_l (ZF.modelsKP hZF) mx.2.1 target.ext
    numbers state.request.numbers (v_transitive_l (kp_pair_l (ZF.modelsKP hx)) rankU) omegaU).1
  refine ⟨source,target,omegaImage,?_⟩
  intro g x y hg point image
  obtain ⟨x',hX,hgx⟩ := layer.injection.1.2.2 g hg
  have hΓ : M.mem x' Γ := (common.common.carrier x').mpr ⟨hX,
    v_transitive_l (kp_pair_l (ZF.modelsKP hx)) rankU Bn inside ⟨x',hX⟩
      ((layer.image x').mpr ⟨g,hg,hgx⟩)⟩
  obtain ⟨y',_,hxy⟩ := common.common.injection.1.2.2 x' hΓ
  have eq := right.1.1.1.2 g y' y (fixed' g y' ((graph g y').mpr ⟨x',hgx,hxy⟩)) image
  have eqx := common.common.injection.2 x' x y (eq ▸ hxy) point
  exact eqx ▸ fixed g x' hgx

end YesMetaZFC.SetTheory.LargeCardinal

/-! ## 给定实际共同图上的原档案求值

短图的原生有序对同时给出指标和值在共同层中的所属。沿调用者已经取得的共同图
搬运这两个坐标及整图，数字层交换则保持同一个背景指标；不重新选择共同图。
-/
namespace YesMetaZFC.SetTheory.LargeCardinal
open Definitional.Project InnerModel Internal
universe u
variable {M : Structure.{u}} (hZF : M.Models ZF)
local notation "I" => kp_pair_l (ZF.modelsKP hZF)

/-- 原档案的实际求值沿已指定的共同图进入同一当前历史。 -/
theorem Tg_iteration_d.archive_transport_l
    {Ω c o C₀ S₀ γ Bγ A X₀ R₀ m r l φ V Γ j q s z i n x : M.Domain}
    {v : Fin 29 → M.Domain} {a : Fin 46 → M.Domain}
    (state : Tg_iteration_d hZF Ω c o C₀ S₀ γ Bγ A v a)
    (root : Zc_model_d I Ω c X₀ R₀) (row : Tg_archive_row_d M.Domain)
    (entry : Rd_entry_d m r (v 13)) (tuple : Rt_tuple_d row.values_d r)
    (common : Ic_agree_d I row.X row.R row.A row.π (v 0) (v 1) (v 18) (v 19)
      row.L l φ row.U V Γ j) (short : Rd_entry_d q s j)
    (numbers : Rr_layer_d I Ω row.X row.R row.w z)
    (point : Rd_entry_d i n z) (value : Rf_val_d I row.X row.R n x q) :
    ∃ n' x', Rd_entry_d i n' (v 3) ∧ Rd_entry_d n n' j ∧ Rd_entry_d x x' j ∧
      Rf_val_d I (v 0) (v 1) n' x' s := by
  obtain ⟨source,target,omega,_⟩ := state.archive_low_l hZF root row entry tuple common
  have hX := ZF.modelsKP (ZFC.models_zf_l (source.native_l I hZF state.tree.omega))
  let N := smdl_structure_l I (R := row.R) source.model.2.1
  let P := smdl_structure_l I (R := v 1) target.model.2.1
  let U : N.Domain := ⟨row.U,common.common.left_rank.2.1⟩
  let L : N.Domain := ⟨row.L,common.common.left_rank.1⟩
  have trans := v_transitive_l (kp_pair_l hX)
    ((rr_rank_native_l I source.model.2.1 hX L U).mp common.common.left_rank)
  let sn : N.Domain := ⟨q,(value.bounds_l I).2.2⟩
  let ni : N.Domain := ⟨n,(value.bounds_l I).1⟩
  let xi : N.Domain := ⟨x,(value.bounds_l I).2.1⟩
  have old := (rf_val_native_l I source.model.2.1 hX.1 ni xi sn).mp value
  have member : N.mem sn U :=
    ((common.common.carrier q).mp (common.common.injection.1.input_mem_of_pairMember short)).2
  have bounds := rd_entry_transitive_l trans member old
  have pick (a : N.Domain) (ha : N.mem a U) : ∃ b : P.Domain, Rd_entry_d a.val b.val j := by
    obtain ⟨b,hb,image⟩ := common.common.injection.1.2.2 a.val ((common.common.carrier a.val).mpr ⟨a.property,ha⟩)
    exact ⟨⟨b,hb⟩,image⟩
  obtain ⟨ni',in'⟩ := pick ni bounds.1
  obtain ⟨xi',ix'⟩ := pick xi bounds.2
  let sn' : P.Domain := ⟨s,common.common.injection.1.output_mem_of_pairMember short⟩
  have move := rr_graph_delta_l I source.model.2.1 target.model.2.1
    ⟨q,common.common.injection.1.input_mem_of_pairMember short⟩
    (fun y hy => ((common.common.carrier y).mp hy).1)
    (fun y t hy ht ty => (common.common.carrier t).mpr ⟨ht,
      trans ⟨y,((common.common.carrier y).mp hy).1⟩ ((common.common.carrier y).mp hy).2 ⟨t,ht⟩ ty⟩)
    common.common.injection common.common.pred
    (rd_entry0_m (.bound 0) (.bound 1) (.bound 2)) (by simp -implicitDefEqProofs) (rd_entry0_delta_l ..)
    (⟨fun k => [ni,xi,sn].get k,fun _ => sn⟩ : Env N 3)
    (⟨fun k => [ni',xi',sn'].get k,fun _ => sn'⟩ : Env P 3)
    (Fin.cases in' (Fin.cases ix' (Fin.cases short (fun k => Fin.elim0 k))))
  have ey := target.ext.native_l I target.model.2.1
  have moved : Rd_entry_d ni' xi' sn' := (rd_entry0_sat_l ey ..).mp
    (move.mp ((rd_entry0_sat_l hX.1 ..).mpr old))
  have low : Rd_entry_d row.w row.U row.R :=
    ((common.common.carrier row.w).mp (common.common.injection.1.input_mem_of_pairMember omega)).2
  have graph := (common.common.layer_image_l (ZF.modelsKP hZF) source.model.2.1 target.ext
    numbers state.request.numbers trans low).2
  exact ⟨ni'.val,xi'.val,(graph i ni'.val).mpr ⟨n,point,in'⟩,in',ix',
    (rf_val_native_l I target.model.2.1 ey ni' xi' sn').mpr moved⟩

end YesMetaZFC.SetTheory.LargeCardinal
