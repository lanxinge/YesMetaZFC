import YesMetaZFC.SetTheory.LargeCardinal.Game.RawCritical
import YesMetaZFC.SetTheory.LargeCardinal.Game.RootSquare

/-! # 实际工厂的低秩方块推进原根切片

原生 γ≤κ<L 的两份秩历史把整个旧切片放入同一次共同图。
秩、端点及完整前驱随该图复合；根图对应只取自工厂的 Vκ 方块
与实际原树复合，不使用外部良基性或任意根解释的唯一性。
-/
namespace YesMetaZFC.SetTheory.LargeCardinal
open Definitional.Project InnerModel Internal
universe u
variable {M : Structure.{u}} (hZF : M.Models ZF)
local notation "I" => kp_pair_l (ZF.modelsKP hZF)

/-- 共同图推进原切片的秩、端点及全部前驱；根对应只读取实际选定方块。 -/
theorem Tg_root_slice_d.common_step_l
    {X₀ R₀ γ₀ D₀ C₀ N R C q γ Vg tg P S C' q' L l U V Γ t c d : M.Domain}
    (slice : Tg_root_slice_d I X₀ R₀ γ₀ D₀ C₀ N R C q γ Vg tg)
    (common : Ic_common_d I N R P S L l U V Γ t)
    (mn : Smdl_d I c N R) (mp : Smdl_d I d P S)
    (hN : (smdl_structure_l I (R := R) mn.2.1).Models KP)
    (hP : (smdl_structure_l I (R := S) mp.2.1).Models KP)
    (high : Rd_entry_d γ L R) (square : Tg_root_square_d D₀ q q' t)
    (context : Rd_entry_d C₀ C' q') :
    ∃ γ' Vg' tg', Rd_entry_d γ γ' t ∧ Rd_entry_d Vg Vg' t ∧ It_comp_d tg t tg' ∧
      Tg_root_slice_d I X₀ R₀ γ₀ D₀ C₀ P S C' q' γ' Vg' tg' ∧
      Rd_entry_d γ' l S := by
  let Nn := smdl_structure_l I (R := R) mn.2.1
  let Pn := smdl_structure_l I (R := S) mp.2.1
  let Ln : Nn.Domain := ⟨L,common.left_rank.1⟩
  let Un : Nn.Domain := ⟨U,common.left_rank.2.1⟩
  let gn : Nn.Domain := ⟨γ,slice.rank.1⟩
  let Vn : Nn.Domain := ⟨Vg,slice.rank.2.1⟩
  have ru : V_d (kp_pair_l hN) Ln Un := (rr_rank_native_l I mn.2.1 hN Ln Un).mp common.left_rank
  have rg : V_d (kp_pair_l hN) gn Vn := (rr_rank_native_l I mn.2.1 hN gn Vn).mp slice.rank
  have limit : Nn.IsLimitOrdinal Ln := (Formula.satisfies_isLimitOrdinal_iff ..).mp
    ((rr_truth_native_l I mn.2.1 (Formula.isLimitOrdinal .newest)
      (by simp -implicitDefEqProofs) (fun _ : Fin 1 => Ln)).mp common.limit)
  have limitG : Nn.IsLimitOrdinal gn := (Formula.satisfies_isLimitOrdinal_iff ..).mp
    ((rr_truth_native_l I mn.2.1 (Formula.isLimitOrdinal .newest)
      (by simp -implicitDefEqProofs) (fun _ : Fin 1 => gn)).mp slice.limit)
  have gL : Nn.mem gn Ln := high
  have gU : Nn.mem gn Un := KP.v_ordinal_subset_l hN ru gn gL
  have vU : Nn.mem Vn Un := (KP.v_compare_l hN rg ru (limit.1.transitive gn gL)).2 gL
  have ut : Nn.TransitiveSet Un := v_transitive_l (kp_pair_l hN) ru
  have domain x (hx : M.mem x Γ) := ((common.carrier x).mp hx).1
  have down x y (hx : M.mem x Γ) (hy : Rd_entry_d y x R) : M.mem y Γ :=
    (common.carrier y).mpr ⟨(mn.2.2.2 y x hy).1,
      ut ⟨x,domain x hx⟩ ((common.carrier x).mp hx).2 ⟨y,(mn.2.2.2 y x hy).1⟩ hy⟩
  have member x y (xy : Rd_entry_d x y tg) : Nn.mem ⟨y,slice.injection.1.output_mem_of_pairMember xy⟩ Vn :=
    (slice.image y).mpr ⟨x,slice.injection.1.input_mem_of_pairMember xy,xy⟩
  have inside x y (xy : Rd_entry_d x y tg) : M.mem y Γ :=
    (common.carrier y).mpr ⟨slice.injection.1.output_mem_of_pairMember xy,
      ut Vn vU ⟨y,slice.injection.1.output_mem_of_pairMember xy⟩ (member x y xy)⟩
  obtain ⟨γ',hγ',iγ⟩ := common.injection.1.2.2 γ ((common.carrier γ).mpr ⟨gn.property,gU⟩)
  obtain ⟨Vg',_,iV⟩ := common.injection.1.2.2 Vg ((common.carrier Vg).mpr ⟨Vn.property,vU⟩)
  let gp : Pn.Domain := ⟨γ',hγ'⟩
  -- 先回收同一源秩历史，再由共同图的完整前驱及子集闭性读成目标秩。
  obtain ⟨F,hF,cert⟩ := KP.v_history_inside_l hN ru limit gU vU rg
  have localrank : Vr_d Un gn Vn := ⟨Vn,F,vU,hF,fun x _ => cert x⟩
  have rank' : Rr_rank_d I P S γ' Vg' := rr_native_rank_value_l I mn.2.1 mp.2.1 hP.1
    Un gn Vn ut common.carrier common.injection common.image common.pred common.right_closed gU vU iγ iV
      ((vr_sat_l hN ut ⟨⟨gn,gU⟩⟩ _ (.bound 1) .newest).mpr localrank)
  let nu : Nonempty {x : Nn.Domain // Nn.mem x Un} := ⟨⟨gn,gU⟩⟩
  let a : Env (rt_model_l Un nu) 1 := ⟨fun _ => ⟨gn,gU⟩,fun _ => ⟨gn,gU⟩⟩
  let b : Env Pn 1 := ⟨fun _ => gp,fun _ => gp⟩
  have limitP : Pn.IsLimitOrdinal gp := (KP.limit0_sat_l hP b .newest).mp
    ((rr_native_delta_l I mn.2.1 mp.2.1 Un ut nu common.carrier common.injection common.pred
      (KP.limit0_m .newest) (by simp -implicitDefEqProofs) (KP.limit0_delta_l _) a b (fun _ => iγ)).mp
        ((KP.limit0_sat_l hN _ .newest).mpr limitG))
  have limit' : Rr_truth_d I P S (Formula.isLimitOrdinal .newest) (fun _ : Fin 1 => γ') :=
    (rr_truth_native_l I mp.2.1 (Formula.isLimitOrdinal .newest)
      (by simp -implicitDefEqProofs) (fun _ : Fin 1 => gp)).mpr
        ((Formula.satisfies_isLimitOrdinal_iff ..).mpr limitP)
  have ft := fn0_function_l (ZF.modelsKP hZF)
    ((fn0_of_function_l (ZF.modelsKP hZF) slice.injection.1).retarget_l inside)
  obtain ⟨tg',fn,graph⟩ := ZF.exists_compositionFunction hZF I ft common.injection.1
  have comp : It_comp_d tg t tg' := ⟨fn.1.1,fun x y => (graph x y).trans
    ⟨And.right,fun ⟨z,xz,zy⟩ => ⟨slice.injection.1.input_mem_of_pairMember xz,z,xz,zy⟩⟩⟩
  have inj : M.IsSetInjectionFromTo I tg' D₀ P := by
    refine ⟨fn,fun x y p hx hy => ?_⟩
    obtain ⟨u,xu,up⟩ := (comp.2 x p).mp hx
    obtain ⟨v,yv,vp⟩ := (comp.2 y p).mp hy
    exact slice.injection.2 x y v (common.injection.2 u v p up vp ▸ xu) yv
  have image y : Rd_entry_d y Vg' S ↔ ∃ x, M.mem x D₀ ∧ Rd_entry_d x y tg' := by
    constructor
    · intro hy
      obtain ⟨v,hv,vy⟩ := (common.pred Vg Vg' iV y).mp hy
      obtain ⟨x,hx,xv⟩ := (slice.image v).mp hv
      exact ⟨x,hx,(comp.2 x y).mpr ⟨v,xv,vy⟩⟩
    · rintro ⟨x,hx,xy⟩
      obtain ⟨v,xv,vy⟩ := (comp.2 x y).mp xy
      exact (common.pred Vg Vg' iV y).mpr ⟨v,(slice.image v).mpr ⟨x,hx,xv⟩,vy⟩
  have pred x y (xy : Rd_entry_d x y tg') z :
      Rd_entry_d z y S ↔ ∃ a, Rd_entry_d a x R₀ ∧ Rd_entry_d a z tg' := by
    obtain ⟨v,xv,vy⟩ := (comp.2 x y).mp xy
    constructor
    · intro zy
      obtain ⟨u,uv,uz⟩ := (common.pred v y vy z).mp zy
      obtain ⟨a,ax,au⟩ := (slice.predecessors x v xv u).mp uv
      exact ⟨a,ax,(comp.2 a z).mpr ⟨u,au,uz⟩⟩
    · rintro ⟨a,ax,az⟩
      obtain ⟨u,au,uz⟩ := (comp.2 a z).mp az
      exact (common.pred v y vy z).mpr ⟨u,(slice.predecessors x v xv u).mpr ⟨a,ax,au⟩,uz⟩
  have endpoint := (er_rep_comp_l (ZF.modelsKP hZF) common.injection domain down inside common.pred comp iγ).mp
    slice.endpoint
  have roots x y (xy : Rd_entry_d x y tg') : Rd_entry_d x y q' := by
    obtain ⟨v,xv,vy⟩ := (comp.2 x y).mp xy
    exact (square x (slice.injection.1.input_mem_of_pairMember xv) v (slice.root x v xv) y).mp vy
  exact ⟨γ',Vg',tg',iγ,iV,comp,⟨context,rank',limit',inj,image,pred,endpoint,roots⟩,
    (common.endpoint.2.2 γ').mpr ⟨γ,gn.property,gL,iγ⟩⟩

/-- 原边源等于当前模型时，低秩方块与根复合实际生产公共核心所需的根方块。 -/
theorem Tg_root_slice_d.step_l
    {X₀ R₀ γ₀ D₀ C₀ N R C q γ Vg tg P S C' q' L l U V Γ t c d j : M.Domain}
    (slice : Tg_root_slice_d I X₀ R₀ γ₀ D₀ C₀ N R C q γ Vg tg)
    (common : Ic_common_d I N R P S L l U V Γ t)
    (mn : Smdl_d I c N R) (mp : Smdl_d I d P S)
    (hN : (smdl_structure_l I (R := R) mn.2.1).Models KP)
    (hP : (smdl_structure_l I (R := S) mp.2.1).Models KP)
    (κ K : (smdl_structure_l I (R := R) mn.2.1).Domain)
    (rankK : V_d (kp_pair_l hN) κ K) (high : Rd_entry_d κ.val L R)
    (below : ∀ x, Rd_entry_d x γ R → Rd_entry_d x κ.val R)
    (square : ∀ x : (smdl_structure_l I (R := R) mn.2.1).Domain,
      (smdl_structure_l I (R := R) mn.2.1).mem x K → ∀ y,
        Rd_entry_d x.val y t ↔ Rd_entry_d x.val y j)
    (function : M.IsSetFunction I q) (root : It_comp_d q j q')
    (context : Rd_entry_d C C' j) :
    ∃ γ' Vg' tg', Rd_entry_d γ γ' t ∧ Rd_entry_d Vg Vg' t ∧ It_comp_d tg t tg' ∧
      Tg_root_slice_d I X₀ R₀ γ₀ D₀ C₀ P S C' q' γ' Vg' tg' ∧
      Rd_entry_d γ' l S ∧ Tg_root_square_d D₀ q q' t := by
  let Nn := smdl_structure_l I (R := R) mn.2.1
  let gn : Nn.Domain := ⟨γ,slice.rank.1⟩
  let Vn : Nn.Domain := ⟨Vg,slice.rank.2.1⟩
  let Ln : Nn.Domain := ⟨L,common.left_rank.1⟩
  let Un : Nn.Domain := ⟨U,common.left_rank.2.1⟩
  have rg := (rr_rank_native_l I mn.2.1 hN gn Vn).mp slice.rank
  have ru := (rr_rank_native_l I mn.2.1 hN Ln Un).mp common.left_rank
  have highγ : Rd_entry_d γ L R := ordinal_down_l hN
    (v_ordinal_l (kp_pair_l hN) rg) (v_ordinal_l (kp_pair_l hN) ru) (fun x hx => below x.val hx) high
  have sub : Nn.MemberSubset Vn K := (KP.v_compare_l hN rg rankK (fun x hx => below x.val hx)).1
  have roots : Tg_root_square_d D₀ q q' t := by
    intro a ha x ax y
    obtain ⟨x₀,_,ax₀⟩ := slice.injection.1.2.2 a ha
    have eq := function.2 a x₀ x (slice.root a x₀ ax₀) ax
    subst x₀
    have member : Nn.mem ⟨x,slice.injection.1.output_mem_of_pairMember ax₀⟩ Vn :=
      (slice.image x).mpr ⟨a,ha,ax₀⟩
    exact (square _ (sub _ member) y).trans
      ⟨fun xy => (root.2 a y).mpr ⟨x,ax,xy⟩,fun ay => by
        obtain ⟨v,av,vy⟩ := (root.2 a y).mp ay
        exact function.2 a v x av ax ▸ vy⟩
  obtain ⟨γ',Vg',tg',iγ,iV,comp,next,bound⟩ := slice.common_step_l hZF common mn mp hN hP highγ roots
    ((root.2 C₀ C').mpr ⟨C,slice.context,context⟩)
  exact ⟨γ',Vg',tg',iγ,iV,comp,next,bound,roots⟩

end YesMetaZFC.SetTheory.LargeCardinal

/-! ## 同次重置工厂的根切片与字母双射

调用方只解包一次原工厂，并固定其共同图、实际 Vκ 方块和目标上下文像。
沿这些已经生产的数据推进同一根切片，得到目标请求的高度界与真实
根图的字母限制双射。此处不重选任何工厂见证。
-/
namespace YesMetaZFC.SetTheory.LargeCardinal
open Definitional.Project InnerModel Internal
universe u
variable {M : Structure.{u}} (hZF : M.Models ZF)
local notation "I" => kp_pair_l (ZF.modelsKP hZF)

/-- 同一工厂的实际低秩方块自动供应重置后的完整根数据。 -/
theorem Tg_root_slice_d.reset_l
    {c₀ X₀ R₀ w₀ γ₀ B₀ a₀ D₀ A C₀ N R C q γ Vg tg
      P S C' q' L l U V Γ t c d j κ' a : M.Domain}
    (cut : Tg_root_cut_d I c₀ X₀ R₀ w₀ γ₀ B₀ a₀ D₀ A)
    (h₀ : (smdl_structure_l I (R := R₀) cut.model.2.1).Models KP)
    (slice : Tg_root_slice_d I X₀ R₀ γ₀ D₀ C₀ N R C q γ Vg tg)
    (common : Ic_common_d I N R P S L l U V Γ t)
    (mn : Smdl_d I c N R) (mp : Smdl_d I d P S)
    (hN : (smdl_structure_l I (R := R) mn.2.1).Models KP)
    (hP : (smdl_structure_l I (R := S) mp.2.1).Models KP)
    (κ K : (smdl_structure_l I (R := R) mn.2.1).Domain)
    (rankK : V_d (kp_pair_l hN) κ K) (hκL : Rd_entry_d κ.val L R)
    (square : ∀ x : (smdl_structure_l I (R := R) mn.2.1).Domain,
      (smdl_structure_l I (R := R) mn.2.1).mem x K → ∀ y,
        Rd_entry_d x.val y t ↔ Rd_entry_d x.val y j)
    (below : ∀ x, Rd_entry_d x γ R → Rd_entry_d x κ.val R)
    (source : M.IsSetFunctionFromTo I q X₀ N) (target : M.IsSetFunction I q')
    (rootGraph : ∀ x y, Rd_entry_d x y q' ↔ M.mem x X₀ ∧ ∃ v, Rd_entry_d x v q ∧ Rd_entry_d v y j)
    (context : Rd_entry_d C C' j)
    (bound : ∀ x, Rd_entry_d x l S → Rd_entry_d x κ' S)
    (ordinal : Rr_truth_d I P S (KP.ord0_m .newest) (fun _ : Fin 1 => κ'))
    (alphabet : Rd_entry_d a₀ a q) :
    ∃ γ' Vg' tg', Rd_entry_d γ γ' t ∧ Rd_entry_d Vg Vg' t ∧ It_comp_d tg t tg' ∧
      Tg_root_slice_d I X₀ R₀ γ₀ D₀ C₀ P S C' q' γ' Vg' tg' ∧
      Rd_entry_d γ' l S ∧ (∀ x, Rd_entry_d x γ' S → Rd_entry_d x κ' S) ∧
      Tg_root_square_d D₀ q q' t ∧
      ∃ a' B f, Rd_entry_d a a' j ∧ Rd_entry_d a₀ a' q' ∧
        (∀ y, M.mem y B ↔ M.mem y P ∧ Rd_entry_d y a' S) ∧
        M.IsSetBijectionFromTo I f A B ∧ M.IsRestrictionOf I f q' A := by
  let Pn := smdl_structure_l I (R := S) mp.2.1
  have root : It_comp_d q j q' := ⟨target.1,fun x y => (rootGraph x y).trans
    ⟨And.right,fun ⟨v,xv,vy⟩ => ⟨source.input_mem_of_pairMember xv,v,xv,vy⟩⟩⟩
  obtain ⟨γ',Vg',tg',iγ,iV,comp,next,high,roots⟩ :=
    slice.step_l hZF common mn mp hN hP κ K rankK hκL below square source.1 root context
  let κn : Pn.Domain := ⟨κ',ordinal.1 0⟩
  have ordκ : Pn.IsOrdinal κn := (KP.ord0_sat_l hP _ .newest).mp
    ((rr_truth_native_l I mp.2.1 (KP.ord0_m .newest)
      (by simp -implicitDefEqProofs) (fun _ : Fin 1 => κn)).mp ordinal)
  have below' x (hx : Rd_entry_d x γ' S) : Rd_entry_d x κ' S :=
    ordκ.transitive ⟨γ',next.rank.1⟩ (bound γ' high) ⟨x,(mp.2.2.2 x γ' hx).1⟩ hx
  have ha : M.mem a₀ D₀ := (cut.carrier a₀).mpr
    ⟨(cut.model.2.2.2 a₀ B₀ cut.alphabet).1,cut.alphabet⟩
  obtain ⟨a',_,letter⟩ := next.injection.1.2.2 a₀ ha
  have rootLetter := next.root a₀ a' letter
  have iA : Rd_entry_d a a' j := by
    obtain ⟨v,av,va⟩ := (root.2 a₀ a').mp rootLetter
    exact source.1.2 a₀ v a av alphabet ▸ va
  obtain ⟨B,f,range,bij,rest⟩ := cut.alphabet_l hZF h₀ next target rootLetter
  exact ⟨γ',Vg',tg',iγ,iV,comp,next,high,below',roots,a',B,f,iA,rootLetter,range,bij,rest⟩

end YesMetaZFC.SetTheory.LargeCardinal

/-! ## 不同原前驱的活动边推进当前根切片

继续轮的实际嵌入以旧档案模型为源，而新共同图以当前模型为源。
旧根方块先经同一逆图找到旧前驱坐标，工厂的低秩方块再把该坐标送入
新后继。只有旧前驱根图与活动边复合，不要求当前根图与该边可复合。
-/
namespace YesMetaZFC.SetTheory.LargeCardinal
open Definitional.Project InnerModel Internal
universe u
variable {M : Structure.{u}} (hZF : M.Models ZF)
local notation "I" => kp_pair_l (ZF.modelsKP hZF)

/-- 同一次逆图和原活动方块生产新根方块，随后调用共有的完整切片推进。 -/
theorem Tg_root_slice_d.continue_step_l
    {X₀ R₀ γ₀ D₀ C₀ X p N R C q γ Vg tg P S C' q' L l U V Γ t c d g k j : M.Domain}
    (slice : Tg_root_slice_d I X₀ R₀ γ₀ D₀ C₀ N R C q γ Vg tg)
    (common : Ic_common_d I N R P S L l U V Γ t)
    (mn : Smdl_d I c N R) (mp : Smdl_d I d P S)
    (hN : (smdl_structure_l I (R := R) mn.2.1).Models KP)
    (hP : (smdl_structure_l I (R := S) mp.2.1).Models KP)
    (κ K : (smdl_structure_l I (R := R) mn.2.1).Domain)
    (rankK : V_d (kp_pair_l hN) κ K) (high : Rd_entry_d κ.val L R)
    (below : ∀ x, Rd_entry_d x γ R → Rd_entry_d x κ.val R)
    (old : Tg_root_square_d D₀ p q g)
    (inverse : ∀ x y, Rd_entry_d x y k ↔ Rd_entry_d y x g)
    (square : ∀ x : (smdl_structure_l I (R := R) mn.2.1).Domain,
      (smdl_structure_l I (R := R) mn.2.1).mem x K → ∀ y E,
        Rd_entry_d x.val y k → (Rd_entry_d x.val E t ↔ Rd_entry_d y E j))
    (source : M.IsSetFunction I q) (parent : M.IsSetFunctionFromTo I p X₀ X)
    (domain : M.MemberSubset D₀ X₀) (root : It_comp_d p j q')
    (context : Rd_entry_d C₀ C' q') :
    ∃ γ' Vg' tg', Rd_entry_d γ γ' t ∧ Rd_entry_d Vg Vg' t ∧ It_comp_d tg t tg' ∧
      Tg_root_slice_d I X₀ R₀ γ₀ D₀ C₀ P S C' q' γ' Vg' tg' ∧
      Rd_entry_d γ' l S ∧ Tg_root_square_d D₀ q q' t := by
  let Nn := smdl_structure_l I (R := R) mn.2.1
  let gn : Nn.Domain := ⟨γ,slice.rank.1⟩
  let Vn : Nn.Domain := ⟨Vg,slice.rank.2.1⟩
  let Ln : Nn.Domain := ⟨L,common.left_rank.1⟩
  let Un : Nn.Domain := ⟨U,common.left_rank.2.1⟩
  have rg := (rr_rank_native_l I mn.2.1 hN gn Vn).mp slice.rank
  have ru := (rr_rank_native_l I mn.2.1 hN Ln Un).mp common.left_rank
  have highγ : Rd_entry_d γ L R := ordinal_down_l hN
    (v_ordinal_l (kp_pair_l hN) rg) (v_ordinal_l (kp_pair_l hN) ru) (fun x hx => below x.val hx) high
  have sub : Nn.MemberSubset Vn K := (KP.v_compare_l hN rg rankK (fun x hx => below x.val hx)).1
  have roots : Tg_root_square_d D₀ q q' t := by
    intro a ha x ax E
    obtain ⟨x₀,_,ax₀⟩ := slice.injection.1.2.2 a ha
    have eq := source.2 a x₀ x (slice.root a x₀ ax₀) ax
    subst x₀
    have member : Nn.mem ⟨x,slice.injection.1.output_mem_of_pairMember ax₀⟩ Vn :=
      (slice.image x).mpr ⟨a,ha,ax₀⟩
    obtain ⟨y,_,ay⟩ := parent.2.2 a (domain a ha)
    have back : Rd_entry_d x y k := (inverse x y).mpr ((old a ha y ay x).mpr ax)
    exact (square _ (sub _ member) y E back).trans
      ⟨fun yE => (root.2 a E).mpr ⟨y,ay,yE⟩,fun aE => by
        obtain ⟨z,az,zE⟩ := (root.2 a E).mp aE
        exact parent.1.2 a z y az ay ▸ zE⟩
  obtain ⟨γ',Vg',tg',iγ,iV,comp,next,bound⟩ :=
    slice.common_step_l hZF common mn mp hN hP highγ roots context
  exact ⟨γ',Vg',tg',iγ,iV,comp,next,bound,roots⟩

end YesMetaZFC.SetTheory.LargeCardinal
